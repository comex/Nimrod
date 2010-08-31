#
#
#           The Nimrod Compiler
#        (c) Copyright 2008 Andreas Rumpf
#
#    See the file "copying.txt", included in this
#    distribution, for details about the copyright.
#

# tree helper routines

import 
  ast, astalgo, scanner, msgs, strutils, idents

proc getMagic*(op: PNode): TMagic

proc isConstExpr*(n: PNode): bool
proc flattenTree*(root: PNode, op: TMagic): PNode
proc TreeToSym*(t: PNode): PSym
proc SwapOperands*(op: PNode)
proc getOpSym*(op: PNode): PSym
proc getProcSym*(call: PNode): PSym
proc ExprStructuralEquivalent*(a, b: PNode): bool
proc sameTree*(a, b: PNode): bool
proc cyclicTree*(n: PNode): bool
# implementation

proc hasSon(father, son: PNode): bool = 
  for i in countup(0, sonsLen(father) - 1): 
    if father.sons[i] == son: 
      return true
  result = false

proc cyclicTreeAux(n, s: PNode): bool = 
  if n == nil: 
    return false
  if hasSon(s, n): 
    return true
  var m = sonsLen(s)
  addSon(s, n)
  if not (n.kind in {nkEmpty..nkNilLit}): 
    for i in countup(0, sonsLen(n) - 1): 
      if cyclicTreeAux(n.sons[i], s): 
        return true
  result = false
  delSon(s, m)

proc cyclicTree(n: PNode): bool = 
  var s = newNodeI(nkEmpty, n.info)
  result = cyclicTreeAux(n, s)

proc ExprStructuralEquivalent(a, b: PNode): bool = 
  result = false
  if a == b: 
    result = true
  elif (a != nil) and (b != nil) and (a.kind == b.kind): 
    case a.kind
    of nkSym: 
      # don't go nuts here: same symbol as string is enough:
      result = a.sym.name.id == b.sym.name.id
    of nkIdent: result = a.ident.id == b.ident.id
    of nkCharLit..nkInt64Lit: result = a.intVal == b.intVal
    of nkFloatLit..nkFloat64Lit: result = a.floatVal == b.floatVal
    of nkStrLit..nkTripleStrLit: result = a.strVal == b.strVal
    of nkEmpty, nkNilLit, nkType: result = true
    else: 
      if sonsLen(a) == sonsLen(b): 
        for i in countup(0, sonsLen(a) - 1): 
          if not ExprStructuralEquivalent(a.sons[i], b.sons[i]): return 
        result = true
  
proc sameTree(a, b: PNode): bool = 
  result = false
  if a == b: 
    result = true
  elif (a != nil) and (b != nil) and (a.kind == b.kind): 
    if a.flags != b.flags: return 
    if a.info.line != b.info.line: return 
    if a.info.col != b.info.col: 
      return                  #if a.info.fileIndex <> b.info.fileIndex then exit;
    case a.kind
    of nkSym: 
      # don't go nuts here: same symbol as string is enough:
      result = a.sym.name.id == b.sym.name.id
    of nkIdent: result = a.ident.id == b.ident.id
    of nkCharLit..nkInt64Lit: result = a.intVal == b.intVal
    of nkFloatLit..nkFloat64Lit: result = a.floatVal == b.floatVal
    of nkStrLit..nkTripleStrLit: result = a.strVal == b.strVal
    of nkEmpty, nkNilLit, nkType: result = true
    else: 
      if sonsLen(a) == sonsLen(b): 
        for i in countup(0, sonsLen(a) - 1): 
          if not sameTree(a.sons[i], b.sons[i]): return 
        result = true
  
proc getProcSym(call: PNode): PSym = 
  result = call.sons[0].sym

proc getOpSym(op: PNode): PSym = 
  if not (op.kind in {nkCall, nkHiddenCallConv, nkCommand, nkCallStrLit}): 
    result = nil
  else: 
    if (sonsLen(op) <= 0): InternalError(op.info, "getOpSym")
    if op.sons[0].Kind == nkSym: result = op.sons[0].sym
    else: result = nil
  
proc getMagic(op: PNode): TMagic = 
  case op.kind
  of nkCall, nkHiddenCallConv, nkCommand, nkCallStrLit: 
    case op.sons[0].Kind
    of nkSym: result = op.sons[0].sym.magic
    else: result = mNone
  else: result = mNone
  
proc TreeToSym(t: PNode): PSym = 
  result = t.sym

proc isConstExpr(n: PNode): bool = 
  result = (n.kind in
      {nkCharLit..nkInt64Lit, nkStrLit..nkTripleStrLit, 
       nkFloatLit..nkFloat64Lit, nkNilLit}) or (nfAllConst in n.flags)

proc flattenTreeAux(d, a: PNode, op: TMagic) = 
  if (getMagic(a) == op):     # a is a "leaf", so add it:
    for i in countup(1, sonsLen(a) - 1): # BUGFIX
      flattenTreeAux(d, a.sons[i], op)
  else: 
    addSon(d, copyTree(a))
  
proc flattenTree(root: PNode, op: TMagic): PNode = 
  result = copyNode(root)
  if (getMagic(root) == op): 
    # BUGFIX: forget to copy prc
    addSon(result, copyNode(root.sons[0]))
    flattenTreeAux(result, root, op)

proc SwapOperands(op: PNode) = 
  var tmp = op.sons[1]
  op.sons[1] = op.sons[2]
  op.sons[2] = tmp
