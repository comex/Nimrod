#
#
#           The Nimrod Compiler
#        (c) Copyright 2008 Andreas Rumpf
#
#    See the file "copying.txt", included in this
#    distribution, for details about the copyright.
#

# Implements a table from trees to trees. Does structural equavilent checking.

import 
  nhashes, ast, astalgo, types, idents

proc NodeTableGet*(t: TNodeTable, key: PNode): TId
proc NodeTablePut*(t: var TNodeTable, key: PNode, val: TId)
proc NodeTableTestOrSet*(t: var TNodeTable, key: PNode, val: TId): TId
# implementation

proc hashTree(n: PNode): THash = 
  result = 0
  if n == nil: return 
  result = ord(n.kind)
  case n.kind
  of nkEmpty, nkNilLit, nkType: 
    nil
  of nkIdent: 
    result = concHash(result, n.ident.h)
  of nkSym: 
    result = concHash(result, n.sym.name.h)
  of nkCharLit..nkInt64Lit: 
    if (n.intVal >= low(int)) and (n.intVal <= high(int)): 
      result = concHash(result, int(n.intVal))
  of nkFloatLit..nkFloat64Lit: 
    if (n.floatVal >= - 1000000.0) and (n.floatVal <= 1000000.0): 
      result = concHash(result, toInt(n.floatVal))
  of nkStrLit..nkTripleStrLit: 
    result = concHash(result, GetHashStr(n.strVal))
  else: 
    for i in countup(0, sonsLen(n) - 1): 
      result = concHash(result, hashTree(n.sons[i]))
  
proc TreesEquivalent(a, b: PNode): bool = 
  result = false
  if a == b: 
    result = true
  elif (a != nil) and (b != nil) and (a.kind == b.kind): 
    case a.kind
    of nkEmpty, nkNilLit, nkType: result = true
    of nkSym: result = a.sym.id == b.sym.id
    of nkIdent: result = a.ident.id == b.ident.id
    of nkCharLit..nkInt64Lit: result = a.intVal == b.intVal
    of nkFloatLit..nkFloat64Lit: result = a.floatVal == b.floatVal
    of nkStrLit..nkTripleStrLit: result = a.strVal == b.strVal
    else: 
      if sonsLen(a) == sonsLen(b): 
        for i in countup(0, sonsLen(a) - 1): 
          if not TreesEquivalent(a.sons[i], b.sons[i]): return 
        result = true
    if result: result = sameTypeOrNil(a.typ, b.typ)
  
proc NodeTableRawGet(t: TNodeTable, k: THash, key: PNode): int = 
  var h: THash
  h = k and high(t.data)
  while t.data[h].key != nil: 
    if (t.data[h].h == k) and TreesEquivalent(t.data[h].key, key): 
      return h
    h = nextTry(h, high(t.data))
  result = - 1

proc NodeTableGet(t: TNodeTable, key: PNode): TId = 
  var index: int
  index = NodeTableRawGet(t, hashTree(key), key)
  if index >= 0: result = t.data[index].val
  else: result = nilId
  
proc NodeTableRawInsert(data: var TNodePairSeq, k: THash, key: PNode, val: TId) = 
  var h: THash
  h = k and high(data)
  while data[h].key != nil: h = nextTry(h, high(data))
  assert(data[h].key == nil)
  data[h].h = k
  data[h].key = key
  data[h].val = val

proc NodeTablePut(t: var TNodeTable, key: PNode, val: TId) = 
  var 
    index: int
    n: TNodePairSeq
    k: THash
  k = hashTree(key)
  index = NodeTableRawGet(t, k, key)
  if index >= 0: 
    assert(t.data[index].key != nil)
    t.data[index].val = val
  else: 
    if mustRehash(len(t.data), t.counter): 
      newSeq(n, len(t.data) * growthFactor)
      for i in countup(0, high(t.data)): 
        if t.data[i].key != nil: 
          NodeTableRawInsert(n, t.data[i].h, t.data[i].key, t.data[i].val)
      swap(t.data, n)
    NodeTableRawInsert(t.data, k, key, val)
    inc(t.counter)

proc NodeTableTestOrSet(t: var TNodeTable, key: PNode, val: TId): TId = 
  var 
    index: int
    n: TNodePairSeq
    k: THash
  k = hashTree(key)
  index = NodeTableRawGet(t, k, key)
  if index >= 0: 
    assert(t.data[index].key != nil)
    result = t.data[index].val
  else: 
    if mustRehash(len(t.data), t.counter): 
      newSeq(n, len(t.data) * growthFactor)
      for i in countup(0, high(t.data)): 
        if t.data[i].key != nil: 
          NodeTableRawInsert(n, t.data[i].h, t.data[i].key, t.data[i].val)
      swap(t.data, n)
    NodeTableRawInsert(t.data, k, key, val)
    result = val
    inc(t.counter)
