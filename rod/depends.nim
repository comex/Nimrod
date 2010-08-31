#
#
#           The Nimrod Compiler
#        (c) Copyright 2010 Andreas Rumpf
#
#    See the file "copying.txt", included in this
#    distribution, for details about the copyright.
#

# This module implements a dependency file generator.

import 
  os, options, ast, astalgo, msgs, ropes, idents, passes, importer

proc genDependPass*(): TPass
proc generateDot*(project: string)

type 
  TGen = object of TPassContext
    module*: PSym
    filename*: string
  PGen = ref TGen

var gDotGraph: PRope # probably safe: the generated DOT file; we need a global variable

proc addDependencyAux(importing, imported: string) = 
  appf(gDotGraph, "$1 -> $2;$n", [toRope(importing), toRope(imported)]) 
  # s1 -> s2_4[label="[0-9]"];
  
proc addDotDependency(c: PPassContext, n: PNode): PNode = 
  result = n
  if n == nil: return 
  var g = PGen(c)
  case n.kind
  of nkImportStmt: 
    for i in countup(0, sonsLen(n) - 1): 
      var imported = splitFile(getModuleFile(n.sons[i])).name
      addDependencyAux(g.module.name.s, imported)
  of nkFromStmt: 
    var imported = splitFile(getModuleFile(n.sons[0])).name
    addDependencyAux(g.module.name.s, imported)
  of nkStmtList, nkBlockStmt, nkStmtListExpr, nkBlockExpr: 
    for i in countup(0, sonsLen(n) - 1): discard addDotDependency(c, n.sons[i])
  else: 
    nil

proc generateDot(project: string) = 
  writeRope(ropef("digraph $1 {$n$2}$n", [
      toRope(changeFileExt(extractFileName(project), "")), gDotGraph]), 
            changeFileExt(project, "dot"))

proc myOpen(module: PSym, filename: string): PPassContext = 
  var g: PGen
  new(g)
  g.module = module
  g.filename = filename
  result = g

proc gendependPass(): TPass = 
  initPass(result)
  result.open = myOpen
  result.process = addDotDependency
