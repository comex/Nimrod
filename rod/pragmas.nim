#
#
#           The Nimrod Compiler
#        (c) Copyright 2010 Andreas Rumpf
#
#    See the file "copying.txt", included in this
#    distribution, for details about the copyright.
#

# This module implements semantic checking for pragmas

import 
  os, platform, condsyms, ast, astalgo, idents, semdata, msgs, rnimsyn, 
  wordrecg, ropes, options, strutils, lists, extccomp, math, magicsys, trees

const 
  FirstCallConv* = wNimcall
  LastCallConv* = wNoconv

const 
  procPragmas* = {FirstCallConv..LastCallConv, wImportc, wExportc, wNodecl, 
    wMagic, wNosideEffect, wSideEffect, wNoreturn, wDynLib, wHeader, 
    wCompilerProc, wPure, wProcVar, wDeprecated, wVarargs, wCompileTime, wMerge, 
    wBorrow, wExtern}
  converterPragmas* = procPragmas
  methodPragmas* = procPragmas
  macroPragmas* = {FirstCallConv..LastCallConv, wImportc, wExportc, wNodecl, 
    wMagic, wNosideEffect, wCompilerProc, wDeprecated, wTypeCheck, wExtern}
  iteratorPragmas* = {FirstCallConv..LastCallConv, wNosideEffect, wSideEffect, 
    wImportc, wExportc, wNodecl, wMagic, wDeprecated, wBorrow, wExtern}
  stmtPragmas* = {wChecks, wObjChecks, wFieldChecks, wRangechecks, wBoundchecks, 
    wOverflowchecks, wNilchecks, wAssertions, wWarnings, wHints, wLinedir, 
    wStacktrace, wLinetrace, wOptimization, wHint, wWarning, wError, wFatal, 
    wDefine, wUndef, wCompile, wLink, wLinkSys, wPure, wPush, wPop, wBreakpoint, 
    wCheckpoint, wPassL, wPassC, wDeadCodeElim, wDeprecated, wFloatChecks,
    wInfChecks, wNanChecks, wPragma}
  lambdaPragmas* = {FirstCallConv..LastCallConv, wImportc, wExportc, wNodecl, 
    wNosideEffect, wSideEffect, wNoreturn, wDynLib, wHeader, wPure, 
    wDeprecated, wExtern}
  typePragmas* = {wImportc, wExportc, wDeprecated, wMagic, wAcyclic, wNodecl, 
    wPure, wHeader, wCompilerProc, wFinal, wSize, wExtern}
  fieldPragmas* = {wImportc, wExportc, wDeprecated, wExtern}
  varPragmas* = {wImportc, wExportc, wVolatile, wRegister, wThreadVar, wNodecl, 
    wMagic, wHeader, wDeprecated, wCompilerProc, wDynLib, wExtern}
  constPragmas* = {wImportc, wExportc, wHeader, wDeprecated, wMagic, wNodecl,
    wExtern}
  procTypePragmas* = {FirstCallConv..LastCallConv, wVarargs, wNosideEffect}

proc pragma*(c: PContext, sym: PSym, n: PNode, validPragmas: TSpecialWords)
proc pragmaAsm*(c: PContext, n: PNode): char
# implementation

proc invalidPragma(n: PNode) = 
  liMessage(n.info, errInvalidPragmaX, renderTree(n, {renderNoComments}))

proc pragmaAsm(c: PContext, n: PNode): char = 
  result = '\0'
  if n != nil: 
    for i in countup(0, sonsLen(n) - 1): 
      var it = n.sons[i]
      if (it.kind == nkExprColonExpr) and (it.sons[0].kind == nkIdent): 
        case whichKeyword(it.sons[0].ident)
        of wSubsChar: 
          if it.sons[1].kind == nkCharLit: result = chr(int(it.sons[1].intVal))
          else: invalidPragma(it)
        else: invalidPragma(it)
      else: 
        invalidPragma(it)

proc setExternName(s: PSym, extname: string) = 
  s.loc.r = toRope(extname % s.name.s)

proc MakeExternImport(s: PSym, extname: string) = 
  setExternName(s, extname)
  incl(s.flags, sfImportc)
  excl(s.flags, sfForward)

proc MakeExternExport(s: PSym, extname: string) = 
  setExternName(s, extname)
  incl(s.flags, sfExportc)

proc getStrLitNode(c: PContext, n: PNode): PNode =
  if n.kind != nkExprColonExpr: 
    liMessage(n.info, errStringLiteralExpected)
  else: 
    n.sons[1] = c.semConstExpr(c, n.sons[1])
    case n.sons[1].kind
    of nkStrLit, nkRStrLit, nkTripleStrLit: result = n.sons[1]
    else: liMessage(n.info, errStringLiteralExpected)

proc expectStrLit(c: PContext, n: PNode): string = 
  result = getStrLitNode(c, n).strVal

proc expectIntLit(c: PContext, n: PNode): int = 
  if n.kind != nkExprColonExpr: 
    liMessage(n.info, errIntLiteralExpected)
    result = 0
  else: 
    n.sons[1] = c.semConstExpr(c, n.sons[1])
    case n.sons[1].kind
    of nkIntLit..nkInt64Lit: result = int(n.sons[1].intVal)
    else: 
      liMessage(n.info, errIntLiteralExpected)
      result = 0

proc getOptionalStr(c: PContext, n: PNode, defaultStr: string): string = 
  if n.kind == nkExprColonExpr: result = expectStrLit(c, n)
  else: result = defaultStr
  
proc processMagic(c: PContext, n: PNode, s: PSym) = 
  var v: string
  #if not (sfSystemModule in c.module.flags) then
  #  liMessage(n.info, errMagicOnlyInSystem);
  if n.kind != nkExprColonExpr: liMessage(n.info, errStringLiteralExpected)
  if n.sons[1].kind == nkIdent: v = n.sons[1].ident.s
  else: v = expectStrLit(c, n)
  incl(s.flags, sfImportc) 
  # magics don't need an implementation, so we
  # treat them as imported, instead of modifing a lot of working code
  # BUGFIX: magic does not imply ``lfNoDecl`` anymore!
  for m in countup(low(TMagic), high(TMagic)): 
    if copy($m, 1) == v: 
      s.magic = m
      return 
  liMessage(n.info, warnUnknownMagic, v)

proc wordToCallConv(sw: TSpecialWord): TCallingConvention = 
  # this assumes that the order of special words and calling conventions is
  # the same
  result = TCallingConvention(ord(ccDefault) + ord(sw) - ord(wNimcall))

proc IsTurnedOn(c: PContext, n: PNode): bool = 
  if (n.kind == nkExprColonExpr) and (n.sons[1].kind == nkIdent): 
    case whichKeyword(n.sons[1].ident)
    of wOn: result = true
    of wOff: result = false
    else: liMessage(n.info, errOnOrOffExpected)
  else: 
    liMessage(n.info, errOnOrOffExpected)

proc onOff(c: PContext, n: PNode, op: TOptions) = 
  if IsTurnedOn(c, n): gOptions = gOptions + op
  else: gOptions = gOptions - op
  
proc pragmaDeadCodeElim(c: PContext, n: PNode) = 
  return #XXX
  #if IsTurnedOn(c, n): incl(c.module.flags, sfDeadCodeElim)
  #else: excl(c.module.flags, sfDeadCodeElim)
  
proc processCallConv(c: PContext, n: PNode) = 
  if (n.kind == nkExprColonExpr) and (n.sons[1].kind == nkIdent): 
    var sw = whichKeyword(n.sons[1].ident)
    case sw
    of firstCallConv..lastCallConv: 
      POptionEntry(c.optionStack.tail).defaultCC = wordToCallConv(sw)
    else: liMessage(n.info, errCallConvExpected)
  else: 
    liMessage(n.info, errCallConvExpected)
  
proc getLib(c: PContext, kind: TLibKind, path: PNode): PLib = 
  var it = PLib(c.libs.head)
  while it != nil: 
    if it.kind == kind: 
      if trees.ExprStructuralEquivalent(it.path, path): return it
    it = PLib(it.next)
  result = newLib(kind)
  result.path = path
  Append(c.libs, result)

proc expectDynlibNode(c: PContext, n: PNode): PNode = 
  if n.kind != nkExprColonExpr: liMessage(n.info, errStringLiteralExpected)
  else: 
    result = c.semExpr(c, n.sons[1])
    if result.kind == nkSym and result.sym.kind == skConst:
      result = result.sym.ast # look it up
    if result.typ == nil or result.typ.kind != tyString: 
      liMessage(n.info, errStringLiteralExpected)
    
proc processDynLib(c: PContext, n: PNode, sym: PSym) = 
  if (sym == nil) or (sym.kind == skModule): 
    POptionEntry(c.optionStack.tail).dynlib = getLib(c, libDynamic, 
        expectDynlibNode(c, n))
  elif n.kind == nkExprColonExpr: 
    var lib = getLib(c, libDynamic, expectDynlibNode(c, n))
    addToLib(lib, sym)
    incl(sym.loc.flags, lfDynamicLib)
  else: 
    incl(sym.loc.flags, lfExportLib)
  
proc processNote(c: PContext, n: PNode) = 
  if (n.kind == nkExprColonExpr) and (sonsLen(n) == 2) and
      (n.sons[0].kind == nkBracketExpr) and
      (n.sons[0].sons[1].kind == nkIdent) and
      (n.sons[0].sons[0].kind == nkIdent) and (n.sons[1].kind == nkIdent): 
    var nk: TNoteKind
    case whichKeyword(n.sons[0].sons[0].ident)
    of wHint: 
      var x = findStr(msgs.HintsToStr, n.sons[0].sons[1].ident.s)
      if x >= 0: nk = TNoteKind(x + ord(hintMin))
      else: invalidPragma(n)
    of wWarning: 
      var x = findStr(msgs.WarningsToStr, n.sons[0].sons[1].ident.s)
      if x >= 0: nk = TNoteKind(x + ord(warnMin))
      else: InvalidPragma(n)
    else: 
      invalidPragma(n)
      return 
    case whichKeyword(n.sons[1].ident)
    of wOn: incl(gNotes, nk)
    of wOff: excl(gNotes, nk)
    else: liMessage(n.info, errOnOrOffExpected)
  else: 
    invalidPragma(n)
  
proc processOption(c: PContext, n: PNode) = 
  if n.kind != nkExprColonExpr: invalidPragma(n)
  elif n.sons[0].kind == nkBracketExpr: processNote(c, n)
  elif n.sons[0].kind != nkIdent: invalidPragma(n)
  else: 
    var sw = whichKeyword(n.sons[0].ident)
    case sw
    of wChecks: OnOff(c, n, checksOptions)
    of wObjChecks: OnOff(c, n, {optObjCheck})
    of wFieldchecks: OnOff(c, n, {optFieldCheck})
    of wRangechecks: OnOff(c, n, {optRangeCheck})
    of wBoundchecks: OnOff(c, n, {optBoundsCheck})
    of wOverflowchecks: OnOff(c, n, {optOverflowCheck})
    of wNilchecks: OnOff(c, n, {optNilCheck})
    of wFloatChecks: OnOff(c, n, {optNanCheck, optInfCheck})
    of wNaNchecks: OnOff(c, n, {optNanCheck})
    of wInfChecks: OnOff(c, n, {optInfCheck})
    of wAssertions: OnOff(c, n, {optAssert})
    of wWarnings: OnOff(c, n, {optWarns})
    of wHints: OnOff(c, n, {optHints})
    of wCallConv: processCallConv(c, n)   
    of wLinedir: OnOff(c, n, {optLineDir})
    of wStacktrace: OnOff(c, n, {optStackTrace})
    of wLinetrace: OnOff(c, n, {optLineTrace})
    of wDebugger: OnOff(c, n, {optEndb})
    of wProfiler: OnOff(c, n, {optProfiler})
    of wByRef: OnOff(c, n, {optByRef})
    of wDynLib: processDynLib(c, n, nil) 
    of wOptimization: 
      if n.sons[1].kind != nkIdent: 
        invalidPragma(n)
      else: 
        case whichKeyword(n.sons[1].ident)
        of wSpeed: 
          incl(gOptions, optOptimizeSpeed)
          excl(gOptions, optOptimizeSize)
        of wSize: 
          excl(gOptions, optOptimizeSpeed)
          incl(gOptions, optOptimizeSize)
        of wNone: 
          excl(gOptions, optOptimizeSpeed)
          excl(gOptions, optOptimizeSize)
        else: liMessage(n.info, errNoneSpeedOrSizeExpected)
    else: liMessage(n.info, errOptionExpected)
  
proc processPush(c: PContext, n: PNode, start: int) = 
  var x = newOptionEntry()
  var y = POptionEntry(c.optionStack.tail)
  x.options = gOptions
  x.defaultCC = y.defaultCC
  x.dynlib = y.dynlib
  x.notes = gNotes
  append(c.optionStack, x)
  for i in countup(start, sonsLen(n) - 1): 
    processOption(c, n.sons[i]) 
    #liMessage(n.info, warnUser, ropeToStr(optionsToStr(gOptions)));
  
proc processPop(c: PContext, n: PNode) = 
  if c.optionStack.counter <= 1: 
    liMessage(n.info, errAtPopWithoutPush)
  else: 
    gOptions = POptionEntry(c.optionStack.tail).options 
    #liMessage(n.info, warnUser, ropeToStr(optionsToStr(gOptions)));
    gNotes = POptionEntry(c.optionStack.tail).notes
    remove(c.optionStack, c.optionStack.tail)

proc processDefine(c: PContext, n: PNode) = 
  if (n.kind == nkExprColonExpr) and (n.sons[1].kind == nkIdent): 
    DefineSymbol(n.sons[1].ident.s)
    liMessage(n.info, warnDeprecated, "define")
  else: 
    invalidPragma(n)
  
proc processUndef(c: PContext, n: PNode) = 
  if (n.kind == nkExprColonExpr) and (n.sons[1].kind == nkIdent): 
    UndefSymbol(n.sons[1].ident.s)
    liMessage(n.info, warnDeprecated, "undef")
  else: 
    invalidPragma(n)
  
type 
  TLinkFeature = enum 
    linkNormal, linkSys

proc processCompile(c: PContext, n: PNode) = 
  var s = expectStrLit(c, n)
  var found = findFile(s)
  if found == "": found = s
  var trunc = ChangeFileExt(found, "")
  extccomp.addExternalFileToCompile(found)
  extccomp.addFileToLink(completeCFilePath(trunc, false))

proc processCommonLink(c: PContext, n: PNode, feature: TLinkFeature) = 
  var f = expectStrLit(c, n)
  if splitFile(f).ext == "": f = toObjFile(f)
  var found = findFile(f)
  if found == "": found = f # use the default
  case feature
  of linkNormal: extccomp.addFileToLink(found)
  of linkSys: 
    extccomp.addFileToLink(joinPath(libpath, completeCFilePath(found, false)))
  else: internalError(n.info, "processCommonLink")
  
proc PragmaBreakpoint(c: PContext, n: PNode) = 
  discard getOptionalStr(c, n, "")

proc PragmaCheckpoint(c: PContext, n: PNode) = 
  # checkpoints can be used to debug the compiler; they are not documented
  var info = n.info
  inc(info.line)              # next line is affected!
  msgs.addCheckpoint(info)

proc noVal(n: PNode) = 
  if n.kind == nkExprColonExpr: invalidPragma(n)

proc processPragma(c: PContext, n: PNode, i: int) = 
  var it = n.sons[i]
  if it.kind != nkExprColonExpr: invalidPragma(n)
  elif it.sons[0].kind != nkIdent: invalidPragma(n)
  elif it.sons[1].kind != nkIdent: invalidPragma(n)
  
  var userPragma = NewSym(skTemplate, it.sons[1].ident, nil)
  userPragma.info = it.info
  var body = newNodeI(nkPragma, n.info)
  for j in i+1 .. sonsLen(n)-1: addSon(body, n.sons[j])
  userPragma.ast = body
  StrTableAdd(c.userPragmas, userPragma)
        
proc pragma(c: PContext, sym: PSym, n: PNode, validPragmas: TSpecialWords) = 
  if n == nil: return 
  for i in countup(0, sonsLen(n) - 1): 
    var it = n.sons[i]
    var key = if it.kind == nkExprColonExpr: it.sons[0] else: it
    if key.kind == nkIdent: 
      var userPragma = StrTableGet(c.userPragmas, key.ident)
      if userPragma != nil: 
        pragma(c, sym, userPragma.ast, validPragmas)
        # XXX BUG: possible infinite recursion!
      else:
        var k = whichKeyword(key.ident)
        if k in validPragmas: 
          case k
          of wExportc: 
            makeExternExport(sym, getOptionalStr(c, it, sym.name.s))
            incl(sym.flags, sfUsed) # avoid wrong hints
          of wImportc: makeExternImport(sym, getOptionalStr(c, it, sym.name.s))
          of wExtern: setExternName(sym, expectStrLit(c, it))
          of wAlign: 
            if sym.typ == nil: invalidPragma(it)
            sym.typ.align = expectIntLit(c, it)
            if not IsPowerOfTwo(sym.typ.align) and (sym.typ.align != 0): 
              liMessage(it.info, errPowerOfTwoExpected)
          of wSize: 
            if sym.typ == nil: invalidPragma(it)
            var size = expectIntLit(c, it)
            if not IsPowerOfTwo(size) or size <= 0 or size > 8: 
              liMessage(it.info, errPowerOfTwoExpected)
            else:
              sym.typ.size = size
          of wNodecl: 
            noVal(it)
            incl(sym.loc.Flags, lfNoDecl)
          of wPure: 
            noVal(it)
            if sym != nil: incl(sym.flags, sfPure)
          of wVolatile: 
            noVal(it)
            incl(sym.flags, sfVolatile)
          of wRegister: 
            noVal(it)
            incl(sym.flags, sfRegister)
          of wThreadVar: 
            noVal(it)
            incl(sym.flags, sfThreadVar)
          of wDeadCodeElim: pragmaDeadCodeElim(c, it)
          of wMagic: processMagic(c, it, sym)
          of wCompileTime: 
            noVal(it)
            incl(sym.flags, sfCompileTime)
            incl(sym.loc.Flags, lfNoDecl)
          of wMerge: 
            noval(it)
            incl(sym.flags, sfMerge)
          of wHeader: 
            var lib = getLib(c, libHeader, getStrLitNode(c, it))
            addToLib(lib, sym)
            incl(sym.flags, sfImportc)
            incl(sym.loc.flags, lfHeader)
            incl(sym.loc.Flags, lfNoDecl) 
            # implies nodecl, because otherwise header would not make sense
            if sym.loc.r == nil: sym.loc.r = toRope(sym.name.s)
          of wNosideeffect: 
            noVal(it)
            incl(sym.flags, sfNoSideEffect)
            if sym.typ != nil: incl(sym.typ.flags, tfNoSideEffect)
          of wSideEffect: 
            noVal(it)
            incl(sym.flags, sfSideEffect)
          of wNoReturn: 
            noVal(it)
            incl(sym.flags, sfNoReturn)
          of wDynLib: 
            processDynLib(c, it, sym)
          of wCompilerProc: 
            noVal(it)           # compilerproc may not get a string!
            makeExternExport(sym, sym.name.s)
            incl(sym.flags, sfCompilerProc)
            incl(sym.flags, sfUsed) # suppress all those stupid warnings
            registerCompilerProc(sym)
          of wProcvar: 
            noVal(it)
            incl(sym.flags, sfProcVar)
          of wDeprecated: 
            noVal(it)
            if sym != nil: incl(sym.flags, sfDeprecated)
            else: incl(c.module.flags, sfDeprecated)
          of wVarargs: 
            noVal(it)
            if sym.typ == nil: invalidPragma(it)
            incl(sym.typ.flags, tfVarargs)
          of wBorrow: 
            noVal(it)
            incl(sym.flags, sfBorrow)
          of wFinal: 
            noVal(it)
            if sym.typ == nil: invalidPragma(it)
            incl(sym.typ.flags, tfFinal)
          of wAcyclic: 
            noVal(it)
            if sym.typ == nil: invalidPragma(it)
            incl(sym.typ.flags, tfAcyclic)
          of wTypeCheck: 
            noVal(it)
            incl(sym.flags, sfTypeCheck)
          of wHint: liMessage(it.info, hintUser, expectStrLit(c, it))
          of wWarning: liMessage(it.info, warnUser, expectStrLit(c, it))
          of wError: liMessage(it.info, errUser, expectStrLit(c, it))
          of wFatal: 
            liMessage(it.info, errUser, expectStrLit(c, it))
            quit(1)
          of wDefine: processDefine(c, it)
          of wUndef: processUndef(c, it)
          of wCompile: processCompile(c, it)
          of wLink: processCommonLink(c, it, linkNormal)
          of wLinkSys: processCommonLink(c, it, linkSys)
          of wPassL: extccomp.addLinkOption(expectStrLit(c, it))
          of wPassC: extccomp.addCompileOption(expectStrLit(c, it))
          of wBreakpoint: PragmaBreakpoint(c, it)
          of wCheckpoint: PragmaCheckpoint(c, it)
          of wPush: 
            processPush(c, n, i + 1)
            break 
          of wPop: processPop(c, it)
          of wPragma: 
            processPragma(c, n, i)
            break
          of wChecks, wObjChecks, wFieldChecks, wRangechecks, wBoundchecks, 
             wOverflowchecks, wNilchecks, wAssertions, wWarnings, wHints, 
             wLinedir, wStacktrace, wLinetrace, wOptimization, wByRef,
             wCallConv, 
             wDebugger, wProfiler, wFloatChecks, wNanChecks, wInfChecks: 
            processOption(c, it) # calling conventions (boring...):
          of firstCallConv..lastCallConv: 
            assert(sym != nil)
            if sym.typ == nil: invalidPragma(it)
            sym.typ.callConv = wordToCallConv(k)
          else: invalidPragma(it)
        else: invalidPragma(it)
    else: processNote(c, it)
  if (sym != nil) and (sym.kind != skModule): 
    if (lfExportLib in sym.loc.flags) and not (sfExportc in sym.flags): 
      liMessage(n.info, errDynlibRequiresExportc)
    var lib = POptionEntry(c.optionstack.tail).dynlib
    if ({lfDynamicLib, lfHeader} * sym.loc.flags == {}) and
        (sfImportc in sym.flags) and (lib != nil): 
      incl(sym.loc.flags, lfDynamicLib)
      addToLib(lib, sym)
      if sym.loc.r == nil: sym.loc.r = toRope(sym.name.s)
  
