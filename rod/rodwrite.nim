#
#
#           The Nimrod Compiler
#        (c) Copyright 2008 Andreas Rumpf
#
#    See the file "copying.txt", included in this
#    distribution, for details about the copyright.
#

# This module is responsible for writing of rod files. Note that writing of
# rod files is a pass, reading of rod files is not! This is why reading and
# writing of rod files is split into two different modules.

import 
  os, options, strutils, nversion, ast, astalgo, msgs, platform, condsyms, 
  ropes, idents, crc, rodread, passes, importer

proc rodwritePass*(): TPass
# implementation

type 
  TRodWriter = object of TPassContext
    module*: PSym
    crc*: TCrc32
    options*: TOptions
    defines*: PRope
    inclDeps*: PRope
    modDeps*: PRope
    interf*: PRope
    compilerProcs*: PRope
    index*: TIndex[TId, int]
    imports*: TIndex[TId, TId]
    converters*: PRope
    init*: PRope
    data*: PRope
    filename*: string
    sstack*: TSymSeq          # a stack of symbols to process
    tstack*: TTypeSeq         # a stack of types to process
    files*: TStringSeq
    nodes: seq[PNode] # a raw list of nodes to process

  PRodWriter = ref TRodWriter

proc newRodWriter(modfilename: string, crc: TCrc32, module: PSym): PRodWriter
proc addModDep(w: PRodWriter, dep: string)
proc addInclDep(w: PRodWriter, dep: string)
proc addInterfaceSym(w: PRodWriter, s: PSym)
proc addStmt(w: PRodWriter, n: PNode)
proc writeRod(w: PRodWriter)
proc encodeStr(w: PRodWriter, s: string): PRope = 
  result = encode(s)

proc processStacks(w: PRodWriter)

proc getDefines(): PRope = 
  var it: TTabIter
  var s = InitTabIter(it, gSymbols)
  result = nil
  while s != nil: 
    if s.position == 1: 
      if result != nil: app(result, " ")
      app(result, s.name.s)
    s = nextIter(it, gSymbols)

proc fileIdx(w: PRodWriter, filename: string): int = 
  for i in countup(0, high(w.files)): 
    if w.files[i] == filename: 
      return i
  result = len(w.files)
  setlen(w.files, result + 1)
  w.files[result] = filename

proc newRodWriter(modfilename: string, crc: TCrc32, module: PSym): PRodWriter = 
  new(result)
  result.sstack = @ []
  result.tstack = @ []
  InitXYTable(result.index.tab)
  InitXYTable(result.imports.tab)
  result.filename = modfilename
  result.crc = crc
  result.module = module
  result.defines = getDefines()
  result.options = options.gOptions
  result.files = @ []
  result.nodes = @ []

proc addModDep(w: PRodWriter, dep: string) = 
  if w.modDeps != nil: app(w.modDeps, " ")
  app(w.modDeps, encode(fileIdx(w, dep)))

const 
  rodNL = "\x0A"

proc addInclDep(w: PRodWriter, dep: string) = 
  app(w.inclDeps, encode(fileIdx(w, dep)))
  app(w.inclDeps, " ")
  app(w.inclDeps, encode(crcFromFile(dep)))
  app(w.inclDeps, rodNL)

proc pushType(w: PRodWriter, t: PType) = 
  # check so that the stack does not grow too large:
  if XYTableGet(w.index.tab, t.id) == InvalidKeyInt: 
    var L = len(w.tstack)
    setlen(w.tstack, L + 1)
    w.tstack[L] = t

proc pushSym(w: PRodWriter, s: PSym) = 
  # check so that the stack does not grow too large:
  if XYTableGet(w.index.tab, s.id) == InvalidKeyInt:
    var L = len(w.sstack)
    setlen(w.sstack, L + 1)
    w.sstack[L] = s

proc encodeNode(w: PRodWriter, fInfo: TLineInfo, n: PNode): PRope = 
  if n == nil: 
    # nil nodes have to be stored too:
    return toRope("()")
  result = toRope("(")
  app(result, encode(ord(n.kind))) 
  # we do not write comments for now
  # Line information takes easily 20% or more of the filesize! Therefore we
  # omit line information if it is the same as the father's line information:
  if (finfo.fileIndex != n.info.fileIndex): 
    appf(result, "?$1,$2,$3", [encode(n.info.col), encode(n.info.line), 
                               encode(fileIdx(w, toFilename(n.info)))])
  elif (finfo.line != n.info.line): 
    appf(result, "?$1,$2", [encode(n.info.col), encode(n.info.line)])
  elif (finfo.col != n.info.col): 
    appf(result, "?$1", [encode(n.info.col)]) 
  # No need to output the file index, as this is the serialization of one
  # file.
  var f = n.flags * PersistentNodeFlags
  if f != {}: appf(result, "$$$1", [encode(cast[int32](f))])
  if n.typ != nil: 
    appf(result, "^$1", [encode(n.typ.id)])
    pushType(w, n.typ)
  case n.kind
  of nkCharLit..nkInt64Lit: 
    if n.intVal != 0: appf(result, "!$1", [encode(n.intVal)])
  of nkFloatLit..nkFloat64Lit: 
    if n.floatVal != 0.0: appf(result, "!$1", [encodeStr(w, $(n.floatVal))])
  of nkStrLit..nkTripleStrLit: 
    if n.strVal != "": appf(result, "!$1", [encodeStr(w, n.strVal)])
  of nkIdent: 
    appf(result, "!$1", [encodeStr(w, n.ident.s)])
  of nkSym: 
    appf(result, "!$1", [encode(n.sym.id)])
    pushSym(w, n.sym)
  else: 
    for i in countup(0, sonsLen(n) - 1): 
      app(result, encodeNode(w, n.info, n.sons[i]))
  app(result, ")")

proc encodeLoc(w: PRodWriter, loc: TLoc): PRope = 
  result = nil
  if loc.k != low(loc.k): app(result, encode(ord(loc.k)))
  if loc.s != low(loc.s): appf(result, "*$1", [encode(ord(loc.s))])
  if loc.flags != {}: appf(result, "$$$1", [encode(cast[int32](loc.flags))])
  if loc.t != nil: 
    appf(result, "^$1", [encode(loc.t.id)])
    pushType(w, loc.t)
  if loc.r != nil: appf(result, "!$1", [encodeStr(w, ropeToStr(loc.r))])
  if loc.a != 0: appf(result, "?$1", [encode(loc.a)])
  if result != nil: result = ropef("<$1>", [result])
  
proc encodeType(w: PRodWriter, t: PType): PRope = 
  if t == nil: 
    # nil nodes have to be stored too:
    return toRope("[]")
  result = nil
  if t.kind == tyForward: InternalError("encodeType: tyForward")
  app(result, encode(ord(t.kind)))
  appf(result, "+$1", [encode(t.id)])
  if t.n != nil: app(result, encodeNode(w, UnknownLineInfo(), t.n))
  if t.flags != {}: appf(result, "$$$1", [encode(cast[int32](t.flags))])
  if t.callConv != low(t.callConv): 
    appf(result, "?$1", [encode(ord(t.callConv))])
  if t.owner != nil: 
    appf(result, "*$1", [encode(t.owner.id)])
    pushSym(w, t.owner)
  if t.sym != nil: 
    appf(result, "&$1", [encode(t.sym.id)])
    pushSym(w, t.sym)
  if t.size != - 1: appf(result, "/$1", [encode(t.size)])
  if t.align != 2: appf(result, "=$1", [encode(t.align)])
  if t.containerID != nilID: appf(result, "@$1", [encode(t.containerID)])
  app(result, encodeLoc(w, t.loc))
  for i in countup(0, sonsLen(t) - 1): 
    if t.sons[i] == nil: 
      app(result, "^()")
    else: 
      appf(result, "^$1", [encode(t.sons[i].id)])
      pushType(w, t.sons[i])

proc encodeLib(w: PRodWriter, lib: PLib, info: TLineInfo): PRope = 
  result = nil
  appf(result, "|$1", [encode(ord(lib.kind))])
  appf(result, "|$1", [encodeStr(w, ropeToStr(lib.name))])
  appf(result, "|$1", [encodeNode(w, info, lib.path)])

proc encodeSym(w: PRodWriter, s: PSym): PRope = 
  var 
    codeAst: PNode
    col, line: PRope
  codeAst = nil
  if s == nil: 
    # nil nodes have to be stored too:
    return toRope("{}")
  result = nil
  app(result, encode(ord(s.kind)))
  appf(result, "+$1", [encode(s.id)])
  appf(result, "&$1", [encodeStr(w, s.name.s)])
  if s.typ != nil: 
    appf(result, "^$1", [encode(s.typ.id)])
    pushType(w, s.typ)
  if s.info.col == int16(- 1): col = nil
  else: col = encode(s.info.col)
  if s.info.line == int16(- 1): line = nil
  else: line = encode(s.info.line)
  appf(result, "?$1,$2,$3", 
       [col, line, encode(fileIdx(w, toFilename(s.info)))])
  if s.owner != nil: 
    appf(result, "*$1", [encode(s.owner.id)])
    pushSym(w, s.owner)
  if s.flags != {}: appf(result, "$$$1", [encode(cast[int32](s.flags))])
  if s.magic != mNone: appf(result, "@$1", [encode(ord(s.magic))])
  if (s.ast != nil): 
    if not astNeeded(s): 
      codeAst = s.ast.sons[codePos]
      s.ast.sons[codePos] = nil
    app(result, encodeNode(w, s.info, s.ast))
    if codeAst != nil: 
      s.ast.sons[codePos] = codeAst
  if s.options != w.options: 
    appf(result, "!$1", [encode(cast[int32](s.options))])
  if s.position != 0: appf(result, "%$1", [encode(s.position)])
  if s.offset != - 1: appf(result, "`$1", [encode(s.offset)])
  app(result, encodeLoc(w, s.loc))
  if s.annex != nil: app(result, encodeLib(w, s.annex, s.info))
    
  
proc addToIndex[X, Y](w: var TIndex[X, Y], key: X, val: Y) =
  # screw compression
  app(w.r, encode(key))
  app(w.r, "=")
  app(w.r, encode(val))
  app(w.r, "=")
  XYTablePut(w.tab, key, val)

var debugWritten: TOrdSet[int]

proc symStack(w: PRodWriter) = 
  var 
    i, L: int
    s, m: PSym
  i = 0
  while i < len(w.sstack): 
    s = w.sstack[i]
    if XYTableGet(w.index.tab, s.id) == InvalidKeyInt:
      m = getModule(s)
      if m == nil: InternalError("symStack: module nil: " & s.name.s)
      if (m.id == w.module.id) or (sfFromGeneric in s.flags): 
        # put definition in here
        L = ropeLen(w.data)
        addToIndex(w.index, s.id, L) #intSetIncl(debugWritten, s.id);
        app(w.data, encodeSym(w, s))
        app(w.data, rodNL)
        if sfInInterface in s.flags: 
          appf(w.interf, "$1 $2" & rodNL, [encode(s.name.s), encode(s.id)])
        if sfCompilerProc in s.flags: 
          appf(w.compilerProcs, "$1 $2" & rodNL, 
               [encode(s.name.s), encode(s.id)])
        if s.kind == skConverter: 
          if w.converters != nil: app(w.converters, " ")
          app(w.converters, encode(s.id))
      elif XYTableGet(w.imports.tab, s.id) == InvalidKeyTId:
        addToIndex(w.imports, s.id, m.id) #if not OrdSetContains(debugWritten, s.id) then begin 
                                          #  MessageOut(w.filename);
                                          #  debug(s.owner);
                                          #  debug(s);
                                          #  InternalError('BUG!!!!');
                                          #end
    inc(i)
  setlen(w.sstack, 0)

proc typeStack(w: PRodWriter) = 
  var i, L: int
  i = 0
  while i < len(w.tstack): 
    if XYTableGet(w.index.tab, w.tstack[i].id) == InvalidKeyInt:
      L = ropeLen(w.data)
      addToIndex(w.index, w.tstack[i].id, L)
      app(w.data, encodeType(w, w.tstack[i]))
      app(w.data, rodNL)
    inc(i)
  setlen(w.tstack, 0)

proc processStacks(w: PRodWriter) = 
  while (len(w.tstack) > 0) or (len(w.sstack) > 0): 
    symStack(w)
    typeStack(w)

proc rawAddInterfaceSym(w: PRodWriter, s: PSym) = 
  pushSym(w, s)
  processStacks(w)

proc addInterfaceSym(w: PRodWriter, s: PSym) = 
  if w == nil: return 
  if {sfInInterface, sfCompilerProc} * s.flags != {}: 
    rawAddInterfaceSym(w, s)

proc addStmt(w: PRodWriter, n: PNode) = 
  app(w.init, encode(ropeLen(w.data)))
  app(w.init, rodNL)
  app(w.data, encodeNode(w, UnknownLineInfo(), n))
  app(w.data, rodNL)
  processStacks(w)

proc writeRod(w: PRodWriter) = 
  var content: PRope
  processStacks(w)            # write header:
  content = toRope("NIM:")
  app(content, toRope(FileVersion))
  app(content, rodNL)
  app(content, toRope("ID:"))
  app(content, encode(w.module.id))
  app(content, rodNL)
  app(content, toRope("CRC:"))
  app(content, encode(w.crc))
  app(content, rodNL)
  app(content, toRope("TIC(" & rodNL))
  app(content, encode(ropeToStr(w.module.typeInitCode1)))
  app(content, rodNL)
  app(content, encode(ropeToStr(w.module.typeInitCode2)))
  app(content, rodNL)
  app(content, toRope(')' & rodNL))
  app(content, toRope("OPTIONS:"))
  app(content, encode(cast[int32](w.options)))
  app(content, rodNL)
  app(content, toRope("DEFINES:"))
  app(content, w.defines)
  app(content, rodNL)
  app(content, toRope("FILES(" & rodNL))
  for i in countup(0, high(w.files)): 
    app(content, encode(w.files[i]))
    app(content, rodNL)
  app(content, toRope(')' & rodNL))
  app(content, toRope("INCLUDES(" & rodNL))
  app(content, w.inclDeps)
  app(content, toRope(')' & rodNL))
  app(content, toRope("DEPS:"))
  app(content, w.modDeps)
  app(content, rodNL)
  app(content, toRope("INTERF(" & rodNL))
  app(content, w.interf)
  app(content, toRope(')' & rodNL))
  app(content, toRope("COMPILERPROCS(" & rodNL))
  app(content, w.compilerProcs)
  app(content, toRope(')' & rodNL))
  app(content, toRope("INDEX(" & rodNL))
  app(content, w.index.r)
  app(content, toRope(')' & rodNL))
  app(content, toRope("IMPORTS(" & rodNL))
  app(content, w.imports.r)
  app(content, toRope(')' & rodNL))
  app(content, toRope("CONVERTERS:"))
  app(content, w.converters)
  app(content, toRope(rodNL))
  app(content, toRope("INIT(" & rodNL))
  app(content, w.init)
  app(content, toRope(')' & rodNL))
  app(content, toRope("DATA(" & rodNL))
  app(content, w.data)
  app(content, toRope(')' & rodNL)) 
  #MessageOut('interf ' + ToString(ropeLen(w.interf)));
  #MessageOut('index ' + ToString(ropeLen(w.indexRope)));
  #MessageOut('init ' + ToString(ropeLen(w.init)));
  #MessageOut('data ' + ToString(ropeLen(w.data)));
  writeRope(content, completeGeneratedFilePath(changeFileExt(w.filename, "rod")))

proc process(c: PPassContext, n: PNode): PNode = 
  var 
    w: PRodWriter
  result = n
  if c == nil: return 
  w = PRodWriter(c)
  w.nodes.add(n)

proc processReal(w : PRodWriter, n : PNode) =
  var
    a: PNode
    s: PSym
  case n.kind
  of nkStmtList: 
    for i in countup(0, sonsLen(n) - 1): processReal(w, n.sons[i])
  of nkTemplateDef, nkMacroDef: 
    s = n.sons[namePos].sym
    addInterfaceSym(w, s)
  of nkProcDef, nkMethodDef, nkIteratorDef, nkConverterDef: 
    s = n.sons[namePos].sym
    if s == nil: InternalError(n.info, "rodwrite.process")
    if (n.sons[codePos] != nil) or (s.magic != mNone) or
        not (sfForward in s.flags): 
      addInterfaceSym(w, s)
  of nkVarSection: 
    for i in countup(0, sonsLen(n) - 1): 
      a = n.sons[i]
      if a.kind == nkCommentStmt: continue 
      if a.kind != nkIdentDefs: InternalError(a.info, "rodwrite.process")
      addInterfaceSym(w, a.sons[0].sym)
  of nkConstSection: 
    for i in countup(0, sonsLen(n) - 1): 
      a = n.sons[i]
      if a.kind == nkCommentStmt: continue 
      if a.kind != nkConstDef: InternalError(a.info, "rodwrite.process")
      addInterfaceSym(w, a.sons[0].sym)
  of nkTypeSection: 
    for i in countup(0, sonsLen(n) - 1): 
      a = n.sons[i]
      if a.kind == nkCommentStmt: continue 
      if a.sons[0].kind != nkSym: InternalError(a.info, "rodwrite.process")
      s = a.sons[0].sym
      addInterfaceSym(w, s) 
      # this takes care of enum fields too
      # Note: The check for ``s.typ.kind = tyEnum`` is wrong for enum
      # type aliasing! Otherwise the same enum symbol would be included
      # several times!
      #
      #        if (a.sons[2] <> nil) and (a.sons[2].kind = nkEnumTy) then begin
      #          a := s.typ.n;
      #          for j := 0 to sonsLen(a)-1 do 
      #            addInterfaceSym(w, a.sons[j].sym);        
      #        end 
  of nkImportStmt: 
    for i in countup(0, sonsLen(n) - 1): addModDep(w, getModuleFile(n.sons[i]))
    addStmt(w, n)
  of nkFromStmt: 
    addModDep(w, getModuleFile(n.sons[0]))
    addStmt(w, n)
  of nkIncludeStmt: 
    for i in countup(0, sonsLen(n) - 1): addInclDep(w, getModuleFile(n.sons[i]))
  of nkPragma: 
    addStmt(w, n)
  else: 
    nil

proc myOpen(module: PSym, filename: string): PPassContext = 
  if module.id == nilId: InternalError("rodwrite: module ID not set")
  var w = newRodWriter(filename, rodread.GetCRC(filename), module)
  result = w

proc myClose(c: PPassContext, n: PNode): PNode = 
  var w = PRodWriter(c)
  for node in w.nodes.items:
    processReal(w, node)
  rawAddInterfaceSym(w, w.module)
  writeRod(w)
  result = n

proc rodwritePass(): TPass = 
  initPass(result)
  if optSymbolFiles in gGlobalOptions: 
    result.open = myOpen
    result.close = myClose
    result.process = process

OrdSetInit(debugWritten)
