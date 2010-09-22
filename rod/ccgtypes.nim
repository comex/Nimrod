#
#
#           The Nimrod Compiler
#        (c) Copyright 2009 Andreas Rumpf
#
#    See the file "copying.txt", included in this
#    distribution, for details about the copyright.
#

#var
#  newDummyVar: int; // just to check the symbol file mechanism

# ------------------------- Name Mangling --------------------------------

proc mangle(name: string): string = 
  case name[0]
  of 'a'..'z': 
    result = ""
    add(result, chr(ord(name[0]) - ord('a') + ord('A')))
  of '0'..'9', 'A'..'Z': 
    result = ""
    add(result, name[0])
  else: result = "HEX" & toHex(ord(name[0]), 2)
  for i in countup(0 + 1, len(name) + 0 - 1): 
    case name[i]
    of 'A'..'Z': 
      add(result, chr(ord(name[i]) - ord('A') + ord('a')))
    of '_': 
      nil
    of 'a'..'z', '0'..'9': 
      add(result, name[i])
    else: 
      add(result, "HEX")
      add(result, toHex(ord(name[i]), 2))

proc mangleName(s: PSym): PRope = 
  result = s.loc.r
  if result == nil: 
    if gCmd == cmdCompileToLLVM: 
      case s.kind
      of skProc, skMethod, skConverter, skConst: 
        result = toRope("@")
      of skVar: 
        if (sfGlobal in s.flags): result = toRope("@")
        else: result = toRope("%")
      of skForVar, skTemp, skParam, skType, skEnumField, skModule: 
        result = toRope("%")
      else: InternalError(s.info, "mangleName")
    app(result, toRope(mangle(s.name.s)))
    app(result, "_")
    app(result, toRope(s.id))
    if optGenMapping in gGlobalOptions: 
      if s.owner != nil: 
        appf(gMapping, "r\"$1.$2\": $3$n", 
             [toRope(s.owner.Name.s), toRope(s.name.s), result])
    s.loc.r = result

proc getTypeName(typ: PType): PRope = 
  if (typ.sym != nil) and ({sfImportc, sfExportc} * typ.sym.flags != {}) and
      (gCmd != cmdCompileToLLVM): 
    result = typ.sym.loc.r
  else: 
    if typ.loc.r == nil: typ.loc.r = ropeff("TY$1", "%TY$1", [toRope(typ.id)])
    result = typ.loc.r
  if result == nil: InternalError("getTypeName: " & $typ.kind)
  
proc mapType(typ: PType): TCTypeKind = 
  case typ.kind
  of tyNone: result = ctVoid
  of tyBool: result = ctBool
  of tyChar: result = ctChar
  of tySet: 
    case int(getSize(typ))
    of 1: result = ctInt8
    of 2: result = ctInt16
    of 4: result = ctInt32
    of 8: result = ctInt64
    else: result = ctArray
  of tyOpenArray, tyArrayConstr, tyArray: result = ctArray
  of tyObject, tyTuple: result = ctStruct
  of tyGenericBody, tyGenericInst, tyGenericParam, tyDistinct, tyOrdinal: 
    result = mapType(lastSon(typ))
  of tyEnum: 
    if firstOrd(typ) < 0: 
      result = ctInt32
    else: 
      case int(getSize(typ))
      of 1: result = ctUInt8
      of 2: result = ctUInt16
      of 4: result = ctInt32
      of 8: result = ctInt64
      else: internalError("mapType")
  of tyRange: result = mapType(typ.sons[0])
  of tyPtr, tyVar, tyRef: 
    case typ.sons[0].kind
    of tyOpenArray, tyArrayConstr, tyArray: result = ctArray
    else: result = ctPtr
  of tyPointer: result = ctPtr
  of tySequence: result = ctNimSeq
  of tyProc: result = ctProc
  of tyString: result = ctNimStr
  of tyCString: result = ctCString
  of tyInt..tyFloat128:
    result = TCTypeKind(ord(typ.kind) - ord(tyInt) + ord(ctInt))
  else: InternalError("mapType")
  
proc mapReturnType(typ: PType): TCTypeKind = 
  if skipTypes(typ, abstractInst).kind == tyArray: result = ctPtr
  else: result = mapType(typ)
  
proc getTypeDescAux(m: BModule, typ: PType, check: var TIdSet): PRope
proc needsComplexAssignment(typ: PType): bool = 
  result = containsGarbageCollectedRef(typ)

proc isInvalidReturnType(rettype: PType): bool = 
  # Arrays and sets cannot be returned by a C procedure, because C is
  # such a poor programming language.
  # We exclude records with refs too. This enhances efficiency and
  # is necessary for proper code generation of assignments.
  if rettype == nil: result = true
  else: 
    case mapType(rettype)
    of ctArray: 
      result = not (skipTypes(rettype, abstractInst).kind in
          {tyVar, tyRef, tyPtr})
    of ctStruct: 
      result = needsComplexAssignment(skipTypes(rettype, abstractInst))
    else: result = false
  
const 
  CallingConvToStr: array[TCallingConvention, string] = ["N_NIMCALL", 
    "N_STDCALL", "N_CDECL", "N_SAFECALL", 
    "N_SYSCALL", # this is probably not correct for all platforms,
                 # but one can #define it to what one wants 
    "N_INLINE", "N_NOINLINE", "N_FASTCALL", "N_CLOSURE", "N_NOCONV"]
  CallingConvToStrLLVM: array[TCallingConvention, string] = ["fastcc $1", 
    "stdcall $1", "ccc $1", "safecall $1", "syscall $1", "$1 alwaysinline", 
    "$1 noinline", "fastcc $1", "ccc $1", "$1"]

proc CacheGetType(tab: TIdTable, key: PType): PRope = 
  # returns nil if we need to declare this type
  # since types are now unique via the ``GetUniqueType`` mechanism, this slow
  # linear search is not necessary anymore:
  result = PRope(IdTableGet(tab, key))

proc getTempName(): PRope = 
  result = ropeff("TMP$1", "%TMP$1", [toRope(getID())])

proc getGlobalTempName(): PRope = 
  result = ropeff("TMP$1", "@TMP$1", [toRope(getID())])

proc ccgIntroducedPtr(s: PSym): bool = 
  var pt = s.typ
  assert(not (sfResult in s.flags))
  case pt.Kind
  of tyObject: 
    # XXX quick hack floatSize*2 for the pegs module under 64bit
    if (optByRef in s.options) or (getSize(pt) > platform.floatSize * 2): 
      result = true           # requested anyway
    elif (tfFinal in pt.flags) and (pt.sons[0] == nil): 
      result = false          # no need, because no subtyping possible
    else: 
      result = true           # ordinary objects are always passed by reference,
                              # otherwise casting doesn't work
  of tyTuple: 
    result = (getSize(pt) > platform.floatSize) or (optByRef in s.options)
  else: result = false
  
proc fillResult(param: PSym) = 
  fillLoc(param.loc, locParam, param.typ, ropeff("Result", "%Result", []), 
          OnStack)
  if (mapReturnType(param.typ) != ctArray) and IsInvalidReturnType(param.typ): 
    incl(param.loc.flags, lfIndirect)
    param.loc.s = OnUnknown

proc genProcParams(m: BModule, t: PType, rettype, params: var PRope, 
                   check: var TIdSet) = 
  params = nil
  if (t.sons[0] == nil) or isInvalidReturnType(t.sons[0]): 
    rettype = toRope("void")
  else: 
    rettype = getTypeDescAux(m, t.sons[0], check)
  for i in countup(1, sonsLen(t.n) - 1): 
    if t.n.sons[i].kind != nkSym: InternalError(t.n.info, "genProcParams")
    var param = t.n.sons[i].sym
    fillLoc(param.loc, locParam, param.typ, mangleName(param), OnStack)
    app(params, getTypeDescAux(m, param.typ, check))
    if ccgIntroducedPtr(param): 
      app(params, "*")
      incl(param.loc.flags, lfIndirect)
      param.loc.s = OnUnknown
    app(params, " ")
    app(params, param.loc.r)  # declare the len field for open arrays:
    var arr = param.typ
    if arr.kind == tyVar: arr = arr.sons[0]
    var j = 0
    while arr.Kind == tyOpenArray: 
      # need to pass hidden parameter:
      appff(params, ", NI $1Len$2", ", @NI $1Len$2", [param.loc.r, toRope(j)])
      inc(j)
      arr = arr.sons[0]
    if i < sonsLen(t.n) - 1: app(params, ", ")
  if (t.sons[0] != nil) and isInvalidReturnType(t.sons[0]): 
    if params != nil: app(params, ", ")
    var arr = t.sons[0]
    app(params, getTypeDescAux(m, arr, check))
    if (mapReturnType(t.sons[0]) != ctArray) or (gCmd == cmdCompileToLLVM): 
      app(params, "*")
    appff(params, " Result", " @Result", [])
  if t.callConv == ccClosure: 
    if params != nil: app(params, ", ")
    app(params, "void* ClPart")
  if tfVarargs in t.flags: 
    if params != nil: app(params, ", ")
    app(params, "...")
  if (params == nil) and (gCmd != cmdCompileToLLVM): app(params, "void)")
  else: app(params, ")")
  params = con("(", params)

proc isImportedType(t: PType): bool = 
  result = (t.sym != nil) and (sfImportc in t.sym.flags)

proc typeNameOrLiteral(t: PType, literal: string): PRope = 
  if (t.sym != nil) and (sfImportc in t.sym.flags) and (t.sym.magic == mNone): 
    result = getTypeName(t)
  else: 
    result = toRope(literal)
  
proc getSimpleTypeDesc(m: BModule, typ: PType): PRope = 
  const 
    NumericalTypeToStr: array[tyInt..tyFloat128, string] = ["NI", "NI8", "NI16", 
      "NI32", "NI64", "NF", "NF32", "NF64", "NF128"]
  case typ.Kind
  of tyPointer: 
    result = typeNameOrLiteral(typ, "void*")
  of tyEnum: 
    if firstOrd(typ) < 0: 
      result = typeNameOrLiteral(typ, "NI32")
    else: 
      case int(getSize(typ))
      of 1: result = typeNameOrLiteral(typ, "NU8")
      of 2: result = typeNameOrLiteral(typ, "NU16")
      of 4: result = typeNameOrLiteral(typ, "NI32")
      of 8: result = typeNameOrLiteral(typ, "NI64")
      else: 
        internalError(typ.sym.info, "getSimpleTypeDesc: " & $(getSize(typ)))
        result = nil
  of tyString: 
    discard cgsym(m, "NimStringDesc")
    result = typeNameOrLiteral(typ, "NimStringDesc*")
  of tyCstring: result = typeNameOrLiteral(typ, "NCSTRING")
  of tyBool: result = typeNameOrLiteral(typ, "NIM_BOOL")
  of tyChar: result = typeNameOrLiteral(typ, "NIM_CHAR")
  of tyNil: result = typeNameOrLiteral(typ, "0")
  of tyInt..tyFloat128: 
    result = typeNameOrLiteral(typ, NumericalTypeToStr[typ.Kind])
  of tyRange: result = getSimpleTypeDesc(m, typ.sons[0])
  else: result = nil
  
proc getTypePre(m: BModule, typ: PType): PRope = 
  if typ == nil: result = toRope("void")
  else: 
    result = getSimpleTypeDesc(m, typ)
    if result == nil: result = CacheGetType(m.typeCache, typ)
  
proc getForwardStructFormat(): string = 
  result = "#ifndef _FSD_$1$n#define _FSD_$1$n"
  if gCmd == cmdCompileToCpp: result = result & "struct $1;$n"
  else: result = result & "typedef struct $1 $1;$n"
  result = result & "#endif$n"
  
proc getTypeForward(m: BModule, typ: PType): PRope = 
  result = CacheGetType(m.forwTypeCache, typ)
  if result != nil: return 
  result = getTypePre(m, typ)
  if result != nil: return 
  case typ.kind
  of tySequence, tyTuple, tyObject: 
    result = getTypeName(typ)
    if not isImportedType(typ): 
      appf(m.ts[ctfsForwardTypes], getForwardStructFormat(), [result])
    IdTablePut(m.forwTypeCache, typ, result)
  else: InternalError("getTypeForward(" & $typ.kind & ')')
  
proc mangleRecFieldName(field: PSym, rectype: PType): PRope = 
  if (rectype.sym != nil) and
      ({sfImportc, sfExportc} * rectype.sym.flags != {}): 
    result = field.loc.r
  else: 
    result = toRope(mangle(field.name.s))
  if result == nil: InternalError(field.info, "mangleRecFieldName")
  
proc genRecordFieldsAux(m: BModule, n: PNode, accessExpr: PRope, rectype: PType, 
                        check: var TIdSet): PRope = 
  var 
    ae, uname, sname, a: PRope
    k: PNode
    field: PSym
  result = nil
  case n.kind
  of nkRecList: 
    for i in countup(0, sonsLen(n) - 1): 
      app(result, genRecordFieldsAux(m, n.sons[i], accessExpr, rectype, check))
  of nkRecCase: 
    if (n.sons[0].kind != nkSym): InternalError(n.info, "genRecordFieldsAux")
    app(result, genRecordFieldsAux(m, n.sons[0], accessExpr, rectype, check))
    uname = toRope(mangle(n.sons[0].sym.name.s) & 'U')
    if accessExpr != nil: ae = ropef("$1.$2", [accessExpr, uname])
    else: ae = uname
    app(result, "union {" & tnl)
    for i in countup(1, sonsLen(n) - 1): 
      case n.sons[i].kind
      of nkOfBranch, nkElse: 
        k = lastSon(n.sons[i])
        if k.kind != nkSym: 
          sname = con("S", toRope(i))
          a = genRecordFieldsAux(m, k, ropef("$1.$2", [ae, sname]), rectype, 
                                 check)
          if a != nil: 
            app(result, "struct {")
            app(result, a)
            appf(result, "} $1;$n", [sname])
        else: 
          app(result, genRecordFieldsAux(m, k, ae, rectype, check))
      else: internalError("genRecordFieldsAux(record case branch)")
    appf(result, "} $1;$n", [uname])
  of nkSym: 
    field = n.sym
    assert(field.ast == nil)
    sname = mangleRecFieldName(field, rectype)
    if accessExpr != nil: ae = ropef("$1.$2", [accessExpr, sname])
    else: ae = sname
    fillLoc(field.loc, locField, field.typ, ae, OnUnknown)
    appf(result, "$1 $2;$n", [getTypeDescAux(m, field.loc.t, check), sname])
  else: internalError(n.info, "genRecordFieldsAux()")
  
proc getRecordFields(m: BModule, typ: PType, check: var TIdSet): PRope = 
  result = genRecordFieldsAux(m, typ.n, nil, typ, check)

proc getRecordDesc(m: BModule, typ: PType, name: PRope, 
                   check: var TIdSet): PRope = 
  # declare the record:
  var hasField = false
  if typ.kind == tyObject: 
    if typ.sons[0] == nil: 
      if typ.sym != nil and sfPure in typ.sym.flags or tfFinal in typ.flags: 
        result = ropecg(m, "struct $1 {$n", [name])
      else: 
        result = ropecg(m, "struct $1 {$n#TNimType* m_type;$n", [name])
        hasField = true
    elif gCmd == cmdCompileToCpp: 
      result = ropecg(m, "struct $1 : public $2 {$n", 
                      [name, getTypeDescAux(m, typ.sons[0], check)])
      hasField = true
    else: 
      result = ropecg(m, "struct $1 {$n  $2 Sup;$n", 
                      [name, getTypeDescAux(m, typ.sons[0], check)])
      hasField = true
  else: 
    result = ropef("struct $1 {$n", [name])
  var desc = getRecordFields(m, typ, check)
  if (desc == nil) and not hasField: 
    appf(result, "char dummy;$n", [])
  else: 
    app(result, desc)
  app(result, "};" & tnl)

proc getTupleDesc(m: BModule, typ: PType, name: PRope, 
                  check: var TIdSet): PRope = 
  result = ropef("struct $1 {$n", [name])
  var desc: PRope = nil
  for i in countup(0, sonsLen(typ) - 1): 
    appf(desc, "$1 Field$2;$n", 
         [getTypeDescAux(m, typ.sons[i], check), toRope(i)])
  if (desc == nil): app(result, "char dummy;" & tnl)
  else: app(result, desc)
  app(result, "};" & tnl)

proc pushType(m: BModule, typ: PType) = 
  add(m.typeStack, typ)

proc getTypeDescAux(m: BModule, typ: PType, check: var TIdSet): PRope = 
  # returns only the type's name
  var 
    name, rettype, desc, recdesc: PRope
    n: biggestInt
    t, et: PType
  t = getUniqueType(typ)
  if t == nil: InternalError("getTypeDescAux: t == nil")
  if t.sym != nil: useHeader(m, t.sym)
  result = getTypePre(m, t)
  if result != nil: return 
  if IdSetContainsOrIncl(check, t.id): 
    InternalError("cannot generate C type for: " & typeToString(typ)) 
    # XXX: this BUG is hard to fix -> we need to introduce helper structs,
    # but determining when this needs to be done is hard. We should split
    # C type generation into an analysis and a code generation phase somehow.
  case t.Kind
  of tyRef, tyPtr, tyVar: 
    et = getUniqueType(t.sons[0])
    if et.kind in {tyArrayConstr, tyArray, tyOpenArray}: 
      et = getUniqueType(elemType(et))
    case et.kind
    of tyObject, tyTuple: 
      # no restriction! We have a forward declaration for structs
      name = getTypeForward(m, et)
      result = con(name, "*")
      IdTablePut(m.typeCache, t, result)
      pushType(m, et)
    of tySequence: 
      # no restriction! We have a forward declaration for structs
      name = getTypeForward(m, et)
      result = con(name, "**")
      IdTablePut(m.typeCache, t, result)
      pushType(m, et)
    else: 
      # else we have a strong dependency  :-(
      result = con(getTypeDescAux(m, et, check), "*")
      IdTablePut(m.typeCache, t, result)
  of tyOpenArray: 
    et = getUniqueType(t.sons[0])
    result = con(getTypeDescAux(m, et, check), "*")
    IdTablePut(m.typeCache, t, result)
  of tyProc: 
    result = getTypeName(t)
    IdTablePut(m.typeCache, t, result)
    genProcParams(m, t, rettype, desc, check)
    if not isImportedType(t): 
      appf(m.ts[ctfsTypes], "#ifndef _SD_$1$n#define _SD_$1$n", [result])
      if t.callConv != ccClosure: # procedure vars may need a closure!
        appf(m.ts[ctfsTypes], "typedef $1_PTR($2, $3) $4;$n", 
             [toRope(CallingConvToStr[t.callConv]), rettype, result, desc])
      else: 
        appf(m.ts[ctfsTypes], "typedef struct $1 {$n" &
            "N_CDECL_PTR($2, PrcPart) $3;$n" & "void* ClPart;$n};$n", 
             [result, rettype, desc])
      appf(m.ts[ctfsTypes], "#endif$n", [])
  of tySequence: 
    # we cannot use getTypeForward here because then t would be associated
    # with the name of the struct, not with the pointer to the struct:
    result = CacheGetType(m.forwTypeCache, t)
    if result == nil: 
      result = getTypeName(t)
      if not isImportedType(t): 
        appf(m.ts[ctfsForwardTypes], getForwardStructFormat(), [result])
      IdTablePut(m.forwTypeCache, t, result)
    assert(CacheGetType(m.typeCache, t) == nil)
    IdTablePut(m.typeCache, t, con(result, "*"))
    if not isImportedType(t): 
      if skipTypes(t.sons[0], abstractInst).kind != tyEmpty: 
        appf(m.ts[ctfsSeqTypes], "#ifndef _SD_$1$n#define _SD_$1$n", [result])
        appcg(m, m.ts[ctfsSeqTypes], 
            "struct $2 {$n" & 
            "  #TGenericSeq Sup;$n" &
            "  $1 data[SEQ_DECL_SIZE];$n" & 
            "};$n", [getTypeDescAux(m, t.sons[0], check), result])
        appf(m.ts[ctfsSeqTypes], "#endif$n", [])
      else: 
        result = toRope("TGenericSeq")
    app(result, "*")
  of tyArrayConstr, tyArray: 
    n = lengthOrd(t)
    if n <= 0: 
      n = 1                   # make an array of at least one element
    result = getTypeName(t)
    IdTablePut(m.typeCache, t, result)
    if not isImportedType(t): 
      appf(m.ts[ctfsTypes], "#ifndef _SD_$1$n#define _SD_$1$n", [result])
      appf(m.ts[ctfsTypes], "typedef $1 $2[$3];$n", 
           [getTypeDescAux(m, t.sons[1], check), result, ToRope(n)])
      appf(m.ts[ctfsTypes], "#endif$n", [])
  of tyObject, tyTuple: 
    result = CacheGetType(m.forwTypeCache, t)
    if result == nil: 
      result = getTypeName(t)
      if not isImportedType(t): 
        appf(m.ts[ctfsForwardTypes], getForwardStructFormat(), [result])
      IdTablePut(m.forwTypeCache, t, result)
    IdTablePut(m.typeCache, t, result) # always call for sideeffects:
    if t.n != nil: recdesc = getRecordDesc(m, t, result, check)
    else: recdesc = getTupleDesc(m, t, result, check)
    if not isImportedType(t):
      appf(m.ts[ctfsTypes], "#ifndef _SD_$1$n#define _SD_$1$n", [result])
      app(m.ts[ctfsTypes], recdesc)
      appf(m.ts[ctfsTypes], "#endif$n", [])
  of tySet: 
    case int(getSize(t))
    of 1: result = toRope("NU8")
    of 2: result = toRope("NU16")
    of 4: result = toRope("NU32")
    of 8: result = toRope("NU64")
    else: 
      result = getTypeName(t)
      IdTablePut(m.typeCache, t, result)
      if not isImportedType(t): 
        appf(m.ts[ctfsTypes], "#ifndef _SD_$1$n#define _SD_$1$n", [result])
        appf(m.ts[ctfsTypes], "typedef NU8 $1[$2];$n", 
             [result, toRope(getSize(t))])
        appf(m.ts[ctfsTypes], "#endif$n", [])
  of tyGenericInst, tyDistinct, tyOrdinal: 
    result = getTypeDescAux(m, lastSon(t), check)
  else: 
    InternalError("getTypeDescAux(" & $t.kind & ')')
    result = nil

proc getTypeDesc(m: BModule, typ: PType): PRope = 
  var check: TIdSet
  IdSetInit(check)
  result = getTypeDescAux(m, typ, check)

proc getTypeDesc(m: BModule, magic: string): PRope = 
  var sym = magicsys.getCompilerProc(magic)
  if sym != nil: 
    result = getTypeDesc(m, sym.typ)
  else: 
    rawMessage(errSystemNeeds, magic)
    result = nil

proc finishTypeDescriptions(m: BModule) = 
  var i = 0
  while i < len(m.typeStack): 
    discard getTypeDesc(m, m.typeStack[i])
    inc(i)

proc genProcHeader(m: BModule, prc: PSym): PRope = 
  var 
    rettype, params: PRope
    check: TIdSet
  # using static is needed for inline procs
  if (prc.typ.callConv == ccInline): result = toRope("static ")
  else: result = nil
  IdSetInit(check)
  fillLoc(prc.loc, locProc, prc.typ, mangleName(prc), OnUnknown)
  genProcParams(m, prc.typ, rettype, params, check)
  appf(result, "$1($2, $3)$4", 
       [toRope(CallingConvToStr[prc.typ.callConv]), rettype, prc.loc.r, params])

proc genTypeInfo(m: BModule, typ: PType): PRope
proc getNimNode(m: BModule): PRope = 
  result = ropef("$1[$2]", [m.typeNodesName, toRope(m.typeNodes)])
  inc(m.typeNodes)

proc getNimType(m: BModule): PRope = 
  result = ropef("$1[$2]", [m.nimTypesName, toRope(m.nimTypes)])
  inc(m.nimTypes)

proc allocMemTI(m: BModule, typ: PType, name: PRope) = 
  var tmp = getNimType(m)
  appf(m.ts[ctfsTypeInit2], "$2 = &$1;$n", [tmp, name])

proc genTypeInfoAuxBase(m: BModule, typ: PType, name, base: PRope) = 
  var nimtypeKind: int
  allocMemTI(m, typ, name)
  if (typ.kind == tyObject) and (tfFinal in typ.flags) and
      (typ.sons[0] == nil): 
    nimtypeKind = ord(high(TTypeKind)) + 1 # tyPureObject
  else:
    nimtypeKind = ord(typ.kind)
  appf(m.ts[ctfsTypeInit3], 
       "$1->size = sizeof($2);$n" & "$1->kind = $3;$n" & "$1->base = $4;$n", 
       [name, getTypeDesc(m, typ), toRope(nimtypeKind), base])     
  # compute type flags for GC optimization
  var flags = 0
  if not containsGarbageCollectedRef(typ): flags = flags or 1
  if not canFormAcycle(typ): flags = flags or 2        
  #else MessageOut("can contain a cycle: " & typeToString(typ))
  if flags != 0: 
    appf(m.ts[ctfsTypeInit3], "$1->flags = $2;$n", [name, toRope(flags)])
  appf(m.ts[ctfsVars], "TNimType* $1; /* $2 */$n", 
       [name, toRope(typeToString(typ))])

proc genTypeInfoAux(m: BModule, typ: PType, name: PRope) = 
  var base: PRope
  if (sonsLen(typ) > 0) and (typ.sons[0] != nil): 
    base = genTypeInfo(m, typ.sons[0])
  else: 
    base = toRope("0")
  genTypeInfoAuxBase(m, typ, name, base)

proc genObjectFields(m: BModule, typ: PType, n: PNode, expr: PRope) = 
  var 
    tmp, tmp2: PRope
    length, x, y: int
    field: PSym
    b: PNode
  case n.kind
  of nkRecList: 
    length = sonsLen(n)
    if length == 1: 
      genObjectFields(m, typ, n.sons[0], expr)
    elif length > 0: 
      tmp = getTempName()
      appf(m.ts[ctfsTypeInit1], "static TNimNode* $1[$2];$n", 
           [tmp, toRope(length)])
      for i in countup(0, length - 1): 
        tmp2 = getNimNode(m)
        appf(m.ts[ctfsTypeInit3], "$1[$2] = &$3;$n", [tmp, toRope(i), tmp2])
        genObjectFields(m, typ, n.sons[i], tmp2)
      appf(m.ts[ctfsTypeInit3], "$1.len = $2; $1.kind = 2; $1.sons = &$3[0];$n", 
           [expr, toRope(length), tmp])
    else: 
      appf(m.ts[ctfsTypeInit3], "$1.len = $2; $1.kind = 2;$n", 
           [expr, toRope(length)])
  of nkRecCase: 
    length = sonsLen(n)
    assert(n.sons[0].kind == nkSym)
    field = n.sons[0].sym
    tmp = getTempName()
    appf(m.ts[ctfsTypeInit3], "$1.kind = 3;$n" &
        "$1.offset = offsetof($2, $3);$n" & "$1.typ = $4;$n" &
        "$1.name = $5;$n" & "$1.sons = &$6[0];$n" &
        "$1.len = $7;$n", [expr, getTypeDesc(m, typ), field.loc.r, 
                           genTypeInfo(m, field.typ), makeCString(field.name.s), 
                           tmp, toRope(lengthOrd(field.typ))])
    appf(m.ts[ctfsTypeInit1], "static TNimNode* $1[$2];$n", 
         [tmp, toRope(lengthOrd(field.typ) + 1)])
    for i in countup(1, length - 1): 
      b = n.sons[i]           # branch
      tmp2 = getNimNode(m)
      genObjectFields(m, typ, lastSon(b), tmp2)
      case b.kind
      of nkOfBranch: 
        if sonsLen(b) < 2: 
          internalError(b.info, "genObjectFields; nkOfBranch broken")
        for j in countup(0, sonsLen(b) - 2): 
          if b.sons[j].kind == nkRange: 
            x = int(getOrdValue(b.sons[j].sons[0]))
            y = int(getOrdValue(b.sons[j].sons[1]))
            while x <= y: 
              appf(m.ts[ctfsTypeInit3], "$1[$2] = &$3;$n", [tmp, toRope(x), tmp2])
              inc(x)
          else: 
            appf(m.ts[ctfsTypeInit3], "$1[$2] = &$3;$n", 
                 [tmp, toRope(getOrdValue(b.sons[j])), tmp2])
      of nkElse: 
        appf(m.ts[ctfsTypeInit3], "$1[$2] = &$3;$n", 
             [tmp, toRope(lengthOrd(field.typ)), tmp2])
      else: internalError(n.info, "genObjectFields(nkRecCase)")
  of nkSym: 
    field = n.sym
    appf(m.ts[ctfsTypeInit3], "$1.kind = 1;$n" &
        "$1.offset = offsetof($2, $3);$n" & "$1.typ = $4;$n" &
        "$1.name = $5;$n", [expr, getTypeDesc(m, typ), 
        field.loc.r, genTypeInfo(m, field.typ), makeCString(field.name.s)])
  else: internalError(n.info, "genObjectFields")
  
proc genObjectInfo(m: BModule, typ: PType, name: PRope) = 
  var tmp: PRope
  if typ.kind == tyObject: genTypeInfoAux(m, typ, name)
  else: genTypeInfoAuxBase(m, typ, name, toRope("0"))
  tmp = getNimNode(m)
  genObjectFields(m, typ, typ.n, tmp)
  appf(m.ts[ctfsTypeInit3], "$1->node = &$2;$n", [name, tmp])

proc genTupleInfo(m: BModule, typ: PType, name: PRope) = 
  var 
    tmp, expr, tmp2: PRope
    length: int
    a: PType
  genTypeInfoAuxBase(m, typ, name, toRope("0"))
  expr = getNimNode(m)
  length = sonsLen(typ)
  if length > 0: 
    tmp = getTempName()
    appf(m.ts[ctfsTypeInit1], "static TNimNode* $1[$2];$n", [tmp, toRope(length)])
    for i in countup(0, length - 1): 
      a = typ.sons[i]
      tmp2 = getNimNode(m)
      appf(m.ts[ctfsTypeInit3], "$1[$2] = &$3;$n", [tmp, toRope(i), tmp2])
      appf(m.ts[ctfsTypeInit3], "$1.kind = 1;$n" &
          "$1.offset = offsetof($2, Field$3);$n" & "$1.typ = $4;$n" &
          "$1.name = \"Field$3\";$n", 
           [tmp2, getTypeDesc(m, typ), toRope(i), genTypeInfo(m, a)])
    appf(m.ts[ctfsTypeInit3], "$1.len = $2; $1.kind = 2; $1.sons = &$3[0];$n", 
         [expr, toRope(length), tmp])
  else: 
    appf(m.ts[ctfsTypeInit3], "$1.len = $2; $1.kind = 2;$n", 
         [expr, toRope(length)])
  appf(m.ts[ctfsTypeInit3], "$1->node = &$2;$n", [name, tmp])

proc genEnumInfo(m: BModule, typ: PType, name: PRope) = 
  var 
    nodePtrs, elemNode, enumNames, enumArray, counter, specialCases: PRope
    length, firstNimNode: int
    field: PSym
  # Type information for enumerations is quite heavy, so we do some
  # optimizations here: The ``typ`` field is never set, as it is redundant
  # anyway. We generate a cstring array and a loop over it. Exceptional
  # positions will be reset after the loop.
  genTypeInfoAux(m, typ, name)
  nodePtrs = getTempName()
  length = sonsLen(typ.n)
  appf(m.ts[ctfsTypeInit1], "static TNimNode* $1[$2];$n", 
       [nodePtrs, toRope(length)])
  enumNames = nil
  specialCases = nil
  firstNimNode = m.typeNodes
  for i in countup(0, length - 1): 
    assert(typ.n.sons[i].kind == nkSym)
    field = typ.n.sons[i].sym
    elemNode = getNimNode(m)
    app(enumNames, makeCString(field.name.s))
    if i < length - 1: app(enumNames, ", " & tnl)
    if field.position != i: 
      appf(specialCases, "$1.offset = $2;$n", [elemNode, toRope(field.position)])
  enumArray = getTempName()
  counter = getTempName()
  appf(m.ts[ctfsTypeInit1], "NI $1;$n", [counter])
  appf(m.ts[ctfsTypeInit1], "static char* NIM_CONST $1[$2] = {$n$3};$n", 
       [enumArray, toRope(length), enumNames])
  appf(m.ts[ctfsTypeInit3], "for ($1 = 0; $1 < $2; $1++) {$n" &
      "$3[$1+$4].kind = 1;$n" & "$3[$1+$4].offset = $1;$n" &
      "$3[$1+$4].name = $5[$1];$n" & "$6[$1] = &$3[$1+$4];$n" & "}$n", [counter, 
      toRope(length), m.typeNodesName, toRope(firstNimNode), enumArray, nodePtrs])
  app(m.ts[ctfsTypeInit3], specialCases)
  appf(m.ts[ctfsTypeInit3], 
       "$1.len = $2; $1.kind = 2; $1.sons = &$3[0];$n$4->node = &$1;$n", 
       [getNimNode(m), toRope(length), nodePtrs, name])

proc genSetInfo(m: BModule, typ: PType, name: PRope) = 
  assert(typ.sons[0] != nil)
  genTypeInfoAux(m, typ, name)
  var tmp = getNimNode(m)
  appf(m.ts[ctfsTypeInit3], "$1.len = $2; $1.kind = 0;$n" & "$3->node = &$1;$n", 
       [tmp, toRope(firstOrd(typ)), name])

proc genArrayInfo(m: BModule, typ: PType, name: PRope) = 
  genTypeInfoAuxBase(m, typ, name, genTypeInfo(m, typ.sons[1]))

var
  gToTypeInfoId: TXYTable[TId, TId] # ?safe?

proc genTypeInfo(m: BModule, typ: PType): PRope = 
  var dataGenerated: bool
  var t = getUniqueType(typ)
  var id = XYTableGet(gToTypeInfoId, t.id)
  if id == InvalidKeyTId:
    dataGenerated = false
    id = t.id                 # getID();
    XYTablePut(gToTypeInfoId, t.id, id)
  else: 
    dataGenerated = true
  result = ropef("NTI$1", [toRope(id)])
  if not IdSetContainsOrIncl(m.typeInfoMarker, id): 
    # declare type information structures:
    discard cgsym(m, "TNimType")
    discard cgsym(m, "TNimNode")
    appf(m.ts[ctfsVars], "extern TNimType* $1; /* $2 */$n", 
         [result, toRope(typeToString(t))])
  if dataGenerated: return 
  case t.kind
  of tyEmpty: 
    result = toRope("0")
  of tyPointer, tyProc, tyBool, tyChar, tyCString, tyString, tyInt..tyFloat128, 
     tyVar: 
    genTypeInfoAuxBase(m, t, result, toRope("0"))
  of tyRef, tyPtr, tySequence, tyRange: 
    genTypeInfoAux(m, t, result)
  of tyArrayConstr, tyArray: 
    genArrayInfo(m, t, result)
  of tySet: 
    genSetInfo(m, t, result)
  of tyEnum: 
    genEnumInfo(m, t, result)
  of tyObject: 
    genObjectInfo(m, t, result)
  of tyTuple: 
    if t.n != nil: genObjectInfo(m, t, result)
    else: genTupleInfo(m, t, result)
  else: InternalError("genTypeInfo(" & $t.kind & ')')
  
proc genTypeSection(m: BModule, n: PNode) = 
  nil
