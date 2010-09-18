#
#
#            Nimrod's Runtime Library
#        (c) Copyright 2010 Andreas Rumpf
#
#    See the file "copying.txt", included in this
#    distribution, for details about the copyright.
#


#            Garbage Collector
#
# The basic algorithm is *Deferrent Reference Counting* with cycle detection.
# Special care has been taken to avoid recursion as far as possible to avoid
# stack overflows when traversing deep datastructures. This is comparable to
# an incremental and generational GC. It should be well-suited for soft real
# time applications (like games).
#
# Future Improvements:
# * Support for multi-threading. However, locks for the reference counting
#   might turn out to be too slow.

const
  CycleIncrease = 2 # is a multiplicative increase
  InitialCycleThreshold = 4*1024*1024 # X MB because cycle checking is slow
  ZctThreshold = 256  # we collect garbage if the ZCT's size
                      # reaches this threshold
                      # this seems to be a good value

const
  rcIncrement = 0b1000 # so that lowest 3 bits are not touched
  # NOTE: Most colors are currently unused
  rcBlack = 0b000  # cell is colored black; in use or free
  rcGray = 0b001   # possible member of a cycle
  rcWhite = 0b010  # member of a garbage cycle
  rcPurple = 0b011 # possible root of a cycle
  rcZct = 0b100    # in ZCT
  rcRed = 0b101    # Candidate cycle undergoing sigma-computation
  rcOrange = 0b110 # Candidate cycle awaiting epoch boundary
  rcShift = 3      # shift by rcShift to get the reference counter
  colorMask = 0b111
type
  TWalkOp = enum
    waZctDecRef, waPush, waCycleDecRef

  TFinalizer {.compilerproc.} = proc (self: pointer)
    # A ref type can have a finalizer that is called before the object's
    # storage is freed.

  TGcStat {.final, pure.} = object
    stackScans: int          # number of performed stack scans (for statistics)
    cycleCollections: int    # number of performed full collections
    maxThreshold: int        # max threshold that has been set
    maxStackSize: int        # max stack size
    maxStackCells: int       # max stack cells in ``decStack``
    cycleTableSize: int      # max entries in cycle table  
  
  TGcHeap {.final, pure.} = object # this contains the zero count and
                                   # non-zero count table
    zct: TCellSeq            # the zero count table
    decStack: TCellSeq       # cells in the stack that are to decref again
    cycleRoots: TCellSet
    tempStack: TCellSeq      # temporary stack for recursion elimination
    cycleRootsLock: TSysLock
    zctLock: TSysLock
    stat: TGcStat

var
  stackBottom: pointer
  gch: TGcHeap
  cycleThreshold: int = InitialCycleThreshold
  recGcLock: int = 0
    # we use a lock to prevent the garbage collector to be triggered in a
    # finalizer; the collector should not call itself this way! Thus every
    # object allocated by a finalizer will not trigger a garbage collection.
    # This is wasteful but safe. This is a lock against recursive garbage
    # collection, not a lock for threads!

proc lock(gch: var TGcHeap) {.inline.} = 
  if isMultiThreaded: 
    Lock(gch.zctLock)
    lock(gch.cycleRootsLock)

proc unlock(gch: var TGcHeap) {.inline.} = 
  if isMultiThreaded: 
    unlock(gch.zctLock)
    unlock(gch.cycleRootsLock)

proc addZCT(s: var TCellSeq, c: PCell) {.noinline.} =
  if (c.refcount and rcZct) == 0:
    c.refcount = c.refcount and not colorMask or rcZct
    add(s, c)

proc cellToUsr(cell: PCell): pointer {.inline.} =
  # convert object (=pointer to refcount) to pointer to userdata
  result = cast[pointer](cast[TAddress](cell)+%TAddress(sizeof(TCell)))

proc usrToCell(usr: pointer): PCell {.inline.} =
  # convert pointer to userdata to object (=pointer to refcount)
  result = cast[PCell](cast[TAddress](usr)-%TAddress(sizeof(TCell)))

proc canbeCycleRoot(c: PCell): bool {.inline.} =
  result = ntfAcyclic notin c.typ.flags

proc extGetCellType(c: pointer): PNimType {.compilerproc.} =
  # used for code generation concerning debugging
  result = usrToCell(c).typ

proc internRefcount(p: pointer): int {.exportc: "getRefcount".} =
  result = int(usrToCell(p).refcount) shr rcShift

# this that has to equals zero, otherwise we have to round up UnitsPerPage:
when BitsPerPage mod (sizeof(int)*8) != 0:
  {.error: "(BitsPerPage mod BitsPerUnit) should be zero!".}

when debugGC:
  proc writeCell(msg: CString, c: PCell) =
    var kind = -1
    if c.typ != nil: kind = ord(c.typ.kind)
    when debugGC:
      c_fprintf(c_stdout, "[GC] %s: %p %d rc=%ld from %s(%ld)\n",
                msg, c, kind, c.refcount shr rcShift, c.filename, c.line)
    else:
      c_fprintf(c_stdout, "[GC] %s: %p %d rc=%ld\n",
                msg, c, kind, c.refcount shr rcShift)

when traceGC:
  # traceGC is a special switch to enable extensive debugging
  type
    TCellState = enum
      csAllocated, csZctFreed, csCycFreed
  var
    states: array[TCellState, TCellSet]

  proc traceCell(c: PCell, state: TCellState) =
    case state
    of csAllocated:
      if c in states[csAllocated]:
        writeCell("attempt to alloc an already allocated cell", c)
        assert(false)
      excl(states[csCycFreed], c)
      excl(states[csZctFreed], c)
    of csZctFreed:
      if c in states[csZctFreed]:
        writeCell("attempt to free zct cell twice", c)
        assert(false)
      if c in states[csCycFreed]:
        writeCell("attempt to free with zct, but already freed with cyc", c)
        assert(false)
      if c notin states[csAllocated]:
        writeCell("attempt to free not an allocated cell", c)
        assert(false)
      excl(states[csAllocated], c)
    of csCycFreed:
      if c notin states[csAllocated]:
        writeCell("attempt to free a not allocated cell", c)
        assert(false)
      if c in states[csCycFreed]:
        writeCell("attempt to free cyc cell twice", c)
        assert(false)
      if c in states[csZctFreed]:
        writeCell("attempt to free with cyc, but already freed with zct", c)
        assert(false)
      excl(states[csAllocated], c)
    incl(states[state], c)

  proc writeLeakage() =
    var z = 0
    var y = 0
    var e = 0
    for c in elements(states[csAllocated]):
      inc(e)
      if c in states[csZctFreed]: inc(z)
      elif c in states[csCycFreed]: inc(y)
      else: writeCell("leak", c)
    cfprintf(cstdout, "Allocations: %ld; ZCT freed: %ld; CYC freed: %ld\n",
             e, z, y)

template gcTrace(cell, state: expr): stmt =
  when traceGC: traceCell(cell, state)

# -----------------------------------------------------------------------------

# forward declarations:
proc collectCT(gch: var TGcHeap)
proc IsOnStack(p: pointer): bool {.noinline.}
proc forAllChildren(cell: PCell, op: TWalkOp)
proc doOperation(p: pointer, op: TWalkOp)
proc forAllChildrenAux(dest: Pointer, mt: PNimType, op: TWalkOp)
# we need the prototype here for debugging purposes

proc prepareDealloc(cell: PCell) =
  if cell.typ.finalizer != nil:
    # the finalizer could invoke something that
    # allocates memory; this could trigger a garbage
    # collection. Since we are already collecting we
    # prevend recursive entering here by a lock.
    # XXX: we should set the cell's children to nil!
    inc(recGcLock)
    (cast[TFinalizer](cell.typ.finalizer))(cellToUsr(cell))
    dec(recGcLock)

proc rtlAddCycleRoot(c: PCell) {.rtl, inl.} = 
  # we MUST access gch as a global here, because this crosses DLL boundaries!
  if isMultiThreaded: Lock(gch.cycleRootsLock)
  incl(gch.cycleRoots, c)
  if isMultiThreaded: Unlock(gch.cycleRootsLock)

proc rtlAddZCT(c: PCell) {.rtl, inl.} =
  # we MUST access gch as a global here, because this crosses DLL boundaries!
  if isMultiThreaded: Lock(gch.zctLock)
  addZCT(gch.zct, c)
  if isMultiThreaded: Unlock(gch.zctLock)

proc decRef(c: PCell) {.inline.} =
  when stressGC:
    if c.refcount <% rcIncrement:
      writeCell("broken cell", c)
  assert(c.refcount >=% rcIncrement)
  if atomicDec(c.refcount, rcIncrement) <% rcIncrement:
    rtlAddZCT(c)
  elif canBeCycleRoot(c):
    rtlAddCycleRoot(c) 

proc incRef(c: PCell) {.inline.} = 
  discard atomicInc(c.refcount, rcIncrement)
  if canBeCycleRoot(c):
    rtlAddCycleRoot(c)

proc nimGCref(p: pointer) {.compilerProc, inline.} = incRef(usrToCell(p))
proc nimGCunref(p: pointer) {.compilerProc, inline.} = decRef(usrToCell(p))

proc asgnRef(dest: ppointer, src: pointer) {.compilerProc, inline.} =
  # the code generator calls this proc!
  assert(not isOnStack(dest))
  # BUGFIX: first incRef then decRef!
  if src != nil: incRef(usrToCell(src))
  if dest^ != nil: decRef(usrToCell(dest^))
  dest^ = src

proc asgnRefNoCycle(dest: ppointer, src: pointer) {.compilerProc, inline.} =
  # the code generator calls this proc if it is known at compile time that no 
  # cycle is possible.
  if src != nil: 
    var c = usrToCell(src)
    discard atomicInc(c.refcount, rcIncrement)
  if dest^ != nil: 
    var c = usrToCell(dest^)
    if atomicDec(c.refcount, rcIncrement) <% rcIncrement:
      rtlAddZCT(c)
  dest^ = src

proc unsureAsgnRef(dest: ppointer, src: pointer) {.compilerProc.} =
  # unsureAsgnRef updates the reference counters only if dest is not on the
  # stack. It is used by the code generator if it cannot decide wether a
  # reference is in the stack or not (this can happen for var parameters).
  if not IsOnStack(dest):
    if src != nil: incRef(usrToCell(src))
    if dest^ != nil: decRef(usrToCell(dest^))
  dest^ = src

proc initGC() =
  when not defined(useNimRtl):
    when traceGC:
      for i in low(TCellState)..high(TCellState): Init(states[i])
    gch.stat.stackScans = 0
    gch.stat.cycleCollections = 0
    gch.stat.maxThreshold = 0
    gch.stat.maxStackSize = 0
    gch.stat.maxStackCells = 0
    gch.stat.cycleTableSize = 0
    # init the rt
    init(gch.zct)
    init(gch.tempStack)
    Init(gch.cycleRoots)
    Init(gch.decStack)
    InitLock(gch.cycleRootsLock)
    InitLock(gch.zctLock)
    new(gOutOfMem) # reserve space for the EOutOfMemory exception here!

proc forAllSlotsAux(dest: pointer, n: ptr TNimNode, op: TWalkOp) =
  var d = cast[TAddress](dest)
  case n.kind
  of nkNone: assert(false)
  of nkSlot: forAllChildrenAux(cast[pointer](d +% n.offset), n.typ, op)
  of nkList:
    for i in 0..n.len-1: forAllSlotsAux(dest, n.sons[i], op)
  of nkCase:
    var m = selectBranch(dest, n)
    if m != nil: forAllSlotsAux(dest, m, op)

proc forAllChildrenAux(dest: Pointer, mt: PNimType, op: TWalkOp) =
  var d = cast[TAddress](dest)
  if dest == nil: return # nothing to do
  if ntfNoRefs notin mt.flags:
    case mt.Kind
    of tyArray, tyArrayConstr, tyOpenArray:
      for i in 0..(mt.size div mt.base.size)-1:
        forAllChildrenAux(cast[pointer](d +% i *% mt.base.size), mt.base, op)
    of tyRef, tyString, tySequence: # leaf:
      doOperation(cast[ppointer](d)^, op)
    of tyObject, tyTuple, tyPureObject:
      forAllSlotsAux(dest, mt.node, op)
    else: nil

proc forAllChildren(cell: PCell, op: TWalkOp) =
  assert(cell != nil)
  assert(cell.typ != nil)
  case cell.typ.Kind
  of tyRef: # common case
    forAllChildrenAux(cellToUsr(cell), cell.typ.base, op)
  of tySequence:
    var d = cast[TAddress](cellToUsr(cell))
    var s = cast[PGenericSeq](d)
    if s != nil:
      for i in 0..s.len-1:
        forAllChildrenAux(cast[pointer](d +% i *% cell.typ.base.size +%
          GenericSeqSize), cell.typ.base, op)
  of tyString: nil
  else: assert(false)

proc checkCollection {.inline.} =
  # checks if a collection should be done
  if recGcLock == 0:
    collectCT(gch)

proc newObj(typ: PNimType, size: int): pointer {.compilerRtl.} =
  # generates a new object and sets its reference counter to 0
  lock(gch)
  assert(typ.kind in {tyRef, tyString, tySequence})
  checkCollection()
  var res = cast[PCell](rawAlloc(allocator, size + sizeof(TCell)))
  zeroMem(res, size+sizeof(TCell))
  assert((cast[TAddress](res) and (MemAlign-1)) == 0)
  # now it is buffered in the ZCT
  res.typ = typ
  when debugGC:
    if framePtr != nil and framePtr.prev != nil:
      res.filename = framePtr.prev.filename
      res.line = framePtr.prev.line
  res.refcount = rcZct # refcount is zero, but mark it to be in the ZCT  
  assert(isAllocatedPtr(allocator, res))
  # its refcount is zero, so add it to the ZCT:
  block addToZCT: 
    # we check the last 8 entries (cache line) for a slot
    # that could be reused
    var L = gch.zct.len
    var d = gch.zct.d
    for i in countdown(L-1, max(0, L-8)):
      var c = d[i]
      if c.refcount >=% rcIncrement:
        c.refcount = c.refcount and not colorMask
        d[i] = res
        break addToZCT
    add(gch.zct, res)
  when logGC: writeCell("new cell", res)
  gcTrace(res, csAllocated)  
  unlock(gch)
  result = cellToUsr(res)

proc newSeq(typ: PNimType, len: int): pointer {.compilerRtl.} =
  # `newObj` already uses locks, so no need for them here.
  result = newObj(typ, addInt(mulInt(len, typ.base.size), GenericSeqSize))
  cast[PGenericSeq](result).len = len
  cast[PGenericSeq](result).space = len

proc growObj(old: pointer, newsize: int): pointer {.rtl.} =
  lock(gch)
  checkCollection()
  var ol = usrToCell(old)
  assert(ol.typ != nil)
  assert(ol.typ.kind in {tyString, tySequence})
  var res = cast[PCell](rawAlloc(allocator, newsize + sizeof(TCell)))
  var elemSize = 1
  if ol.typ.kind != tyString:
    elemSize = ol.typ.base.size
  
  var oldsize = cast[PGenericSeq](old).len*elemSize + GenericSeqSize
  copyMem(res, ol, oldsize + sizeof(TCell))
  zeroMem(cast[pointer](cast[TAddress](res)+% oldsize +% sizeof(TCell)),
          newsize-oldsize)
  assert((cast[TAddress](res) and (MemAlign-1)) == 0)
  assert(res.refcount shr rcShift <=% 1)
  #if res.refcount <% rcIncrement:
  #  add(gch.zct, res)
  #else: # XXX: what to do here?
  #  decRef(ol)
  if (ol.refcount and colorMask) == rcZct:
    var j = gch.zct.len-1
    var d = gch.zct.d
    while j >= 0: 
      if d[j] == ol:
        d[j] = res
        break
      dec(j)
  if canBeCycleRoot(ol): excl(gch.cycleRoots, ol)
  when logGC:
    writeCell("growObj old cell", ol)
    writeCell("growObj new cell", res)
  gcTrace(ol, csZctFreed)
  gcTrace(res, csAllocated)
  when reallyDealloc: rawDealloc(allocator, ol)
  else:
    assert(ol.typ != nil)
    zeroMem(ol, sizeof(TCell))
  unlock(gch)
  result = cellToUsr(res)

# ---------------- cycle collector -------------------------------------------

proc doOperation(p: pointer, op: TWalkOp) =
  if p == nil: return
  var c: PCell = usrToCell(p)
  assert(c != nil)
  case op # faster than function pointers because of easy prediction
  of waZctDecRef:
    assert(c.refcount >=% rcIncrement)
    c.refcount = c.refcount -% rcIncrement
    when logGC: writeCell("decref (from doOperation)", c)
    if c.refcount <% rcIncrement: addZCT(gch.zct, c)
  of waPush:
    add(gch.tempStack, c)
  of waCycleDecRef:
    assert(c.refcount >=% rcIncrement)
    c.refcount = c.refcount -% rcIncrement

# we now use a much simpler and non-recursive algorithm for cycle removal
proc collectCycles(gch: var TGcHeap) =
  var tabSize = 0
  for c in elements(gch.cycleRoots):
    inc(tabSize)
    forallChildren(c, waCycleDecRef)
  gch.stat.cycleTableSize = max(gch.stat.cycleTableSize, tabSize)

  # restore reference counts (a depth-first traversal is needed):
  var marker: TCellSet
  Init(marker)
  for c in elements(gch.cycleRoots):
    if c.refcount >=% rcIncrement:
      if not containsOrIncl(marker, c):
        gch.tempStack.len = 0
        forAllChildren(c, waPush)
        while gch.tempStack.len > 0:
          dec(gch.tempStack.len)
          var d = gch.tempStack.d[gch.tempStack.len]
          d.refcount = d.refcount +% rcIncrement
          if d in gch.cycleRoots and not containsOrIncl(marker, d):
            forAllChildren(d, waPush)
  # remove cycles:
  for c in elements(gch.cycleRoots):
    if c.refcount <% rcIncrement:
      gch.tempStack.len = 0
      forAllChildren(c, waPush)
      while gch.tempStack.len > 0:
        dec(gch.tempStack.len)
        var d = gch.tempStack.d[gch.tempStack.len]
        if d.refcount <% rcIncrement:
          if d notin gch.cycleRoots: # d is leaf of c and not part of cycle
            addZCT(gch.zct, d)
            when logGC: writeCell("add to ZCT (from cycle collector)", d)
      prepareDealloc(c)
      gcTrace(c, csCycFreed)
      when logGC: writeCell("cycle collector dealloc cell", c)
      when reallyDealloc: rawDealloc(allocator, c)
      else:
        assert(c.typ != nil)
        zeroMem(c, sizeof(TCell))
  Deinit(gch.cycleRoots)
  Init(gch.cycleRoots)

proc gcMark(p: pointer) {.inline.} =
  # the addresses are not as cells on the stack, so turn them to cells:
  var cell = usrToCell(p)
  var c = cast[TAddress](cell)
  if c >% PageSize and (c and (MemAlign-1)) == 0:
    # fast check: does it look like a cell?
    if isAllocatedPtr(allocator, cell): 
      # mark the cell:
      cell.refcount = cell.refcount +% rcIncrement
      add(gch.decStack, cell)

proc markThreadStacks(gch: var TGcHeap) = 
  when isMultiThreaded:
    nil

# ----------------- stack management --------------------------------------
#  inspired from Smart Eiffel

when defined(sparc):
  const stackIncreases = false
elif defined(hppa) or defined(hp9000) or defined(hp9000s300) or
     defined(hp9000s700) or defined(hp9000s800) or defined(hp9000s820):
  const stackIncreases = true
else:
  const stackIncreases = false

when not defined(useNimRtl):
  proc setStackBottom(theStackBottom: pointer) =
    #c_fprintf(c_stdout, "stack bottom: %p;\n", theStackBottom)
    # the first init must be the one that defines the stack bottom:
    if stackBottom == nil: stackBottom = theStackBottom
    else:
      var a = cast[TAddress](theStackBottom) # and not PageMask - PageSize*2
      var b = cast[TAddress](stackBottom)
      when stackIncreases:
        stackBottom = cast[pointer](min(a, b))
      else:
        stackBottom = cast[pointer](max(a, b))

proc stackSize(): int {.noinline.} =
  var stackTop {.volatile.}: pointer
  result = abs(cast[int](addr(stackTop)) - cast[int](stackBottom))

when defined(sparc): # For SPARC architecture.
  proc isOnStack(p: pointer): bool =
    var stackTop {.volatile.}: pointer
    var b = cast[TAddress](stackBottom)
    var a = cast[TAddress](addr(stackTop))
    var x = cast[TAddress](p)
    result = x >=% a and x <=% b

  proc markStackAndRegisters(gch: var TGcHeap) {.noinline, cdecl.} =
    when defined(sparcv9):
      asm  """"flushw \n" """
    else:
      asm  """"ta      0x3   ! ST_FLUSH_WINDOWS\n" """

    var
      max = stackBottom
      sp: PPointer
      stackTop: array[0..1, pointer]
    sp = addr(stackTop[0])
    # Addresses decrease as the stack grows.
    while sp <= max:
      gcMark(sp^)
      sp = cast[ppointer](cast[TAddress](sp) +% sizeof(pointer))

elif defined(ELATE):
  {.error: "stack marking code is to be written for this architecture".}

elif stackIncreases:
  # ---------------------------------------------------------------------------
  # Generic code for architectures where addresses increase as the stack grows.
  # ---------------------------------------------------------------------------
  proc isOnStack(p: pointer): bool =
    var stackTop {.volatile.}: pointer
    var a = cast[TAddress](stackBottom)
    var b = cast[TAddress](addr(stackTop))
    var x = cast[TAddress](p)
    result = x >=% a and x <=% b

  var
    jmpbufSize {.importc: "sizeof(jmp_buf)", nodecl.}: int
      # a little hack to get the size of a TJmpBuf in the generated C code
      # in a platform independant way

  proc markStackAndRegisters(gch: var TGcHeap) {.noinline, cdecl.} =
    var registers: C_JmpBuf
    if c_setjmp(registers) == 0'i32: # To fill the C stack with registers.
      var max = cast[TAddress](stackBottom)
      var sp = cast[TAddress](addr(registers)) +% jmpbufSize -% sizeof(pointer)
      # sp will traverse the JMP_BUF as well (jmp_buf size is added,
      # otherwise sp would be below the registers structure).
      while sp >=% max:
        gcMark(cast[ppointer](sp)^)
        sp = sp -% sizeof(pointer)

else:
  # ---------------------------------------------------------------------------
  # Generic code for architectures where addresses decrease as the stack grows.
  # ---------------------------------------------------------------------------
  proc isOnStack(p: pointer): bool =
    var stackTop {.volatile.}: pointer
    var b = cast[TAddress](stackBottom)
    var a = cast[TAddress](addr(stackTop))
    var x = cast[TAddress](p)
    result = x >=% a and x <=% b

  proc markStackAndRegisters(gch: var TGcHeap) {.noinline, cdecl.} =
    # We use a jmp_buf buffer that is in the C stack.
    # Used to traverse the stack and registers assuming
    # that 'setjmp' will save registers in the C stack.
    var registers: C_JmpBuf
    if c_setjmp(registers) == 0'i32: # To fill the C stack with registers.
      var max = cast[TAddress](stackBottom)
      var sp = cast[TAddress](addr(registers))
      while sp <=% max:
        gcMark(cast[ppointer](sp)^)
        sp = sp +% sizeof(pointer)

# ----------------------------------------------------------------------------
# end of non-portable code
# ----------------------------------------------------------------------------

proc CollectZCT(gch: var TGcHeap) =
  # Note: Freeing may add child objects to the ZCT! So essentially we do 
  # deep freeing, which is bad for incremental operation. In order to 
  # avoid a deep stack, we move objects to keep the ZCT small.
  # This is performance critical!
  var L = addr(gch.zct.len)
  while L^ > 0:
    var c = gch.zct.d[0]
    # remove from ZCT:
    assert((c.refcount and colorMask) == rcZct)
    c.refcount = c.refcount and not colorMask
    gch.zct.d[0] = gch.zct.d[L^ - 1]
    dec(L^)
    if c.refcount <% rcIncrement: 
      # It may have a RC > 0, if it is in the hardware stack or
      # it has not been removed yet from the ZCT. This is because
      # ``incref`` does not bother to remove the cell from the ZCT 
      # as this might be too slow.
      # In any case, it should be removed from the ZCT. But not
      # freed. **KEEP THIS IN MIND WHEN MAKING THIS INCREMENTAL!**
      if canBeCycleRoot(c): excl(gch.cycleRoots, c)
      when logGC: writeCell("zct dealloc cell", c)
      gcTrace(c, csZctFreed)
      # We are about to free the object, call the finalizer BEFORE its
      # children are deleted as well, because otherwise the finalizer may
      # access invalid memory. This is done by prepareDealloc():
      prepareDealloc(c)
      forAllChildren(c, waZctDecRef)
      when reallyDealloc: rawDealloc(allocator, c)
      else:
        assert(c.typ != nil)
        zeroMem(c, sizeof(TCell))

proc unmarkStackAndRegisters(gch: var TGcHeap) = 
  var d = gch.decStack.d
  for i in 0..gch.decStack.len-1:
    assert isAllocatedPtr(allocator, d[i])
    decRef(d[i]) # OPT: cannot create a cycle!
  gch.decStack.len = 0

proc collectCT(gch: var TGcHeap) =
  if gch.zct.len >= ZctThreshold or (cycleGC and
      getOccupiedMem() >= cycleThreshold) or stressGC:
    gch.stat.maxStackSize = max(gch.stat.maxStackSize, stackSize())
    assert(gch.decStack.len == 0)
    markStackAndRegisters(gch)
    markThreadStacks(gch)
    gch.stat.maxStackCells = max(gch.stat.maxStackCells, gch.decStack.len)
    inc(gch.stat.stackScans)
    collectZCT(gch)
    when cycleGC:
      if getOccupiedMem() >= cycleThreshold or stressGC:
        collectCycles(gch)
        collectZCT(gch)
        inc(gch.stat.cycleCollections)
        cycleThreshold = max(InitialCycleThreshold, getOccupiedMem() *
                             cycleIncrease)
        gch.stat.maxThreshold = max(gch.stat.maxThreshold, cycleThreshold)
    unmarkStackAndRegisters(gch)

when not defined(useNimRtl):
  proc GC_disable() = discard atomicInc(recGcLock, 1)
  proc GC_enable() =
    if recGcLock > 0: discard atomicDec(recGcLock, 1)

  proc GC_setStrategy(strategy: TGC_Strategy) =
    case strategy
    of gcThroughput: nil
    of gcResponsiveness: nil
    of gcOptimizeSpace: nil
    of gcOptimizeTime: nil

  proc GC_enableMarkAndSweep() =
    cycleThreshold = InitialCycleThreshold

  proc GC_disableMarkAndSweep() =
    cycleThreshold = high(cycleThreshold)-1
    # set to the max value to suppress the cycle detector

  proc GC_fullCollect() =
    lock(gch)
    var oldThreshold = cycleThreshold
    cycleThreshold = 0 # forces cycle collection
    collectCT(gch)
    cycleThreshold = oldThreshold
    unlock(gch)

  proc GC_getStatistics(): string =
    GC_disable()
    result = "[GC] total memory: " & $(getTotalMem()) & "\n" &
             "[GC] occupied memory: " & $(getOccupiedMem()) & "\n" &
             "[GC] stack scans: " & $gch.stat.stackScans & "\n" &
             "[GC] stack cells: " & $gch.stat.maxStackCells & "\n" &
             "[GC] cycle collections: " & $gch.stat.cycleCollections & "\n" &
             "[GC] max threshold: " & $gch.stat.maxThreshold & "\n" &
             "[GC] zct capacity: " & $gch.zct.cap & "\n" &
             "[GC] max cycle table size: " & $gch.stat.cycleTableSize & "\n" &
             "[GC] max stack size: " & $gch.stat.maxStackSize
    when traceGC: writeLeakage()
    GC_enable()
