#
#
#            Nimrod's Runtime Library
#        (c) Copyright 2009 Andreas Rumpf
#
#    See the file "copying.txt", included in this
#    distribution, for details about the copyright.
#


# simple integer arithmetic with overflow checking

proc raiseOverflow {.compilerproc, noinline, noreturn.} =
  # a single proc to reduce code size to a minimum
  raise newException(EOverflow, "over- or underflow")

proc raiseDivByZero {.compilerproc, noinline, noreturn.} =
  raise newException(EDivByZero, "divison by zero")



proc absInt(a: int): int {.compilerProc, inline.} =
  if a != low(int):
    if a >= 0: return a
    else: return -a
  raiseOverflow()

const
  asmVersion = (defined(i386) or defined(x8664)) and
               (defined(vcc) or defined(wcc) or
               defined(dmc) or defined(gcc) or defined(llvm_gcc))
    # my Version of Borland C++Builder does not have
    # tasm32, which is needed for assembler blocks
    # this is why Borland is not included in the 'when'

when asmVersion and defined(i386) and not defined(gcc) and not defined(llvm_gcc):
  # assembler optimized versions for compilers that
  # have an intel syntax assembler:
  proc addInt32(a, b: int32): int32 {.compilerProc, pure.} =
    # a in eax, and b in edx
    asm """
        mov eax, `a`
        add eax, `b`
        jno theEnd
        call `raiseOverflow`
      theEnd:
    """

  proc subInt32(a, b: int32): int32 {.compilerProc, pure.} =
    asm """
        mov eax, `a`
        sub eax, `b`
        jno theEnd
        call `raiseOverflow`
      theEnd:
    """

  proc negInt32(a: int32): int32 {.compilerProc, pure.} =
    asm """
        mov eax, `a`
        neg eax
        jno theEnd
        call `raiseOverflow`
      theEnd:
    """

  proc divInt32(a, b: int32): int32 {.compilerProc, pure.} =
    asm """
        mov eax, `a`
        mov ecx, `b`
        xor edx, edx
        idiv ecx
        jno  theEnd
        call `raiseOverflow`
      theEnd:
    """

  proc modInt32(a, b: int32): int32 {.compilerProc, pure.} =
    asm """
        mov eax, `a`
        mov ecx, `b`
        xor edx, edx
        idiv ecx
        jno theEnd
        call `raiseOverflow`
      theEnd:
        mov eax, edx
    """

  proc mulInt32(a, b: int32): int32 {.compilerProc, pure.} =
    asm """
        mov eax, `a`
        mov ecx, `b`
        imul ecx
        jno theEnd
        call `raiseOverflow`
      theEnd:
    """

elif asmVersion and (defined(i386) or defined(x8664)) and (defined(gcc) or defined(llvm_gcc)):
  proc addInt32(a, b: int32): int32 {.compilerProc, inline.} =
    result = a
    asm """
      "addl %1, %0\n"
      "jno 1f\n"
      "call `raiseOverflow`\n"
      "1: \n"
      :"+r"(`result`)
      :"g"(`b`)
    """
  
  proc subInt32(a, b: int32): int32 {.compilerProc, inline.} =
    result = a
    asm """
      "subl %1, %0\n"
      "jno 1f\n"
      "call `raiseOverflow`\n"
      "1: \n"
      :"+r"(`result`)
      :"g"(`b`)
    """
  
  proc mulInt32(a, b: int32): int32 {.compilerProc, inline.} =
    result = a
    asm """
      "imull %1, %0\n"
      "jno 1f\n"
      "call `raiseOverflow`\n"
      "1: \n"
      :"+r"(`result`)
      :"g"(`b`)
    """

  proc divInt32(a, b: int32): int32 {.compilerProc, inline.} =
    if b == 0'i32: raiseDivByZero() 
    result = a
    var remainder = (if a < 0: -1'i32 else: 0'i32)
    var b2 = b
    asm """
      "idivl %2\n"
      :"+d"(`remainder`), "+a"(`result`)
      :"g"(`b2`)
    """

  proc modInt32(a, b: int32): int32 {.compilerProc, inline.} =
    if b == 0'i32: raiseDivByZero() 
    var quotient = a
    result = (if a < 0: -1'i32 else: 0'i32)
    var b2 = b
    asm """
      "idivl %2\n"
      :"+d"(`result`), "+a"(`quotient`)
      :"g"(`b2`)
    """

  when defined(x8664):
    proc addInt64(a, b: int64): int64 {.compilerProc, inline.} =
      result = a
      asm """
        "addq %1, %0\n"
        "jno 1f\n"
        "call `raiseOverflow`\n"
        "1: \n"
        :"+r"(`result`)
        :"g"(`b`)
      """

  proc subInt64(a, b: int64): int64 {.compilerProc, inline.} =
    result = a
    asm """
      "subq %1, %0\n"
      "jno 1f\n"
      "call `raiseOverflow`\n"
      "1: \n"
      :"+r"(`result`)
      :"g"(`b`)
    """
  
  proc mulInt64(a, b: int64): int64 {.compilerProc, inline.} =
    result = a
    asm """
      "imulq %1, %0\n"
      "jno 1f\n"
      "call `raiseOverflow`\n"
      "1: \n"
      :"+r"(`result`)
      :"g"(`b`)
    """
 
  proc divInt64(a, b: int64): int64 {.compilerProc, inline.} =
    if b == 0'i64: raiseDivByZero() 
    result = a
    var remainder = (if a < 0: -1'i64 else: 0'i64)
    var b2 = b
    asm """
      "idivq %2\n"
      :"+d"(`remainder`), "+a"(`result`)
      :"g"(`b2`)
    """

  proc modInt64(a, b: int64): int64 {.compilerProc, inline.} =
    if b == 0'i64: raiseDivByZero() 
    var quotient = a
    result = (if a < 0: -1'i64 else: 0'i64)
    var b2 = b
    asm """
      "idivq %2\n"
      :"+d"(`result`), "+a"(`quotient`)
      :"g"(`b2`)
    """

# 64-bit:

when not defined(mulInt64):
    #
    # This code has been inspired by Python's source code.
    # The native int product x*y is either exactly right or *way* off, being
    # just the last n bits of the true product, where n is the number of bits
    # in an int (the delivered product is the true product plus i*2**n for
    # some integer i).
    #
    # The native float64 product x*y is subject to three
    # rounding errors: on a sizeof(int)==8 box, each cast to double can lose
    # info, and even on a sizeof(int)==4 box, the multiplication can lose info.
    # But, unlike the native int product, it's not in *range* trouble:  even
    # if sizeof(int)==32 (256-bit ints), the product easily fits in the
    # dynamic range of a float64. So the leading 50 (or so) bits of the float64
    # product are correct.
    #
    # We check these two ways against each other, and declare victory if they're
    # approximately the same. Else, because the native int product is the only
    # one that can lose catastrophic amounts of information, it's the native int
    # product that must have overflowed.
    #
    proc mulInt64(a, b: int64): int64 {.compilerproc.} =
      var
        resAsFloat, floatProd: float64
      result = a *% b
      floatProd = toBiggestFloat(a) # conversion
      floatProd = floatProd * toBiggestFloat(b)
      resAsFloat = toBiggestFloat(result)

      # Fast path for normal case: small multiplicands, and no info
      # is lost in either method.
      if resAsFloat == floatProd: return result

      # Somebody somewhere lost info. Close enough, or way off? Note
      # that a != 0 and b != 0 (else resAsFloat == floatProd == 0).
      # The difference either is or isn't significant compared to the
      # true value (of which floatProd is a good approximation).

      # abs(diff)/abs(prod) <= 1/32 iff
      #   32 * abs(diff) <= abs(prod) -- 5 good bits is "close enough"
      if unlikely(32.0 * abs(resAsFloat - floatProd) > abs(floatProd)):
        raiseOverflow()
      return result

when not defined(addInt64):
    proc addInt64(a, b: int64): int64 {.compilerProc, inline.} =
      result = a +% b
      if unlikely((result xor a) < int64(0) and (result xor b) < int64(0)): raiseOverflow()
      return result

when not defined(subInt64):
    proc subInt64(a, b: int64): int64 {.compilerProc, inline.} =
      return addInt64(a, -b)

when not defined(negInt64):
    proc negInt64(a: int64): int64 {.compilerProc, inline.} =
      if unlikely(a == low(int64)):
        raiseOverflow()
      return ((not a) + 1)

when not defined(absInt64):
    proc absInt64(a: int64): int64 {.compilerProc, inline.} =
      if a >= 0: return a
      else: return -a

when not defined(divInt64):
    proc divInt64(a, b: int64): int64 {.compilerProc, inline.} =
      if b == int64(0):
        raiseDivByZero()
      if a == low(int64) and b == int64(-1):
        raiseOverflow()
      if a < 0 and b < 0:
        return (-a) // (-b)
      elif a < 0:
        return -((-a) // b)
      elif b < 0:
        return -(a // (-b))
      else:
        return a // b

when not defined(modInt64):
    proc modInt64(a, b: int64): int64 {.compilerProc, inline.} =
      if b == int64(0):
        raiseDivByZero()
      return a mod b

# 32-bit: (this is exactly the same as the above but s/64/32)

when not defined(mulInt32):
    #
    # This code has been inspired by Python's source code.
    # The native int product x*y is either exactly right or *way* off, being
    # just the last n bits of the true product, where n is the number of bits
    # in an int (the delivered product is the true product plus i*2**n for
    # some integer i).
    #
    # The native float32 product x*y is subject to three
    # rounding errors: on a sizeof(int)==8 box, each cast to double can lose
    # info, and even on a sizeof(int)==4 box, the multiplication can lose info.
    # But, unlike the native int product, it's not in *range* trouble:  even
    # if sizeof(int)==32 (256-bit ints), the product easily fits in the
    # dynamic range of a float32. So the leading 50 (or so) bits of the float32
    # product are correct.
    #
    # We check these two ways against each other, and declare victory if they're
    # approximately the same. Else, because the native int product is the only
    # one that can lose catastrophic amounts of information, it's the native int
    # product that must have overflowed.
    #
    proc mulInt32(a, b: int32): int32 {.compilerproc.} =
      var
        resAsFloat, floatProd: float32
      result = a *% b
      floatProd = toBiggestFloat(a) # conversion
      floatProd = floatProd * toBiggestFloat(b)
      resAsFloat = toBiggestFloat(result)

      # Fast path for normal case: small multiplicands, and no info
      # is lost in either method.
      if resAsFloat == floatProd: return result

      # Somebody somewhere lost info. Close enough, or way off? Note
      # that a != 0 and b != 0 (else resAsFloat == floatProd == 0).
      # The difference either is or isn't significant compared to the
      # true value (of which floatProd is a good approximation).

      # abs(diff)/abs(prod) <= 1/32 iff
      #   32 * abs(diff) <= abs(prod) -- 5 good bits is "close enough"
      if unlikely(32.0 * abs(resAsFloat - floatProd) > abs(floatProd)):
        raiseOverflow()
      return result

when not defined(addInt32):
    proc addInt32(a, b: int32): int32 {.compilerProc, inline.} =
      result = a +% b
      if unlikely((result xor a) < int32(0) and (result xor b) < int32(0)): raiseOverflow()
      return result

when not defined(subInt32):
    proc subInt32(a, b: int32): int32 {.compilerProc, inline.} =
      return addInt32(a, -b)

when not defined(negInt32):
    proc negInt32(a: int32): int32 {.compilerProc, inline.} =
      if unlikely(a == low(int32)):
        raiseOverflow()
      return ((not a) + 1)

when not defined(absInt32):
    proc absInt32(a: int32): int32 {.compilerProc, inline.} =
      if unlikely(a == low(int32)):
        raiseOverflow()
      if a >= 0: return a
      else: return -a

when not defined(divInt32):
    proc divInt32(a, b: int32): int32 {.compilerProc, inline.} =
      if b == int32(0):
        raiseDivByZero()
      if a == low(int32) and b == int32(-1):
        raiseOverflow()
      if a < 0 and b < 0:
        return (-a) // (-b)
      elif a < 0:
        return -((-a) // b)
      elif b < 0:
        return -(a // (-b))
      else:
        return a // b

when not defined(modInt32):
    proc modInt32(a, b: int32): int32 {.compilerProc, inline.} =
      if b == int32(0):
        raiseDivByZero()
      return a - ((a div b) * b)

# end

proc negInt(a : int) : int {.compilerProc, inline.} =
    when sizeof(int) == sizeof(int32):
        return int(negInt32(int32(a)))
    elif sizeof(int) == sizeof(int64):
        return int(negInt64(int64(a)))
    else:
        assert(false)

template binaryOption(base, if32, if64 : expr) : stmt =
    proc base(a, b : int) : int {.compilerProc, inline.} =
        when sizeof(int) == sizeof(int32):
            return int(if32(int32(a), int32(b)))
        elif sizeof(int) == sizeof(int64):
            return int(if64(int64(a), int64(b)))
        else:
            assert(false)

binaryOption(addInt, addInt32, addInt64)
binaryOption(subInt, subInt32, subInt64)
binaryOption(divInt, divInt32, divInt64)
binaryOption(modInt, modInt32, modInt64)
binaryOption(mulInt, mulInt32, mulInt64)

# We avoid setting the FPU control word here for compatibility with libraries
# written in other languages.

proc raiseFloatInvalidOp {.noinline, noreturn.} =
  raise newException(EFloatInvalidOp, "FPU operation caused a NaN result")

proc nanCheck(x: float64) {.compilerProc, inline.} =
  if x != x: raiseFloatInvalidOp()

proc raiseFloatOverflow(x: float64) {.noinline, noreturn.} =
  if x > 0.0:
    raise newException(EFloatOverflow, "FPU operation caused an overflow")
  else:
    raise newException(EFloatUnderflow, "FPU operations caused an underflow")

proc infCheck(x: float64) {.compilerProc, inline.} =
  if x != 0.0 and x*0.5 == x: raiseFloatOverflow(x)
