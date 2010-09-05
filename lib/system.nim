#
#
#            Nimrod's Runtime Library
#        (c) Copyright 2010 Andreas Rumpf
#
#    See the file "copying.txt", included in this
#    distribution, for details about the copyright.
#

## The compiler depends on the System module to work properly and the System
## module depends on the compiler. Most of the routines listed here use
## special compiler magic.
## Each module implicitly imports the System module; it must not be listed
## explicitly. Because of this there cannot be a user-defined module named
## ``system``.

{.push hints: off.}

type
  int* {.magic: Int.} ## default integer type; bitwidth depends on
                      ## architecture, but is always the same as a pointer
  int8* {.magic: Int8.} ## signed 8 bit integer type
  int16* {.magic: Int16.} ## signed 16 bit integer type
  int32* {.magic: Int32.} ## signed 32 bit integer type
  int64* {.magic: Int64.} ## signed 64 bit integer type
  float* {.magic: Float.} ## default floating point type
  float32* {.magic: Float32.} ## 32 bit floating point type
  float64* {.magic: Float64.} ## 64 bit floating point type
type # we need to start a new type section here, so that ``0`` can have a type
  bool* {.magic: Bool.} = enum ## built-in boolean type
    false = 0, true = 1

type
  char* {.magic: Char.} ## built-in 8 bit character type (unsigned)
  string* {.magic: String.} ## built-in string type
  cstring* {.magic: Cstring.} ## built-in cstring (*compatible string*) type
  pointer* {.magic: Pointer.} ## built-in pointer type
  Ordinal* {.magic: Ordinal.}[T]

type
  `nil` {.magic: "Nil".}
  expr* {.magic: Expr.} ## meta type to denote an expression (for templates)
  stmt* {.magic: Stmt.} ## meta type to denote a statement (for templates)
  typeDesc* {.magic: TypeDesc.} ## meta type to denote
                                ## a type description (for templates)

proc defined*[T](x: T): bool {.magic: "Defined", noSideEffect.}
  ## Special compile-time procedure that checks whether `x` is
  ## defined. `x` has to be an identifier or a qualified identifier.
  ## This can be used to check whether a library provides a certain
  ## feature or not:
  ##
  ## .. code-block:: Nimrod
  ##   when not defined(strutils.toUpper):
  ##     # provide our own toUpper proc here, because strutils is
  ##     # missing it.

proc definedInScope*[T](x: T): bool {.
  magic: "DefinedInScope", noSideEffect.}
  ## Special compile-time procedure that checks whether `x` is
  ## defined in the current scope. `x` has to be an identifier.

proc `not` *(x: bool): bool {.magic: "Not", noSideEffect.}
  ## Boolean not; returns true iff ``x == false``.

proc `and`*(x, y: bool): bool {.magic: "And", noSideEffect.}
  ## Boolean ``and``; returns true iff ``x == y == true``.
  ## Evaluation is short-circuited: this means that if ``x`` is false,
  ## ``y`` will not even be evaluated.
proc `or`*(x, y: bool): bool {.magic: "Or", noSideEffect.}
  ## Boolean ``or``; returns true iff ``not (not x and not y)``.
  ## Evaluation is short-circuited: this means that if ``x`` is true,
  ## ``y`` will not even be evaluated.
proc `xor`*(x, y: bool): bool {.magic: "Xor", noSideEffect.}
  ## Boolean `exclusive or`; returns true iff ``x != y``.

proc new*[T](a: var ref T) {.magic: "New", noSideEffect.}
  ## creates a new object of type ``T`` and returns a safe (traced)
  ## reference to it in ``a``.

proc new*[T](a: var ref T, finalizer: proc (x: ref T)) {.
  magic: "NewFinalize", noSideEffect.}
  ## creates a new object of type ``T`` and returns a safe (traced)
  ## reference to it in ``a``. When the garbage collector frees the object,
  ## `finalizer` is called. The `finalizer` may not keep a reference to the
  ## object pointed to by `x`. The `finalizer` cannot prevent the GC from
  ## freeing the object. Note: The `finalizer` refers to the type `T`, not to
  ## the object! This means that for each object of type `T` the finalizer
  ## will be called!

# for low and high the return type T may not be correct, but
# we handle that with compiler magic in SemLowHigh()
proc high*[T](x: T): T {.magic: "High", noSideEffect.}
  ## returns the highest possible index of an array, a sequence, a string or
  ## the highest possible value of an ordinal value `x`. As a special
  ## semantic rule, `x` may also be a type identifier.

proc low*[T](x: T): T {.magic: "Low", noSideEffect.}
  ## returns the lowest possible index of an array, a sequence, a string or
  ## the lowest possible value of an ordinal value `x`. As a special
  ## semantic rule, `x` may also be a type identifier.

type
  range*{.magic: "Range".} [T] ## Generic type to construct range types.
  array*{.magic: "Array".}[I, T]  ## Generic type to construct
                                  ## fixed-length arrays.
  openarray*{.magic: "OpenArray".}[T]  ## Generic type to construct open arrays.
                                       ## Open arrays are implemented as a
                                       ## pointer to the array data and a
                                       ## length field.
  seq*{.magic: "Seq".}[T]  ## Generic type to construct sequences.
  set*{.magic: "Set".}[T]  ## Generic type to construct bit sets.

when not defined(EcmaScript) and not defined(NimrodVM):
  type
    TGenericSeq {.compilerproc, pure.} = object
      len, space: int
    PGenericSeq {.exportc.} = ptr TGenericSeq
    # len and space without counting the terminating zero:
    NimStringDesc {.compilerproc, final.} = object of TGenericSeq
      data: array[0..100_000_000, char]
    NimString = ptr NimStringDesc

  include "system/hti"

type
  Byte* = Int8 ## this is an alias for ``int8``, that is a signed
               ## int 8 bits wide.

  Natural* = range[0..high(int)]
    ## is an int type ranging from zero to the maximum value
    ## of an int. This type is often useful for documentation and debugging.

  Positive* = range[1..high(int)]
    ## is an int type ranging from one to the maximum value
    ## of an int. This type is often useful for documentation and debugging.

  TObject* {.exportc: "TNimObject".} =
    object ## the root of Nimrod's object hierarchy. Objects should
           ## inherit from TObject or one of its descendants. However,
           ## objects that have no ancestor are allowed.
  PObject* = ref TObject ## reference to TObject

  E_Base* {.compilerproc.} = object of TObject ## base exception class;
                                               ## each exception has to
                                               ## inherit from `E_Base`.
    name: cstring             ## The exception's name is its Nimrod identifier.
                              ## This field is filled automatically in the
                              ## ``raise`` statement.
    msg* {.exportc: "message".}: string ## the exception's message. Not
                                        ## providing an exception message 
                                        ## is bad style.

  EAsynch* = object of E_Base ## Abstract exception class for
                              ## *asynchronous exceptions* (interrupts).
                              ## This is rarely needed: Most
                              ## exception types inherit from `ESynch`
  ESynch* = object of E_Base  ## Abstract exception class for
                              ## *synchronous exceptions*. Most exceptions
                              ## should be inherited (directly or indirectly)
                              ## from ESynch.
  ESystem* = object of ESynch ## Abstract class for exceptions that the runtime
                              ## system raises.
  EIO* = object of ESystem    ## raised if an IO error occured.
  EOS* = object of ESystem    ## raised if an operating system service failed.
  EInvalidLibrary* = object of EOS ## raised if a dynamic library
                                   ## could not be loaded.
  EResourceExhausted* = object of ESystem ## raised if a resource request
                                           ## could not be fullfilled.
  EArithmetic* = object of ESynch       ## raised if any kind of arithmetic
                                        ## error occured.
  EDivByZero* {.compilerproc.} =
    object of EArithmetic ## is the exception class for integer divide-by-zero
                          ## errors.
  EOverflow* {.compilerproc.} =
    object of EArithmetic  ## is the exception class for integer calculations
                           ## whose results are too large to fit in the
                           ## provided bits.

  EAccessViolation* {.compilerproc.} =
    object of ESynch ## the exception class for invalid memory access errors

  EAssertionFailed* {.compilerproc.} =
    object of ESynch  ## is the exception class for Assert
                      ## procedures that is raised if the
                      ## assertion proves wrong

  EControlC* = object of EAsynch        ## is the exception class for Ctrl+C
                                        ## key presses in console applications.

  EInvalidValue* = object of ESynch     ## is the exception class for string
                                        ## and object conversion errors.

  EOutOfMemory* = object of ESystem     ## is the exception class for
                                        ## unsuccessful attempts to allocate
                                        ## memory.

  EInvalidIndex* = object of ESynch     ## is raised if an array index is out
                                        ## of bounds.
  EInvalidField* = object of ESynch     ## is raised if a record field is not
                                        ## accessible because its dicriminant's
                                        ## value does not fit.

  EOutOfRange* = object of ESynch       ## is raised if a range check error
                                        ## occured.

  EStackOverflow* = object of ESystem   ## is raised if the hardware stack
                                        ## used for subroutine calls overflowed.

  ENoExceptionToReraise* = object of ESynch ## is raised if there is no
                                            ## exception to reraise.

  EInvalidObjectAssignment* =
    object of ESynch ## is raised if an object gets assigned to its
                     ## farther's object.

  EInvalidObjectConversion* =
    object of ESynch ## is raised if an object is converted to an incompatible
                     ## object type.

  EFloatingPoint* = object of ESynch ## base class for floating point exceptions
  EFloatInvalidOp* {.compilerproc.} = 
    object of EFloatingPoint ## Invalid operation according to IEEE: Raised by 
                             ## 0.0/0.0, for example.
  EFloatDivByZero* {.compilerproc.} = 
    object of EFloatingPoint ## Division by zero. Divisor is zero and dividend 
                             ## is a finite nonzero number.
  EFloatOverflow* {.compilerproc.} = 
    object of EFloatingPoint ## Overflow. Operation produces a result 
                             ## that exceeds the range of the exponent
  EFloatUnderflow* {.compilerproc.} = 
    object of EFloatingPoint ## Underflow. Operation produces a result 
                             ## that is too small to be represented as 
                             ## a normal number
  EFloatInexact* {.compilerproc.} = 
    object of EFloatingPoint ## Inexact. Operation produces a result
                             ## that cannot be represented with infinite
                             ## precision -- for example, 2.0 / 3.0, log(1.1) 
                             ## NOTE: Nimrod currently does not detect these!

  TResult* = enum Failure, Success

proc sizeof*[T](x: T): natural {.magic: "SizeOf", noSideEffect.}
  ## returns the size of ``x`` in bytes. Since this is a low-level proc,
  ## its usage is discouraged - using ``new`` for the most cases suffices
  ## that one never needs to know ``x``'s size. As a special semantic rule,
  ## ``x`` may also be a type identifier (``sizeof(int)`` is valid).

proc succ*[T](x: ordinal[T], y = 1): T {.magic: "Succ", noSideEffect.}
  ## returns the ``y``-th successor of the value ``x``. ``T`` has to be
  ## an ordinal type. If such a value does not exist, ``EOutOfRange`` is raised
  ## or a compile time error occurs.

proc pred*[T](x: ordinal[T], y = 1): T {.magic: "Pred", noSideEffect.}
  ## returns the ``y``-th predecessor of the value ``x``. ``T`` has to be
  ## an ordinal type. If such a value does not exist, ``EOutOfRange`` is raised
  ## or a compile time error occurs.

proc inc*[T](x: var ordinal[T], y = 1) {.magic: "Inc", noSideEffect.}
  ## increments the ordinal ``x`` by ``y``. If such a value does not
  ## exist, ``EOutOfRange`` is raised or a compile time error occurs. This is a
  ## short notation for: ``x = succ(x, y)``.

proc dec*[T](x: var ordinal[T], y = 1) {.magic: "Dec", noSideEffect.}
  ## decrements the ordinal ``x`` by ``y``. If such a value does not
  ## exist, ``EOutOfRange`` is raised or a compile time error occurs. This is a
  ## short notation for: ``x = pred(x, y)``.
  
proc newSeq*[T](s: var seq[T], len: int) {.magic: "NewSeq", noSideEffect.}
  ## creates a new sequence of type ``seq[T]`` with length ``len``.
  ## This is equivalent to ``s = @[]; setlen(s, len)``, but more
  ## efficient since no reallocation is needed.

proc len*[T](x: openarray[T]): int {.magic: "LengthOpenArray", noSideEffect.}
proc len*(x: string): int {.magic: "LengthStr", noSideEffect.}
proc len*(x: cstring): int {.magic: "LengthStr", noSideEffect.}
proc len*[I, T](x: array[I, T]): int {.magic: "LengthArray", noSideEffect.}
proc len*[T](x: seq[T]): int {.magic: "LengthSeq", noSideEffect.}
  ## returns the length of an array, a sequence or a string.
  ## This is rougly the same as ``high(T)-low(T)+1``, but its resulting type is
  ## always an int.

# set routines:
proc incl*[T](x: var set[T], y: T) {.magic: "Incl", noSideEffect.}
  ## includes element ``y`` to the set ``x``. This is the same as
  ## ``x = x + {y}``, but it might be more efficient.

proc excl*[T](x: var set[T], y: T) {.magic: "Excl", noSideEffect.}
  ## excludes element ``y`` to the set ``x``. This is the same as
  ## ``x = x - {y}``, but it might be more efficient.

proc card*[T](x: set[T]): int {.magic: "Card", noSideEffect.}
  ## returns the cardinality of the set ``x``, i.e. the number of elements
  ## in the set.

proc ord*[T](x: T): int {.magic: "Ord", noSideEffect.}
  ## returns the internal int value of an ordinal value ``x``.

proc chr*(u: range[0..255]): char {.magic: "Chr", noSideEffect.}
  ## converts an int in the range 0..255 to a character.

# --------------------------------------------------------------------------
# built-in operators

proc ze*(x: int8): int {.magic: "Ze8ToI", noSideEffect.}
  ## zero extends a smaller integer type to ``int``. This treats `x` as
  ## unsigned.
proc ze*(x: int16): int {.magic: "Ze16ToI", noSideEffect.}
  ## zero extends a smaller integer type to ``int``. This treats `x` as
  ## unsigned.

proc ze64*(x: int8): int64 {.magic: "Ze8ToI64", noSideEffect.}
  ## zero extends a smaller integer type to ``int64``. This treats `x` as
  ## unsigned.
proc ze64*(x: int16): int64 {.magic: "Ze16ToI64", noSideEffect.}
  ## zero extends a smaller integer type to ``int64``. This treats `x` as
  ## unsigned.

proc ze64*(x: int32): int64 {.magic: "Ze32ToI64", noSideEffect.}
  ## zero extends a smaller integer type to ``int64``. This treats `x` as
  ## unsigned.
proc ze64*(x: int): int64 {.magic: "ZeIToI64", noDecl, noSideEffect.}
  ## zero extends a smaller integer type to ``int64``. This treats `x` as
  ## unsigned. Does nothing if the size of an ``int`` is the same as ``int64``.
  ## (This is the case on 64 bit processors.)

proc toU8*(x: int): int8 {.magic: "ToU8", noSideEffect.}
  ## treats `x` as unsigned and converts it to a byte by taking the last 8 bits
  ## from `x`.
proc toU16*(x: int): int16 {.magic: "ToU16", noSideEffect.}
  ## treats `x` as unsigned and converts it to an ``int16`` by taking the last
  ## 16 bits from `x`.
proc toU32*(x: int64): int32 {.magic: "ToU32", noSideEffect.}
  ## treats `x` as unsigned and converts it to an ``int32`` by taking the
  ## last 32 bits from `x`.


# integer calculations:
proc `+` *(x: int): int {.magic: "UnaryPlusI", noSideEffect.}
proc `+` *(x: int8): int8 {.magic: "UnaryPlusI", noSideEffect.}
proc `+` *(x: int16): int16 {.magic: "UnaryPlusI", noSideEffect.}
proc `+` *(x: int32): int32 {.magic: "UnaryPlusI", noSideEffect.}
proc `+` *(x: int64): int64 {.magic: "UnaryPlusI64", noSideEffect.}
  ## Unary `+` operator for an integer. Has no effect.

proc `-` *(x: int): int {.magic: "UnaryMinusI", noSideEffect.}
proc `-` *(x: int8): int8 {.magic: "UnaryMinusI", noSideEffect.}
proc `-` *(x: int16): int16 {.magic: "UnaryMinusI", noSideEffect.}
proc `-` *(x: int32): int32 {.magic: "UnaryMinusI", noSideEffect.}
proc `-` *(x: int64): int64 {.magic: "UnaryMinusI64", noSideEffect.}
  ## Unary `-` operator for an integer. Negates `x`.

proc `not` *(x: int): int {.magic: "BitnotI", noSideEffect.}
proc `not` *(x: int8): int8 {.magic: "BitnotI", noSideEffect.}
proc `not` *(x: int16): int16 {.magic: "BitnotI", noSideEffect.}
proc `not` *(x: int32): int32 {.magic: "BitnotI", noSideEffect.}
proc `not` *(x: int64): int64 {.magic: "BitnotI64", noSideEffect.}
  ## computes the `bitwise complement` of the integer `x`.

proc `+` *(x, y: int): int {.magic: "AddI", noSideEffect.}
proc `+` *(x, y: int8): int8 {.magic: "AddI", noSideEffect.}
proc `+` *(x, y: int16): int16 {.magic: "AddI", noSideEffect.}
proc `+` *(x, y: int32): int32 {.magic: "AddI32", noSideEffect.}
proc `+` *(x, y: int64): int64 {.magic: "AddI64", noSideEffect.}
  ## Binary `+` operator for an integer.

proc `-` *(x, y: int): int {.magic: "SubI", noSideEffect.}
proc `-` *(x, y: int8): int8 {.magic: "SubI", noSideEffect.}
proc `-` *(x, y: int16): int16 {.magic: "SubI", noSideEffect.}
proc `-` *(x, y: int32): int32 {.magic: "SubI32", noSideEffect.}
proc `-` *(x, y: int64): int64 {.magic: "SubI64", noSideEffect.}
  ## Binary `-` operator for an integer.

proc `*` *(x, y: int): int {.magic: "MulI", noSideEffect.}
proc `*` *(x, y: int8): int8 {.magic: "MulI", noSideEffect.}
proc `*` *(x, y: int16): int16 {.magic: "MulI", noSideEffect.}
proc `*` *(x, y: int32): int32 {.magic: "MulI32", noSideEffect.}
proc `*` *(x, y: int64): int64 {.magic: "MulI64", noSideEffect.}
  ## Binary `*` operator for an integer.

proc `div` *(x, y: int): int {.magic: "DivI", noSideEffect.}
proc `div` *(x, y: int8): int8 {.magic: "DivI", noSideEffect.}
proc `div` *(x, y: int16): int16 {.magic: "DivI", noSideEffect.}
proc `div` *(x, y: int32): int32 {.magic: "DivI32", noSideEffect.}
proc `div` *(x, y: int64): int64 {.magic: "DivI64", noSideEffect.}
  ## computes the integer division. This is roughly the same as
  ## ``floor(x/y)``.

proc `mod` *(x, y: int): int {.magic: "ModI", noSideEffect.}
proc `mod` *(x, y: int8): int8 {.magic: "ModI", noSideEffect.}
proc `mod` *(x, y: int16): int16 {.magic: "ModI", noSideEffect.}
proc `mod` *(x, y: int32): int32 {.magic: "ModI32", noSideEffect.}
proc `mod` *(x, y: int64): int64 {.magic: "ModI64", noSideEffect.}
  ## computes the integer modulo operation. This is the same as
  ## ``x - (x div y) * y``.

proc `shr` *(x, y: int): int {.magic: "ShrI", noSideEffect.}
proc `shr` *(x, y: int8): int8 {.magic: "ShrI", noSideEffect.}
proc `shr` *(x, y: int16): int16 {.magic: "ShrI", noSideEffect.}
proc `shr` *(x, y: int32): int32 {.magic: "ShrI", noSideEffect.}
proc `shr` *(x, y: int64): int64 {.magic: "ShrI64", noSideEffect.}
  ## computes the `shift right` operation of `x` and `y`.

proc `shl` *(x, y: int): int {.magic: "ShlI", noSideEffect.}
proc `shl` *(x, y: int8): int8 {.magic: "ShlI", noSideEffect.}
proc `shl` *(x, y: int16): int16 {.magic: "ShlI", noSideEffect.}
proc `shl` *(x, y: int32): int32 {.magic: "ShlI", noSideEffect.}
proc `shl` *(x, y: int64): int64 {.magic: "ShlI64", noSideEffect.}
  ## computes the `shift left` operation of `x` and `y`.

proc `and` *(x, y: int): int {.magic: "BitandI", noSideEffect.}
proc `and` *(x, y: int8): int8 {.magic: "BitandI", noSideEffect.}
proc `and` *(x, y: int16): int16 {.magic: "BitandI", noSideEffect.}
proc `and` *(x, y: int32): int32 {.magic: "BitandI", noSideEffect.}
proc `and` *(x, y: int64): int64 {.magic: "BitandI64", noSideEffect.}
  ## computes the `bitwise and` of numbers `x` and `y`.

proc `or` *(x, y: int): int {.magic: "BitorI", noSideEffect.}
proc `or` *(x, y: int8): int8 {.magic: "BitorI", noSideEffect.}
proc `or` *(x, y: int16): int16 {.magic: "BitorI", noSideEffect.}
proc `or` *(x, y: int32): int32 {.magic: "BitorI", noSideEffect.}
proc `or` *(x, y: int64): int64 {.magic: "BitorI64", noSideEffect.}
  ## computes the `bitwise or` of numbers `x` and `y`.

proc `xor` *(x, y: int): int {.magic: "BitxorI", noSideEffect.}
proc `xor` *(x, y: int8): int8 {.magic: "BitxorI", noSideEffect.}
proc `xor` *(x, y: int16): int16 {.magic: "BitxorI", noSideEffect.}
proc `xor` *(x, y: int32): int32 {.magic: "BitxorI", noSideEffect.}
proc `xor` *(x, y: int64): int64 {.magic: "BitxorI64", noSideEffect.}
  ## computes the `bitwise xor` of numbers `x` and `y`.

proc `==` *(x, y: int): bool {.magic: "EqI", noSideEffect.}
proc `==` *(x, y: int8): bool {.magic: "EqI", noSideEffect.}
proc `==` *(x, y: int16): bool {.magic: "EqI", noSideEffect.}
proc `==` *(x, y: int32): bool {.magic: "EqI", noSideEffect.}
proc `==` *(x, y: int64): bool {.magic: "EqI64", noSideEffect.}
  ## Compares two integers for equality.

proc `<=` *(x, y: int): bool {.magic: "LeI", noSideEffect.}
proc `<=` *(x, y: int8): bool {.magic: "LeI", noSideEffect.}
proc `<=` *(x, y: int16): bool {.magic: "LeI", noSideEffect.}
proc `<=` *(x, y: int32): bool {.magic: "LeI", noSideEffect.}
proc `<=` *(x, y: int64): bool {.magic: "LeI64", noSideEffect.}
  ## Returns true iff `x` is less than or equal to `y`.

proc `<` *(x, y: int): bool {.magic: "LtI", noSideEffect.}
proc `<` *(x, y: int8): bool {.magic: "LtI", noSideEffect.}
proc `<` *(x, y: int16): bool {.magic: "LtI", noSideEffect.}
proc `<` *(x, y: int32): bool {.magic: "LtI", noSideEffect.}
proc `<` *(x, y: int64): bool {.magic: "LtI64", noSideEffect.}
  ## Returns true iff `x` is less than `y`.

proc abs*(x: int): int {.magic: "AbsI", noSideEffect.}
proc abs*(x: int8): int8 {.magic: "AbsI", noSideEffect.}
proc abs*(x: int16): int16 {.magic: "AbsI", noSideEffect.}
proc abs*(x: int32): int32 {.magic: "AbsI", noSideEffect.}
proc abs*(x: int64): int64 {.magic: "AbsI64", noSideEffect.}
  ## returns the absolute value of `x`. If `x` is ``low(x)`` (that 
  ## is -MININT for its type), an overflow exception is thrown (if overflow
  ## checking is turned on).

proc `+%` *(x, y: int): int {.magic: "AddU", noSideEffect.}
proc `+%` *(x, y: int8): int8 {.magic: "AddU", noSideEffect.}
proc `+%` *(x, y: int16): int16 {.magic: "AddU", noSideEffect.}
proc `+%` *(x, y: int32): int32 {.magic: "AddU", noSideEffect.}
proc `+%` *(x, y: int64): int64 {.magic: "AddU64", noSideEffect.}
  ## treats `x` and `y` as unsigned and adds them. The result is truncated to
  ## fit into the result. This implements modulo arithmetic. No overflow
  ## errors are possible.

proc `-%` *(x, y: int): int {.magic: "SubU", noSideEffect.}
proc `-%` *(x, y: int8): int8 {.magic: "SubU", noSideEffect.}
proc `-%` *(x, y: int16): int16 {.magic: "SubU", noSideEffect.}
proc `-%` *(x, y: int32): int32 {.magic: "SubU", noSideEffect.}
proc `-%` *(x, y: int64): int64 {.magic: "SubU64", noSideEffect.}
  ## treats `x` and `y` as unsigned and subtracts them. The result is
  ## truncated to fit into the result. This implements modulo arithmetic.
  ## No overflow errors are possible.

proc `*%` *(x, y: int): int {.magic: "MulU", noSideEffect.}
proc `*%` *(x, y: int8): int8 {.magic: "MulU", noSideEffect.}
proc `*%` *(x, y: int16): int16 {.magic: "MulU", noSideEffect.}
proc `*%` *(x, y: int32): int32 {.magic: "MulU", noSideEffect.}
proc `*%` *(x, y: int64): int64 {.magic: "MulU64", noSideEffect.}
  ## treats `x` and `y` as unsigned and multiplies them. The result is
  ## truncated to fit into the result. This implements modulo arithmetic.
  ## No overflow errors are possible.

proc `/%` *(x, y: int): int {.magic: "DivU", noSideEffect.}
proc `/%` *(x, y: int8): int8 {.magic: "DivU", noSideEffect.}
proc `/%` *(x, y: int16): int16 {.magic: "DivU", noSideEffect.}
proc `/%` *(x, y: int32): int32 {.magic: "DivU", noSideEffect.}
proc `/%` *(x, y: int64): int64 {.magic: "DivU64", noSideEffect.}
  ## treats `x` and `y` as unsigned and divides them. The result is
  ## truncated to fit into the result. This implements modulo arithmetic.
  ## No overflow errors are possible.

proc `%%` *(x, y: int): int {.magic: "ModU", noSideEffect.}
proc `%%` *(x, y: int8): int8 {.magic: "ModU", noSideEffect.}
proc `%%` *(x, y: int16): int16 {.magic: "ModU", noSideEffect.}
proc `%%` *(x, y: int32): int32 {.magic: "ModU", noSideEffect.}
proc `%%` *(x, y: int64): int64 {.magic: "ModU64", noSideEffect.}
  ## treats `x` and `y` as unsigned and compute the modulo of `x` and `y`.
  ## The result is truncated to fit into the result.
  ## This implements modulo arithmetic.
  ## No overflow errors are possible.

proc `<=%` *(x, y: int): bool {.magic: "LeU", noSideEffect.}
proc `<=%` *(x, y: int8): bool {.magic: "LeU", noSideEffect.}
proc `<=%` *(x, y: int16): bool {.magic: "LeU", noSideEffect.}
proc `<=%` *(x, y: int32): bool {.magic: "LeU", noSideEffect.}
proc `<=%` *(x, y: int64): bool {.magic: "LeU64", noSideEffect.}
  ## treats `x` and `y` as unsigned and compares them.
  ## Returns true iff ``unsigned(x) <= unsigned(y)``.

proc `<%` *(x, y: int): bool {.magic: "LtU", noSideEffect.}
proc `<%` *(x, y: int8): bool {.magic: "LtU", noSideEffect.}
proc `<%` *(x, y: int16): bool {.magic: "LtU", noSideEffect.}
proc `<%` *(x, y: int32): bool {.magic: "LtU", noSideEffect.}
proc `<%` *(x, y: int64): bool {.magic: "LtU64", noSideEffect.}
  ## treats `x` and `y` as unsigned and compares them.
  ## Returns true iff ``unsigned(x) < unsigned(y)``.


# floating point operations:
proc `+` *(x: float): float {.magic: "UnaryPlusF64", noSideEffect.}
proc `-` *(x: float): float {.magic: "UnaryMinusF64", noSideEffect.}
proc `+` *(x, y: float): float {.magic: "AddF64", noSideEffect.}
proc `-` *(x, y: float): float {.magic: "SubF64", noSideEffect.}
proc `*` *(x, y: float): float {.magic: "MulF64", noSideEffect.}
proc `/` *(x, y: float): float {.magic: "DivF64", noSideEffect.}
  ## computes the floating point division

proc `==` *(x, y: float): bool {.magic: "EqF64", noSideEffect.}
proc `<=` *(x, y: float): bool {.magic: "LeF64", noSideEffect.}
proc `<`  *(x, y: float): bool {.magic: "LtF64", noSideEffect.}
proc abs*(x: float): float {.magic: "AbsF64", noSideEffect.}
proc min*(x, y: float): float {.magic: "MinF64", noSideEffect.}
proc max*(x, y: float): float {.magic: "MaxF64", noSideEffect.}

# set operators
proc `*` *[T](x, y: set[T]): set[T] {.magic: "MulSet", noSideEffect.}
  ## This operator computes the intersection of two sets.
proc `+` *[T](x, y: set[T]): set[T] {.magic: "PlusSet", noSideEffect.}
  ## This operator computes the union of two sets.
proc `-` *[T](x, y: set[T]): set[T] {.magic: "MinusSet", noSideEffect.}
  ## This operator computes the difference of two sets.
proc `-+-` *[T](x, y: set[T]): set[T] {.magic: "SymDiffSet", noSideEffect.}
  ## computes the symmetric set difference. This is the same as
  ## ``(A - B) + (B - A)``, but more efficient.

# comparison operators:
proc `==` *[T](x, y: ordinal[T]): bool {.magic: "EqEnum", noSideEffect.}
proc `==` *(x, y: pointer): bool {.magic: "EqRef", noSideEffect.}
proc `==` *(x, y: string): bool {.magic: "EqStr", noSideEffect.}
proc `==` *(x, y: cstring): bool {.magic: "EqCString", noSideEffect.}
proc `==` *(x, y: char): bool {.magic: "EqCh", noSideEffect.}
proc `==` *(x, y: bool): bool {.magic: "EqB", noSideEffect.}
proc `==` *[T](x, y: set[T]): bool {.magic: "EqSet", noSideEffect.}
proc `==` *[T](x, y: ref T): bool {.magic: "EqRef", noSideEffect.}
proc `==` *[T](x, y: ptr T): bool {.magic: "EqRef", noSideEffect.}

proc `<=` *[T](x, y: ordinal[T]): bool {.magic: "LeEnum", noSideEffect.}
proc `<=` *(x, y: string): bool {.magic: "LeStr", noSideEffect.}
proc `<=` *(x, y: char): bool {.magic: "LeCh", noSideEffect.}
proc `<=` *[T](x, y: set[T]): bool {.magic: "LeSet", noSideEffect.}
proc `<=` *(x, y: bool): bool {.magic: "LeB", noSideEffect.}
proc `<=` *[T](x, y: ref T): bool {.magic: "LePtr", noSideEffect.}
proc `<=` *(x, y: pointer): bool {.magic: "LePtr", noSideEffect.}

proc `<` *[T](x, y: ordinal[T]): bool {.magic: "LtEnum", noSideEffect.}
proc `<` *(x, y: string): bool {.magic: "LtStr", noSideEffect.}
proc `<` *(x, y: char): bool {.magic: "LtCh", noSideEffect.}
proc `<` *[T](x, y: set[T]): bool {.magic: "LtSet", noSideEffect.}
proc `<` *(x, y: bool): bool {.magic: "LtB", noSideEffect.}
proc `<` *[T](x, y: ref T): bool {.magic: "LtPtr", noSideEffect.}
proc `<` *[T](x, y: ptr T): bool {.magic: "LtPtr", noSideEffect.}
proc `<` *(x, y: pointer): bool {.magic: "LtPtr", noSideEffect.}

template `!=` * (x, y: expr): expr =
  ## unequals operator. This is a shorthand for ``not (x == y)``.
  not (x == y)

template `>=` * (x, y: expr): expr =
  ## "is greater or equals" operator. This is the same as ``y <= x``.
  y <= x

template `>` * (x, y: expr): expr =
  ## "is greater" operator. This is the same as ``y < x``.
  y < x

proc contains*[T](x: set[T], y: T): bool {.magic: "InSet", noSideEffect.}
  ## One should overload this proc if one wants to overload the ``in`` operator.
  ## The parameters are in reverse order! ``a in b`` is a template for
  ## ``contains(b, a)``.
  ## This is because the unification algorithm that Nimrod uses for overload
  ## resolution works from left to right.
  ## But for the ``in`` operator that would be the wrong direction for this
  ## piece of code:
  ##
  ## .. code-block:: Nimrod
  ##   var s: set[range['a'..'z']] = {'a'..'c'}
  ##   writeln(stdout, 'b' in s)
  ##
  ## If ``in`` had been declared as ``[T](elem: T, s: set[T])`` then ``T`` would
  ## have been bound to ``char``. But ``s`` is not compatible to type
  ## ``set[char]``! The solution is to bind ``T`` to ``range['a'..'z']``. This
  ## is achieved by reversing the parameters for ``contains``; ``in`` then
  ## passes its arguments in reverse order.

template `in` * (x, y: expr): expr = contains(y, x)
template `not_in` * (x, y: expr): expr = not contains(y, x)

proc `is` *[T, S](x: T, y: S): bool {.magic: "Is", noSideEffect.}
template `is_not` *(x, y: expr): expr = not (x is y)

proc cmp*[T, S: typeDesc](x: T, y: S): int =
  ## Generic compare proc. Returns a value < 0 iff x < y, a value > 0 iff x > y
  ## and 0 iff x == y. This is useful for writing generic algorithms without
  ## performance loss. This generic implementation uses the `==` and `<`
  ## operators.
  if x == y: return 0
  if x < y: return -1
  return 1

proc cmp*(x, y: string): int {.noSideEffect.}
  ## Compare proc for strings. More efficient than the generic version.

proc `@` * [IDX, T](a: array[IDX, T]): seq[T] {.
  magic: "ArrToSeq", nosideeffect.}
  ## turns an array into a sequence. This most often useful for constructing
  ## sequences with the array constructor: ``@[1, 2, 3]`` has the type 
  ## ``seq[int]``, while ``[1, 2, 3]`` has the type ``array[0..2, int]``. 

proc setLen*[T](s: var seq[T], newlen: int) {.
  magic: "SetLengthSeq", noSideEffect.}
  ## sets the length of `s` to `newlen`.
  ## ``T`` may be any sequence type.
  ## If the current length is greater than the new length,
  ## ``s`` will be truncated.

proc setLen*(s: var string, newlen: int) {.
  magic: "SetLengthStr", noSideEffect.}
  ## sets the length of `s` to `newlen`.
  ## If the current length is greater than the new length,
  ## ``s`` will be truncated.

proc newString*(len: int): string {.
  magic: "NewString", importc: "mnewString", noSideEffect.}
  ## returns a new string of length ``len`` but with uninitialized
  ## content. One needs to fill the string character after character
  ## with the index operator ``s[i]``. This procedure exists only for
  ## optimization purposes; the same effect can be achieved with the
  ## ``&`` operator.

# concat operator:
proc `&` * (x: string, y: char): string {.
  magic: "ConStrStr", noSideEffect, merge.}
proc `&` * (x: char, y: char): string {.
  magic: "ConStrStr", noSideEffect, merge.}
proc `&` * (x, y: string): string {.
  magic: "ConStrStr", noSideEffect, merge.}
proc `&` * (x: char, y: string): string {.
  magic: "ConStrStr", noSideEffect, merge.}
  ## is the `concatenation operator`. It concatenates `x` and `y`.

proc add*(x: var string, y: char) {.magic: "AppendStrCh", noSideEffect.}
proc add*(x: var string, y: string) {.magic: "AppendStrStr", noSideEffect.}

type
  TEndian* = enum ## is a type describing the endianness of a processor.
    littleEndian, bigEndian

const
  isMainModule* {.magic: "IsMainModule".}: bool = false
    ## is true only when accessed in the main module. This works thanks to
    ## compiler magic. It is useful to embed testing code in a module.

  CompileDate* {.magic: "CompileDate"}: string = "0000-00-00"
    ## is the date of compilation as a string of the form
    ## ``YYYY-MM-DD``. This works thanks to compiler magic.

  CompileTime* {.magic: "CompileTime"}: string = "00:00:00"
    ## is the time of compilation as a string of the form
    ## ``HH:MM:SS``. This works thanks to compiler magic.

  NimrodVersion* {.magic: "NimrodVersion"}: string = "0.0.0"
    ## is the version of Nimrod as a string.
    ## This works thanks to compiler magic.

  NimrodMajor* {.magic: "NimrodMajor"}: int = 0
    ## is the major number of Nimrod's version.
    ## This works thanks to compiler magic.

  NimrodMinor* {.magic: "NimrodMinor"}: int = 0
    ## is the minor number of Nimrod's version.
    ## This works thanks to compiler magic.

  NimrodPatch* {.magic: "NimrodPatch"}: int = 0
    ## is the patch number of Nimrod's version.
    ## This works thanks to compiler magic.

  cpuEndian* {.magic: "CpuEndian"}: TEndian = littleEndian
    ## is the endianness of the target CPU. This is a valuable piece of
    ## information for low-level code only. This works thanks to compiler magic.
    
  hostOS* {.magic: "HostOS"}: string = ""
    ## a string that describes the host operating system. Possible values:
    ## "windows", "macosx", "linux", "netbsd", "freebsd", "openbsd", "solaris",
    ## "aix".
        
  hostCPU* {.magic: "HostCPU"}: string = ""
    ## a string that describes the host CPU. Possible values:
    ## "i386", "alpha", "powerpc", "sparc", "amd64", "mips", "arm".
  
  appType* {.magic: "AppType"}: string = ""
    ## a string that describes the application type. Possible values:
    ## "console", "gui", "lib".
  
include "system/inclrtl"
include "system/cgprocs"

proc add *[T](x: var seq[T], y: T) {.magic: "AppendSeqElem", noSideEffect.}
proc add *[T](x: var seq[T], y: openArray[T]) {.noSideEffect.} =
  ## Generic proc for adding a data item `y` to a container `x`.
  ## For containers that have an order, `add` means *append*. New generic
  ## containers should also call their adding proc `add` for consistency.
  ## Generic code becomes much easier to write if the Nimrod naming scheme is
  ## respected.
  var xl = x.len
  setLen(x, xl + y.len)
  for i in 0..high(y): x[xl+i] = y[i]

proc del* [T](x: var seq[T], i: int) {.noSideEffect.} = 
  ## deletes the item at index `i` by putting ``x[high(x)]`` into position `i`.
  ## This is an O(1) operation.
  var xl = x.len
  x[i] = x[xl-1]
  setLen(x, xl-1)
  
proc delete*[T](x: var seq[T], i: int) {.noSideEffect.} = 
  ## deletes the item at index `i` by moving ``x[i+1..]`` by one position.
  ## This is an O(n) operation.
  var xl = x.len
  for j in i..xl-2: x[j] = x[j+1]
  setLen(x, xl-1)
  
proc insert*[T](x: var seq[T], item: T, i = 0) {.noSideEffect.} = 
  ## inserts `item` into `x` at position `i`.
  var xl = x.len
  setLen(x, xl+1)
  var j = xl-1
  while j >= i:
    x[j+1] = x[j]
    dec(j)
  x[i] = item


proc repr*[T](x: T): string {.magic: "Repr", noSideEffect.}
  ## takes any Nimrod variable and returns its string representation. It
  ## works even for complex data graphs with cycles. This is a great
  ## debugging tool.

type
  TAddress* = int
    ## is the signed integer type that should be used for converting
    ## pointers to integer addresses for readability.

  BiggestInt* = int64
    ## is an alias for the biggest signed integer type the Nimrod compiler
    ## supports. Currently this is ``int64``, but it is platform-dependant
    ## in general.

  BiggestFloat* = float64
    ## is an alias for the biggest floating point type the Nimrod
    ## compiler supports. Currently this is ``float64``, but it is
    ## platform-dependant in general.

type # these work for most platforms:
  cchar* {.importc: "char", nodecl.} = char
    ## This is the same as the type ``char`` in *C*.
  cschar* {.importc: "signed char", nodecl.} = byte
    ## This is the same as the type ``signed char`` in *C*.
  cshort* {.importc: "short", nodecl.} = int16
    ## This is the same as the type ``short`` in *C*.
  cint* {.importc: "int", nodecl.} = int32
    ## This is the same as the type ``int`` in *C*.
  clong* {.importc: "long", nodecl.} = int
    ## This is the same as the type ``long`` in *C*.
  clonglong* {.importc: "long long", nodecl.} = int64
    ## This is the same as the type ``long long`` in *C*.
  cfloat* {.importc: "float", nodecl.} = float32
    ## This is the same as the type ``float`` in *C*.
  cdouble* {.importc: "double", nodecl.} = float64
    ## This is the same as the type ``double`` in *C*.
  clongdouble* {.importc: "long double", nodecl.} = BiggestFloat
    ## This is the same as the type ``long double`` in *C*.
    ## This C type is not supported by Nimrod's code generator

  cstringArray* {.importc: "char**", nodecl.} = ptr array [0..50_000, cstring]
    ## This is binary compatible to the type ``char**`` in *C*. The array's
    ## high value is large enough to disable bounds checking in practice.
    ## Use `cstringArrayToSeq` to convert it into a ``seq[string]``.

  PFloat32* = ptr Float32 ## an alias for ``ptr float32``
  PFloat64* = ptr Float64 ## an alias for ``ptr float64``
  PInt64* = ptr Int64 ## an alias for ``ptr int64``
  PInt32* = ptr Int32 ## an alias for ``ptr int32``
  
proc toFloat*(i: int): float {.
  magic: "ToFloat", noSideEffect, importc: "toFloat".}
  ## converts an integer `i` into a ``float``. If the conversion
  ## fails, `EInvalidValue` is raised. However, on most platforms the
  ## conversion cannot fail.

proc toBiggestFloat*(i: biggestint): biggestfloat {.
  magic: "ToBiggestFloat", noSideEffect, importc: "toBiggestFloat".}
  ## converts an biggestint `i` into a ``biggestfloat``. If the conversion
  ## fails, `EInvalidValue` is raised. However, on most platforms the
  ## conversion cannot fail.

proc toInt*(f: float): int {.
  magic: "ToInt", noSideEffect, importc: "toInt".}
  ## converts a floating point number `f` into an ``int``. Conversion
  ## rounds `f` if it does not contain an integer value. If the conversion
  ## fails (because `f` is infinite for example), `EInvalidValue` is raised.

proc toBiggestInt*(f: biggestfloat): biggestint {.
  magic: "ToBiggestInt", noSideEffect, importc: "toBiggestInt".}
  ## converts a biggestfloat `f` into a ``biggestint``. Conversion
  ## rounds `f` if it does not contain an integer value. If the conversion
  ## fails (because `f` is infinite for example), `EInvalidValue` is raised.

proc addQuitProc*(QuitProc: proc {.noconv.}) {.importc: "atexit", nodecl.}
  ## adds/registers a quit procedure. Each call to ``addQuitProc``
  ## registers another quit procedure. Up to 30 procedures can be
  ## registered. They are executed on a last-in, first-out basis
  ## (that is, the last function registered is the first to be executed).
  ## ``addQuitProc`` raises an EOutOfIndex if ``quitProc`` cannot be
  ## registered.

# Support for addQuitProc() is done by Ansi C's facilities here.
# In case of an unhandled exeption the exit handlers should
# not be called explicitly! The user may decide to do this manually though.

proc copy*(s: string, first = 0): string {.
  magic: "CopyStr", importc: "copyStr", noSideEffect.}
proc copy*(s: string, first, last: int): string {.
  magic: "CopyStrLast", importc: "copyStrLast", noSideEffect.}
  ## copies a slice of `s` into a new string and returns this new
  ## string. The bounds `first` and `last` denote the indices of
  ## the first and last characters that shall be copied. If ``last``
  ## is omitted, it is treated as ``high(s)``.

proc zeroMem*(p: Pointer, size: int) {.importc, noDecl.}
  ## overwrites the contents of the memory at ``p`` with the value 0.
  ## Exactly ``size`` bytes will be overwritten. Like any procedure
  ## dealing with raw memory this is *unsafe*.

proc copyMem*(dest, source: Pointer, size: int) {.importc: "memcpy", noDecl.}
  ## copies the contents from the memory at ``source`` to the memory
  ## at ``dest``. Exactly ``size`` bytes will be copied. The memory
  ## regions may not overlap. Like any procedure dealing with raw
  ## memory this is *unsafe*.

proc moveMem*(dest, source: Pointer, size: int) {.importc: "memmove", noDecl.}
  ## copies the contents from the memory at ``source`` to the memory
  ## at ``dest``. Exactly ``size`` bytes will be copied. The memory
  ## regions may overlap, ``moveMem`` handles this case appropriately
  ## and is thus somewhat more safe than ``copyMem``. Like any procedure
  ## dealing with raw memory this is still *unsafe*, though.

proc equalMem*(a, b: Pointer, size: int): bool {.
  importc: "equalMem", noDecl, noSideEffect.}
  ## compares the memory blocks ``a`` and ``b``. ``size`` bytes will
  ## be compared. If the blocks are equal, true is returned, false
  ## otherwise. Like any procedure dealing with raw memory this is
  ## *unsafe*.

proc alloc*(size: int): pointer {.noconv, rtl.}
  ## allocates a new memory block with at least ``size`` bytes. The
  ## block has to be freed with ``realloc(block, 0)`` or
  ## ``dealloc(block)``. The block is not initialized, so reading
  ## from it before writing to it is undefined behaviour!
proc alloc0*(size: int): pointer {.noconv, rtl.}
  ## allocates a new memory block with at least ``size`` bytes. The
  ## block has to be freed with ``realloc(block, 0)`` or
  ## ``dealloc(block)``. The block is initialized with all bytes
  ## containing zero, so it is somewhat safer than ``alloc``.
proc realloc*(p: Pointer, newsize: int): pointer {.noconv, rtl.}
  ## grows or shrinks a given memory block. If p is **nil** then a new
  ## memory block is returned. In either way the block has at least
  ## ``newsize`` bytes. If ``newsize == 0`` and p is not **nil**
  ## ``realloc`` calls ``dealloc(p)``. In other cases the block has to
  ## be freed with ``dealloc``.
proc dealloc*(p: Pointer) {.noconv, rtl.}
  ## frees the memory allocated with ``alloc``, ``alloc0`` or
  ## ``realloc``. This procedure is dangerous! If one forgets to
  ## free the memory a leak occurs; if one tries to access freed
  ## memory (or just freeing it twice!) a core dump may happen
  ## or other memory may be corrupted. 

proc assert*(cond: bool) {.magic: "Assert", noSideEffect.}
  ## provides a means to implement `programming by contracts`:idx: in Nimrod.
  ## ``assert`` evaluates expression ``cond`` and if ``cond`` is false, it
  ## raises an ``EAssertionFailure`` exception. However, the compiler may
  ## not generate any code at all for ``assert`` if it is advised to do so.
  ## Use ``assert`` for debugging purposes only.

proc swap*[T](a, b: var T) {.magic: "Swap", noSideEffect.}
  ## swaps the values `a` and `b`. This is often more efficient than
  ## ``tmp = a; a = b; b = tmp``. Particularly useful for sorting algorithms.

template `>=%` *(x, y: expr): expr = y <=% x
  ## treats `x` and `y` as unsigned and compares them.
  ## Returns true iff ``unsigned(x) >= unsigned(y)``.

template `>%` *(x, y: expr): expr = y <% x
  ## treats `x` and `y` as unsigned and compares them.
  ## Returns true iff ``unsigned(x) > unsigned(y)``.

proc `$` *(x: int): string {.magic: "IntToStr", noSideEffect.}
  ## The stingify operator for an integer argument. Returns `x`
  ## converted to a decimal string.

proc `$` *(x: int64): string {.magic: "Int64ToStr", noSideEffect.}
  ## The stingify operator for an integer argument. Returns `x`
  ## converted to a decimal string.

proc `$` *(x: float): string {.magic: "FloatToStr", noSideEffect.}
  ## The stingify operator for a float argument. Returns `x`
  ## converted to a decimal string.

proc `$` *(x: bool): string {.magic: "BoolToStr", noSideEffect.}
  ## The stingify operator for a boolean argument. Returns `x`
  ## converted to the string "false" or "true".

proc `$` *(x: char): string {.magic: "CharToStr", noSideEffect.}
  ## The stingify operator for a character argument. Returns `x`
  ## converted to a string.

proc `$` *(x: Cstring): string {.magic: "CStrToStr", noSideEffect.}
  ## The stingify operator for a CString argument. Returns `x`
  ## converted to a string.

proc `$` *(x: string): string {.magic: "StrToStr", noSideEffect.}
  ## The stingify operator for a string argument. Returns `x`
  ## as it is. This operator is useful for generic code, so
  ## that ``$expr`` also works if ``expr`` is already a string.

proc `$` *[T](x: ordinal[T]): string {.magic: "EnumToStr", noSideEffect.}
  ## The stingify operator for an enumeration argument. This works for
  ## any enumeration type thanks to compiler magic. If a
  ## a ``$`` operator for a concrete enumeration is provided, this is
  ## used instead. (In other words: *Overwriting* is possible.)

# undocumented:
proc getRefcount*[T](x: ref T): int {.importc: "getRefcount", noSideEffect.}
  ## retrieves the reference count of an heap-allocated object. The
  ## value is implementation-dependant.

#proc writeStackTrace() {.export: "writeStackTrace".}

when not defined(NimrodVM):
  proc getCurrentExceptionMsg*(): string {.exportc.}
    ## retrieves the error message that was attached to the current
    ## exception; if there is none, "" is returned.
  
  proc getCurrentException*(): ref E_Base
    ## retrieves the current exception; if there is none, nil is returned.

# new constants:
const
  inf* {.magic: "Inf".} = 1.0 / 0.0
    ## contains the IEEE floating point value of positive infinity.
  neginf* {.magic: "NegInf".} = -inf
    ## contains the IEEE floating point value of negative infinity.
  nan* {.magic: "NaN".} = 0.0 / 0.0
    ## contains an IEEE floating point value of *Not A Number*. Note
    ## that you cannot compare a floating point value to this value
    ## and expect a reasonable result - use the `classify` procedure
    ## in the module ``math`` for checking for NaN.

# GC interface:

proc getOccupiedMem*(): int {.rtl.}
  ## returns the number of bytes that are owned by the process and hold data.

proc getFreeMem*(): int {.rtl.}
  ## returns the number of bytes that are owned by the process, but do not
  ## hold any meaningful data.

proc getTotalMem*(): int {.rtl.}
  ## returns the number of bytes that are owned by the process.


iterator countdown*[T](a, b: T, step = 1): T {.inline.} =
  ## Counts from ordinal value `a` down to `b` with the given
  ## step count. `T` may be any ordinal type, `step` may only
  ## be positive.
  var res = a
  while res >= b:
    yield res
    dec(res, step)

iterator countup*[T](a, b: T, step = 1): T {.inline.} =
  ## Counts from ordinal value `a` up to `b` with the given
  ## step count. `T` may be any ordinal type, `step` may only
  ## be positive.
  var res = a
  while res <= b:
    yield res
    inc(res, step)
  # we cannot use ``for x in a..b: `` here, because that is not
  # known in the System module


proc min*(x, y: int): int {.magic: "MinI", noSideEffect.}
proc min*(x, y: int8): int8 {.magic: "MinI", noSideEffect.}
proc min*(x, y: int16): int16 {.magic: "MinI", noSideEffect.}
proc min*(x, y: int32): int32 {.magic: "MinI", noSideEffect.}
proc min*(x, y: int64): int64 {.magic: "MinI64", noSideEffect.}
  ## The minimum value of two integers.

proc min*[T](x: openarray[T]): T = 
  ## The minimum value of an openarray.
  result = x[0]
  for i in 1..high(x): result = min(result, x[i])

proc max*(x, y: int): int {.magic: "MaxI", noSideEffect.}
proc max*(x, y: int8): int8 {.magic: "MaxI", noSideEffect.}
proc max*(x, y: int16): int16 {.magic: "MaxI", noSideEffect.}
proc max*(x, y: int32): int32 {.magic: "MaxI", noSideEffect.}
proc max*(x, y: int64): int64 {.magic: "MaxI64", noSideEffect.}
  ## The maximum value of two integers.

proc max*[T](x: openarray[T]): T = 
  ## The maximum value of an openarray.
  result = x[0]
  for i in 1..high(x): result = max(result, x[i])


iterator items*[T](a: openarray[T]): T {.inline.} =
  ## iterates over each item of `a`.
  var i = 0
  while i < len(a):
    yield a[i]
    inc(i)

iterator items*[IX, T](a: array[IX, T]): T {.inline.} =
  ## iterates over each item of `a`.
  var i = low(IX)
  if i <= high(IX):
    while true:
      yield a[i]
      if i >= high(IX): break
      inc(i)

iterator items*[T](a: seq[T]): T {.inline.} =
  ## iterates over each item of `a`.
  var i = 0
  while i < len(a):
    yield a[i]
    inc(i)

iterator items*(a: string): char {.inline.} =
  ## iterates over each item of `a`.
  var i = 0
  while i < len(a):
    yield a[i]
    inc(i)

iterator items*[T](a: set[T]): T {.inline.} =
  ## iterates over each element of `a`. `items` iterates only over the
  ## elements that are really in the set (and not over the ones the set is
  ## able to hold).
  var i = low(T)
  if i <= high(T):
    while true:
      if i in a: yield i
      if i >= high(T): break
      inc(i)

iterator items*(a: cstring): char {.inline.} =
  ## iterates over each item of `a`.
  var i = 0
  while a[i] != '\0':
    yield a[i]
    inc(i)

proc isNil*[T](x: seq[T]): bool {.noSideEffect, magic: "IsNil".}
proc isNil*[T](x: ref T): bool {.noSideEffect, magic: "IsNil".}
proc isNil*(x: string): bool {.noSideEffect, magic: "IsNil".}
proc isNil*[T](x: ptr T): bool {.noSideEffect, magic: "IsNil".}
proc isNil*(x: pointer): bool {.noSideEffect, magic: "IsNil".}
proc isNil*(x: cstring): bool {.noSideEffect, magic: "IsNil".}
  ## Fast check whether `x` is nil. This is sometimes more efficient than
  ## ``== nil``.

proc `&` *[T](x, y: openArray[T]): seq[T] {.noSideEffect.} =
  newSeq(result, x.len + y.len)
  for i in 0..x.len-1:
    result[i] = x[i]
  for i in 0..y.len-1:
    result[i+x.len] = y[i]

proc `&` *[T](x: openArray[T], y: T): seq[T] {.noSideEffect.} =
  newSeq(result, x.len + 1)
  for i in 0..x.len-1:
    result[i] = x[i]
  result[x.len] = y

proc `&` *[T](x: T, y: openArray[T]): seq[T] {.noSideEffect.} =
  newSeq(result, y.len + 1)
  for i in 0..y.len-1:
    result[i] = y[i]
  result[y.len] = x

when not defined(NimrodVM):
  when not defined(ECMAScript):
    proc seqToPtr[T](x: seq[T]): pointer {.inline, nosideeffect.} =
      result = cast[pointer](x)
  else:
    proc seqToPtr[T](x: seq[T]): pointer {.pure, nosideeffect.} =
      asm """return `x`"""
  
  proc `==` *[T: typeDesc](x, y: seq[T]): bool {.noSideEffect.} =
    ## Generic equals operator for sequences: relies on a equals operator for
    ## the element type `T`.
    if seqToPtr(x) == seqToPtr(y):
      result = true
    elif seqToPtr(x) == nil or seqToPtr(y) == nil:
      result = false
    elif x.len == y.len:
      for i in 0..x.len-1:
        if x[i] != y[i]: return false
      result = true

proc find*[T, S: typeDesc](a: T, item: S): int {.inline.}=
  ## Returns the first index of `item` in `a` or -1 if not found. This requires
  ## appropriate `items` and `==` procs to work.
  for i in items(a):
    if i == item: return
    inc(result)
  result = -1

proc contains*[T](a: openArray[T], item: T): bool {.inline.}=
  ## Returns true if `item` is in `a` or false if not found. This is a shortcut
  ## for ``find(a, item) >= 0``.
  return find(a, item) >= 0

proc pop*[T](s: var seq[T]): T {.inline, noSideEffect.} = 
  ## returns the last item of `s` and decreases ``s.len`` by one. This treats
  ## `s` as a stack and implements the common *pop* operation.
  var L = s.len-1
  result = s[L]
  setLen(s, L)

proc each*[T, S](data: openArray[T], op: proc (x: T): S): seq[S] {.
    noSideEffect.} = 
  ## The well-known ``map`` operation from functional programming. Applies
  ## `op` to every item in `data` and returns the result as a sequence.
  newSeq(result, data.len)
  for i in 0..data.len-1: result[i] = op(data[i])

proc each*[T](data: var openArray[T], op: proc (x: var T)) =
  ## The well-known ``map`` operation from functional programming. Applies
  ## `op` to every item in `data`.
  for i in 0..data.len-1: op(data[i])


# ----------------- FPU ------------------------------------------------------

#proc disableFPUExceptions*()
# disables all floating point unit exceptions

#proc enableFPUExceptions*()
# enables all floating point unit exceptions

# ----------------- GC interface ---------------------------------------------

proc GC_disable*() {.rtl.}
  ## disables the GC. If called n-times, n calls to `GC_enable` are needed to
  ## reactivate the GC. Note that in most circumstances one should only disable
  ## the mark and sweep phase with `GC_disableMarkAndSweep`.

proc GC_enable*() {.rtl.}
  ## enables the GC again.

proc GC_fullCollect*() {.rtl.}
  ## forces a full garbage collection pass.
  ## Ordinary code does not need to call this (and should not).

type
  TGC_Strategy* = enum ## the strategy the GC should use for the application
    gcThroughput,      ## optimize for throughput
    gcResponsiveness,  ## optimize for responsiveness (default)
    gcOptimizeTime,    ## optimize for speed
    gcOptimizeSpace    ## optimize for memory footprint

proc GC_setStrategy*(strategy: TGC_Strategy) {.rtl.}
  ## tells the GC the desired strategy for the application.

proc GC_enableMarkAndSweep*() {.rtl.}
proc GC_disableMarkAndSweep*() {.rtl.}
  ## the current implementation uses a reference counting garbage collector
  ## with a seldomly run mark and sweep phase to free cycles. The mark and
  ## sweep phase may take a long time and is not needed if the application
  ## does not create cycles. Thus the mark and sweep phase can be deactivated
  ## and activated separately from the rest of the GC.

proc GC_getStatistics*(): string {.rtl.}
  ## returns an informative string about the GC's activity. This may be useful
  ## for tweaking.
  
proc GC_ref*[T](x: ref T) {.magic: "GCref".}
proc GC_ref*[T](x: seq[T]) {.magic: "GCref".}
proc GC_ref*(x: string) {.magic: "GCref".}
  ## marks the object `x` as referenced, so that it will not be freed until
  ## it is unmarked via `GC_unref`. If called n-times for the same object `x`,
  ## n calls to `GC_unref` are needed to unmark `x`. 
  
proc GC_unref*[T](x: ref T) {.magic: "GCunref".}
proc GC_unref*[T](x: seq[T]) {.magic: "GCunref".}
proc GC_unref*(x: string) {.magic: "GCunref".}
  ## see the documentation of `GC_ref`.

template accumulateResult*(iter: expr) =
  ## helps to convert an iterator to a proc.
  result = @[]
  for x in iter: add(result, x)

{.push checks: off, line_dir: off, debugger: off.}  
# obviously we cannot generate checking operations here :-)
# because it would yield into an endless recursion
# however, stack-traces are available for most parts
# of the code

var
  dbgLineHook*: proc = nil
    ## set this variable to provide a procedure that should be called before
    ## each executed instruction. This should only be used by debuggers!
    ## Only code compiled with the ``debugger:on`` switch calls this hook.

when not defined(ECMAScript):
  {.push overflow_checks:off}
  proc add* (x: var string, y: cstring) =
    var i = 0
    while y[i] != '\0':
      add(x, y[i])
      inc(i)
  {.pop.}
else:
  proc add* (x: var string, y: cstring) {.pure.} =
    asm """
      var len = `x`[0].length-1;
      for (var i = 0; i < `y`.length; ++i) {
        `x`[0][len] = `y`.charCodeAt(i);
        ++len;
      }
      `x`[0][len] = 0
    """

proc `/`*(x, y: int): float {.inline, noSideEffect.} =
  ## integer division that results in a float.
  result = toFloat(x) / toFloat(y)

proc echo*[Ty](x: openarray[Ty]) {.magic: "Echo".}
  ## equivalent to ``writeln(stdout, x); flush(stdout)``. BUT: This is
  ## available for the ECMAScript target too!

template newException*(exceptn, message: expr): expr = 
  ## creates an exception object of type "exceptn" and sets its ``msg`` field
  ## to `message`. Returns the new exception object. 
  block: # open a new scope
    var
      e: ref exceptn
    new(e)
    e.msg = message
    e

const
  QuitSuccess* = 0
    ## is the value that should be passed to ``quit`` to indicate
    ## success.

  QuitFailure* = 1
    ## is the value that should be passed to ``quit`` to indicate
    ## failure.

proc quit*(errorcode: int = QuitSuccess) {.
  magic: "Exit", importc: "exit", noDecl, noReturn.}
  ## stops the program immediately; before stopping the program the
  ## "quit procedures" are called in the opposite order they were added
  ## with ``addQuitProc``. ``quit`` never returns and ignores any
  ## exception that may have been raised by the quit procedures.
  ## It does *not* call the garbage collector to free all the memory,
  ## unless a quit procedure calls ``GC_collect``.

when not defined(EcmaScript) and not defined(NimrodVM): 
  proc quit*(errormsg: string) {.noReturn.}
    ## a shorthand for ``echo(errormsg); quit(quitFailure)``.

when not defined(EcmaScript) and not defined(NimrodVM):
  
  proc likely*(val : bool) : bool {.importc: "likely", nodecl, nosideeffect}
  proc unlikely*(val : bool) : bool {.importc: "unlikely", nodecl, nosideeffect}


  proc atomicInc*(memLoc: var int, x: int): int {.inline.}
    ## atomic increment of `memLoc`. Returns the value after the operation.
  
  proc atomicDec*(memLoc: var int, x: int): int {.inline.}
    ## atomic decrement of `memLoc`. Returns the value after the operation.

  proc initGC()

  proc initStackBottom() {.inline.} = 
    # WARNING: This is very fragile! An array size of 8 does not work on my
    # Linux 64bit system. Very strange, but we are at the will of GCC's 
    # optimizer...
    var locals {.volatile.}: pointer
    setStackBottom(addr(locals))

  var
    strDesc: TNimType

  strDesc.size = sizeof(string)
  strDesc.kind = tyString
  strDesc.flags = {ntfAcyclic}
  initStackBottom()
  initGC() # BUGFIX: need to be called here!

  {.push stack_trace: off.}

  include "system/ansi_c"

  proc cmp(x, y: string): int =
    return int(c_strcmp(x, y))

  const pccHack = if defined(pcc): "_" else: "" # Hack for PCC
  when defined(windows):
    # work-around C's sucking abstraction:
    # BUGFIX: stdin and stdout should be binary files!
    proc setmode(handle, mode: int) {.importc: pccHack & "setmode",
                                      header: "<io.h>".}
    proc fileno(f: C_TextFileStar): int {.importc: pccHack & "fileno",
                                          header: "<fcntl.h>".}
    var
      O_BINARY {.importc: pccHack & "O_BINARY", nodecl.}: int

    # we use binary mode in Windows:
    setmode(fileno(c_stdin), O_BINARY)
    setmode(fileno(c_stdout), O_BINARY)
  
  when defined(endb):
    proc endbStep()

  # ----------------- IO Part --------------------------------------------------

  type
    CFile {.importc: "FILE", nodecl, final.} = object  # empty record for
                                                       # data hiding
    TFile* = ptr CFile ## The type representing a file handle.

    TFileMode* = enum           ## The file mode when opening a file.
      fmRead,                   ## Open the file for read access only.
      fmWrite,                  ## Open the file for write access only.
      fmReadWrite,              ## Open the file for read and write access.
                                ## If the file does not exist, it will be
                                ## created.
      fmReadWriteExisting,      ## Open the file for read and write access.
                                ## If the file does not exist, it will not be
                                ## created.
      fmAppend                  ## Open the file for writing only; append data
                                ## at the end.

    TFileHandle* = cint ## type that represents an OS file handle; this is
                        ## useful for low-level file access

  # text file handling:
  var
    stdin* {.importc: "stdin", noDecl.}: TFile   ## The standard input stream.
    stdout* {.importc: "stdout", noDecl.}: TFile ## The standard output stream.
    stderr* {.importc: "stderr", noDecl.}: TFile
      ## The standard error stream.
      ##
      ## Note: In my opinion, this should not be used -- the concept of a
      ## separate error stream is a design flaw of UNIX. A seperate *message
      ## stream* is a good idea, but since it is named ``stderr`` there are few
      ## programs out there that distinguish properly between ``stdout`` and
      ## ``stderr``. So, that's what you get if you don't name your variables
      ## appropriately. It also annoys people if redirection via ``>output.txt``
      ## does not work because the program writes to ``stderr``.

  proc Open*(f: var TFile, filename: string,
             mode: TFileMode = fmRead, bufSize: int = -1): Bool
    ## Opens a file named `filename` with given `mode`.
    ##
    ## Default mode is readonly. Returns true iff the file could be opened.
    ## This throws no exception if the file could not be opened. The reason is
    ## that the programmer needs to provide an appropriate error message 
    ## anyway.

  proc Open*(f: var TFile, filehandle: TFileHandle,
             mode: TFileMode = fmRead): Bool
    ## Creates a ``TFile`` from a `filehandle` with given `mode`.
    ##
    ## Default mode is readonly. Returns true iff the file could be opened.

  proc reopen*(f: TFile, filename: string, mode: TFileMode = fmRead): bool
    ## reopens the file `f` with given `filename` and `mode`. This 
    ## is often used to redirect the `stdin`, `stdout` or `stderr`
    ## file variables.
    ##
    ## Default mode is readonly. Returns true iff the file could be reopened.

  proc Close*(f: TFile) {.importc: "fclose", nodecl.}
    ## Closes the file.

  proc EndOfFile*(f: TFile): Bool
    ## Returns true iff `f` is at the end.
  proc readChar*(f: TFile): char {.importc: "fgetc", nodecl.}
    ## Reads a single character from the stream `f`. If the stream
    ## has no more characters, `EEndOfFile` is raised.
  proc FlushFile*(f: TFile) {.importc: "fflush", noDecl.}
    ## Flushes `f`'s buffer.

  proc readFile*(filename: string): string
    ## Opens a file name `filename` for reading. Then reads the
    ## file's content completely into a string and
    ## closes the file afterwards. Returns the string. Returns nil if there was
    ## an error. Does not throw an IO exception.

  proc write*(f: TFile, r: float)
  proc write*(f: TFile, i: int)
  proc write*(f: TFile, s: string)
  proc write*(f: TFile, b: Bool)
  proc write*(f: TFile, c: char)
  proc write*(f: TFile, c: cstring)
  proc write*(f: TFile, a: openArray[string])
    ## Writes a value to the file `f`. May throw an IO exception.

  proc readLine*(f: TFile): string
    ## reads a line of text from the file `f`. May throw an IO exception.
    ## Reading from an empty file buffer, does not throw an exception, but
    ## returns nil. A line of text may be delimited by ``CR``, ``LF`` or
    ## ``CRLF``. The newline character(s) are not part of the returned string.

  proc writeln*[Ty](f: TFile, x: Ty) {.inline.}
    ## writes a value `x` to `f` and then writes "\n".
    ## May throw an IO exception.

  proc writeln*[Ty](f: TFile, x: openArray[Ty]) {.inline.}
    ## writes a value `x` to `f` and then writes "\n".
    ## May throw an IO exception.

  proc getFileSize*(f: TFile): int64
    ## retrieves the file size (in bytes) of `f`.

  proc ReadBytes*(f: TFile, a: var openarray[byte], start, len: int): int
    ## reads `len` bytes into the buffer `a` starting at ``a[start]``. Returns
    ## the actual number of bytes that have been read which may be less than
    ## `len` (if not as many bytes are remaining), but not greater.

  proc ReadChars*(f: TFile, a: var openarray[char], start, len: int): int
    ## reads `len` bytes into the buffer `a` starting at ``a[start]``. Returns
    ## the actual number of bytes that have been read which may be less than
    ## `len` (if not as many bytes are remaining), but not greater.

  proc readBuffer*(f: TFile, buffer: pointer, len: int): int
    ## reads `len` bytes into the buffer pointed to by `buffer`. Returns
    ## the actual number of bytes that have been read which may be less than
    ## `len` (if not as many bytes are remaining), but not greater.

  proc writeBytes*(f: TFile, a: openarray[byte], start, len: int): int
    ## writes the bytes of ``a[start..start+len-1]`` to the file `f`. Returns
    ## the number of actual written bytes, which may be less than `len` in case
    ## of an error.

  proc writeChars*(f: tFile, a: openarray[char], start, len: int): int
    ## writes the bytes of ``a[start..start+len-1]`` to the file `f`. Returns
    ## the number of actual written bytes, which may be less than `len` in case
    ## of an error.

  proc writeBuffer*(f: TFile, buffer: pointer, len: int): int
    ## writes the bytes of buffer pointed to by the parameter `buffer` to the
    ## file `f`. Returns the number of actual written bytes, which may be less
    ## than `len` in case of an error.

  proc setFilePos*(f: TFile, pos: int64)
    ## sets the position of the file pointer that is used for read/write
    ## operations. The file's first byte has the index zero.

  proc getFilePos*(f: TFile): int64
    ## retrieves the current position of the file pointer that is used to
    ## read from the file `f`. The file's first byte has the index zero.

  include "system/sysio"

  iterator lines*(filename: string): string =
    ## Iterate over any line in the file named `filename`.
    ## If the file does not exist `EIO` is raised.
    var
      f: TFile
    if not open(f, filename):
      raise newException(EIO, "cannot open: " & filename)
    var res = ""
    while not endOfFile(f):
      rawReadLine(f, res)
      yield res
    Close(f)

  iterator lines*(f: TFile): string =
    ## Iterate over any line in the file `f`.
    var res = ""
    while not endOfFile(f):
      rawReadLine(f, res)
      yield res

  proc fileHandle*(f: TFile): TFileHandle {.importc: "fileno",
                                            header: "<stdio.h>"}
    ## returns the OS file handle of the file ``f``. This is only useful for
    ## platform specific programming.

  proc quit(errormsg: string) =
    echo(errormsg)
    quit(quitFailure)

  proc cstringArrayToSeq*(a: cstringArray, len: int): seq[string] =
    ## converts a ``cstringArray`` to a ``seq[string]``. `a` is supposed to be
    ## of length ``len``.
    newSeq(result, len)
    for i in 0..len-1: result[i] = $a[i]

  proc cstringArrayToSeq*(a: cstringArray): seq[string] =
    ## converts a ``cstringArray`` to a ``seq[string]``. `a` is supposed to be
    ## terminated by ``nil``.
    var L = 0
    while a[L] != nil: inc(L)
    result = cstringArrayToSeq(a, L)

  # ----------------------------------------------------------------------------

  include "system/excpt"

  # we cannot compile this with stack tracing on
  # as it would recurse endlessly!
  include "system/arithm"
  {.pop.} # stack trace
  include "system/dyncalls"
  include "system/sets"

  const
    GenericSeqSize = (2 * sizeof(int))
    
  proc reprAny(p: pointer, typ: PNimType): string {.compilerRtl.}

  proc getDiscriminant(aa: Pointer, n: ptr TNimNode): int =
    assert(n.kind == nkCase)
    var d: int
    var a = cast[TAddress](aa)
    case n.typ.size
    of 1: d = ze(cast[ptr int8](a +% n.offset)^)
    of 2: d = ze(cast[ptr int16](a +% n.offset)^)
    of 4: d = int(cast[ptr int32](a +% n.offset)^)
    else: assert(false)
    return d

  proc selectBranch(aa: Pointer, n: ptr TNimNode): ptr TNimNode =
    var discr = getDiscriminant(aa, n)
    if discr <% n.len:
      result = n.sons[discr]
      if result == nil: result = n.sons[n.len]
      # n.sons[n.len] contains the ``else`` part (but may be nil)
    else:
      result = n.sons[n.len]

  include "system/systhread"
  include "system/mmdisp"
  include "system/sysstr"
  include "system/assign"
  include "system/repr"

  # we have to implement it here after gentostr for the cstrToNimStrDummy proc
  proc getCurrentExceptionMsg(): string =
    if excHandler == nil: return ""
    return $excHandler.exc.msg

  proc getCurrentException(): ref E_Base = 
    if excHandler != nil: 
      result = excHandler.exc

  {.push stack_trace: off.}
  when defined(endb):
    include "system/debugger"

  when defined(profiler):
    include "system/profiler"
  {.pop.} # stacktrace

elif defined(ecmaScript):
  include "system/ecmasys"
elif defined(NimrodVM):
  # Stubs for the GC interface:
  proc GC_disable() = nil
  proc GC_enable() = nil
  proc GC_fullCollect() = nil
  proc GC_setStrategy(strategy: TGC_Strategy) = nil
  proc GC_enableMarkAndSweep() = nil
  proc GC_disableMarkAndSweep() = nil
  proc GC_getStatistics(): string = return ""
  
  proc getOccupiedMem(): int = return -1
  proc getFreeMem(): int = return -1
  proc getTotalMem(): int = return -1
  
  proc cmp(x, y: string): int =
    if x == y: return 0
    if x < y: return -1
    return 1
    
  proc dealloc(p: pointer) = nil
  proc alloc(size: int): pointer = nil
  proc alloc0(size: int): pointer = nil
  proc realloc(p: Pointer, newsize: int): pointer = nil

  proc likely*(val : bool) : bool {.inline, nosideeffect.} =
    return val
  proc unlikely*(val : bool) : bool {.inline, nosideeffect.} =
    return val


{.pop.} # checks
{.pop.} # hints
