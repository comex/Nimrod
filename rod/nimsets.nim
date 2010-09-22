#
#
#           The Nimrod Compiler
#        (c) Copyright 2009 Andreas Rumpf
#
#    See the file "copying.txt", included in this
#    distribution, for details about the copyright.
#

# this unit handles Nimrod sets; it implements symbolic sets

import 
  ast, astalgo, trees, nversion, msgs, platform, bitsets, types, rnimsyn

proc toBitSet*(s: PNode, b: var TBitSet)
  # this function is used for case statement checking:
proc overlap*(a, b: PNode): bool
proc inSet*(s: PNode, elem: PNode): bool
proc someInSet*(s: PNode, a, b: PNode): bool
proc emptyRange*(a, b: PNode): bool
proc SetHasRange*(s: PNode): bool
  # returns true if set contains a range (needed by the code generator)
  # these are used for constant folding:
proc unionSets*(a, b: PNode): PNode
proc diffSets*(a, b: PNode): PNode
proc intersectSets*(a, b: PNode): PNode
proc symdiffSets*(a, b: PNode): PNode
proc containsSets*(a, b: PNode): bool
proc equalSets*(a, b: PNode): bool
proc cardSet*(s: PNode): BiggestInt
# implementation

proc inSet(s: PNode, elem: PNode): bool = 
  if s.kind != nkCurly: InternalError(s.info, "inSet")
  for i in countup(0, sonsLen(s) - 1): 
    if s.sons[i].kind == nkRange: 
      if leValue(s.sons[i].sons[0], elem) and
          leValue(elem, s.sons[i].sons[1]): 
        return true
    else: 
      if sameValue(s.sons[i], elem): 
        return true
  result = false

proc overlap(a, b: PNode): bool = 
  if a.kind == nkRange: 
    if b.kind == nkRange: 
      result = leValue(a.sons[0], b.sons[1]) and
          leValue(b.sons[1], a.sons[1]) or
          leValue(a.sons[0], b.sons[0]) and leValue(b.sons[0], a.sons[1])
    else: 
      result = leValue(a.sons[0], b) and leValue(b, a.sons[1])
  else: 
    if b.kind == nkRange: 
      result = leValue(b.sons[0], a) and leValue(a, b.sons[1])
    else: 
      result = sameValue(a, b)

proc SomeInSet(s: PNode, a, b: PNode): bool = 
  # checks if some element of a..b is in the set s
  if s.kind != nkCurly: InternalError(s.info, "SomeInSet")
  for i in countup(0, sonsLen(s) - 1): 
    if s.sons[i].kind == nkRange: 
      if leValue(s.sons[i].sons[0], b) and leValue(b, s.sons[i].sons[1]) or
          leValue(s.sons[i].sons[0], a) and leValue(a, s.sons[i].sons[1]): 
        return true
    else: 
      # a <= elem <= b
      if leValue(a, s.sons[i]) and leValue(s.sons[i], b): 
        return true
  result = false

proc toBitSet(s: PNode, b: var TBitSet) = 
  var first, j: BiggestInt
  first = firstOrd(s.typ.sons[0])
  bitSetInit(b, int(getSize(s.typ)))
  for i in countup(0, sonsLen(s) - 1): 
    if s.sons[i].kind == nkRange: 
      j = getOrdValue(s.sons[i].sons[0])
      while j <= getOrdValue(s.sons[i].sons[1]): 
        BitSetIncl(b, j - first)
        inc(j)
    else: 
      BitSetIncl(b, getOrdValue(s.sons[i]) - first)
  
proc ToTreeSet(s: TBitSet, settype: PType, info: TLineInfo): PNode = 
  var 
    a, b, e, first: BiggestInt # a, b are interval borders
    elemType: PType
    n: PNode
  elemType = settype.sons[0]
  first = firstOrd(elemType)
  result = newNodeI(nkCurly, info)
  result.typ = settype
  result.info = info
  e = 0
  while e < high(s) * elemSize: 
    if bitSetIn(s, e): 
      a = e
      b = e
      while true: 
        Inc(b)
        if (b > high(s) * elemSize) or not bitSetIn(s, b): break 
      Dec(b)
      if a == b: 
        addSon(result, newIntTypeNode(nkIntLit, a + first, elemType))
      else: 
        n = newNodeI(nkRange, info)
        n.typ = elemType
        addSon(n, newIntTypeNode(nkIntLit, a + first, elemType))
        addSon(n, newIntTypeNode(nkIntLit, b + first, elemType))
        addSon(result, n)
      e = b
    Inc(e)

type 
  TSetOP = enum 
    soUnion, soDiff, soSymDiff, soIntersect

proc nodeSetOp(a, b: PNode, op: TSetOp): PNode = 
  var x, y: TBitSet
  toBitSet(a, x)
  toBitSet(b, y)
  case op
  of soUnion: BitSetUnion(x, y)
  of soDiff: BitSetDiff(x, y)
  of soSymDiff: BitSetSymDiff(x, y)
  of soIntersect: BitSetIntersect(x, y)
  result = toTreeSet(x, a.typ, a.info)

proc unionSets(a, b: PNode): PNode = 
  result = nodeSetOp(a, b, soUnion)

proc diffSets(a, b: PNode): PNode = 
  result = nodeSetOp(a, b, soDiff)

proc intersectSets(a, b: PNode): PNode = 
  result = nodeSetOp(a, b, soIntersect)

proc symdiffSets(a, b: PNode): PNode = 
  result = nodeSetOp(a, b, soSymDiff)

proc containsSets(a, b: PNode): bool = 
  var x, y: TBitSet
  toBitSet(a, x)
  toBitSet(b, y)
  result = bitSetContains(x, y)

proc equalSets(a, b: PNode): bool = 
  var x, y: TBitSet
  toBitSet(a, x)
  toBitSet(b, y)
  result = bitSetEquals(x, y)

proc cardSet(s: PNode): BiggestInt = 
  # here we can do better than converting it into a compact set
  # we just count the elements directly
  result = 0
  for i in countup(0, sonsLen(s) - 1): 
    if s.sons[i].kind == nkRange: 
      result = result + getOrdValue(s.sons[i].sons[1]) -
          getOrdValue(s.sons[i].sons[0]) + 1
    else: 
      Inc(result)
  
proc SetHasRange(s: PNode): bool = 
  if s.kind != nkCurly: InternalError(s.info, "SetHasRange")
  for i in countup(0, sonsLen(s) - 1): 
    if s.sons[i].kind == nkRange: 
      return true
  result = false

proc emptyRange(a, b: PNode): bool = 
  result = not leValue(a, b)  # a > b iff not (a <= b)
  