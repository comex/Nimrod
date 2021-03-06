#
#
#           The Nimrod Compiler
#        (c) Copyright 2010 Andreas Rumpf
#
#    See the file "copying.txt", included in this
#    distribution, for details about the copyright.
#

# This module implements a generic doubled linked list.

type 
  PListEntry* = ref TListEntry
  TListEntry* = object of TObject
    prev*, next*: PListEntry

  TStrEntry* = object of TListEntry
    data*: string

  PStrEntry* = ref TStrEntry
  TLinkedList* = object       # for the "find" operation:
    head*, tail*: PListEntry
    Counter*: int

  TCompareProc* = proc (entry: PListEntry, closure: Pointer): bool

proc InitLinkedList*(list: var TLinkedList)
proc Append*(list: var TLinkedList, entry: PListEntry)
proc Prepend*(list: var TLinkedList, entry: PListEntry)
proc Remove*(list: var TLinkedList, entry: PListEntry)
proc InsertBefore*(list: var TLinkedList, pos, entry: PListEntry)
proc Find*(list: TLinkedList, fn: TCompareProc, closure: Pointer): PListEntry
proc AppendStr*(list: var TLinkedList, data: string)
proc IncludeStr*(list: var TLinkedList, data: string): bool
proc PrependStr*(list: var TLinkedList, data: string)
# implementation

proc InitLinkedList(list: var TLinkedList) = 
  list.Counter = 0
  list.head = nil
  list.tail = nil

proc Append(list: var TLinkedList, entry: PListEntry) = 
  Inc(list.counter)
  entry.next = nil
  entry.prev = list.tail
  if list.tail != nil: 
    assert(list.tail.next == nil)
    list.tail.next = entry
  list.tail = entry
  if list.head == nil: list.head = entry
  
proc newStrEntry(data: string): PStrEntry = 
  new(result)
  result.data = data

proc AppendStr(list: var TLinkedList, data: string) = 
  append(list, newStrEntry(data))

proc PrependStr(list: var TLinkedList, data: string) = 
  prepend(list, newStrEntry(data))

proc Contains*(list: TLinkedList, data: string): bool = 
  var it = list.head
  while it != nil: 
    if PStrEntry(it).data == data: 
      return true
    it = it.next

proc IncludeStr(list: var TLinkedList, data: string): bool = 
  if Contains(list, data): return true
  AppendStr(list, data)       # else: add to list

proc InsertBefore(list: var TLinkedList, pos, entry: PListEntry) = 
  assert(pos != nil)
  if pos == list.head: 
    prepend(list, entry)
  else: 
    Inc(list.counter)
    entry.next = pos
    entry.prev = pos.prev
    if pos.prev != nil: pos.prev.next = entry
    pos.prev = entry

proc Prepend(list: var TLinkedList, entry: PListEntry) = 
  Inc(list.counter)
  entry.prev = nil
  entry.next = list.head
  if list.head != nil: 
    assert(list.head.prev == nil)
    list.head.prev = entry
  list.head = entry
  if list.tail == nil: list.tail = entry
  
proc Remove(list: var TLinkedList, entry: PListEntry) = 
  Dec(list.counter)
  if entry == list.tail: 
    list.tail = entry.prev
  if entry == list.head: 
    list.head = entry.next
  if entry.next != nil: entry.next.prev = entry.prev
  if entry.prev != nil: entry.prev.next = entry.next
  
proc Find(list: TLinkedList, fn: TCompareProc, closure: Pointer): PListEntry = 
  result = list.head
  while result != nil: 
    if fn(result, closure): return 
    result = result.next
