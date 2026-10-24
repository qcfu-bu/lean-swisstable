import Std.Data.HashMap
import Std.Data.HashSet
import OAMap

/-!
# `#guard` tests for the functions that have no Std lemmas

`docs/ARCHITECTURE.md` §9.2. `HashMap.partition`, `values`, `valuesArray`, the `Repr` instances,
`HashSet.partition`, `HashSet.ofArray` and `Internal.numBuckets` are not pinned by any Std
statement, so their behaviour is checked here by `#guard`, which fails the build when a check
evaluates to `false`. Everything else is covered by the proofs and by parity.

The checks do not depend on the iteration order, which is the core's: they compare with Std's
maps through queries and sorted lists, and with the other traversals of the same map (`values`
enumerates the order of `toList`, §1). The only guards that depend on the selected core are in
the last section, marked to revisit at INTEG.

Owner: ITER, Wave 3.
-/

namespace OAMapTest.Unverified

/-- Keys that `==` and `hash` compare by `key` only, so a test can tell which of two equal keys a
map or set stores. -/
structure K where
  key : Nat
  tag : Nat

instance : BEq K := ⟨fun a b => a.key == b.key⟩
instance : Hashable K := ⟨fun a => hash a.key⟩

/-- Sorts entries by key, then value. -/
def sortE (l : List (Nat × Nat)) : List (Nat × Nat) :=
  l.mergeSort fun a b => a.1 < b.1 || (a.1 == b.1 && a.2 ≤ b.2)

/-- The keys the tests on small maps probe: all their keys, and some absent ones. -/
def probe : List Nat := List.range 12

/-- Entries with a repeated key (`2`): `ofList` keeps the last value, `21`. -/
def entries : List (Nat × Nat) := [(1, 10), (2, 20), (3, 30), (4, 40), (5, 50), (2, 21), (8, 80)]

def m : OAMap.HashMap Nat Nat := .ofList entries
def sm : Std.HashMap Nat Nat := .ofList entries

/-- A larger map, built by `insert`, with some keys erased. -/
def big : OAMap.HashMap Nat Nat :=
  let t := (List.range 300).foldl (fun (acc : OAMap.HashMap Nat Nat) i => acc.insert i (i * i)) ∅
  (t.erase 7).erase 100
def sbig : Std.HashMap Nat Nat :=
  let t := (List.range 300).foldl (fun (acc : Std.HashMap Nat Nat) i => acc.insert i (i * i)) ∅
  (t.erase 7).erase 100

def even (k _ : Nat) : Bool := k % 2 == 0

/-! ## `HashMap.values` and `HashMap.valuesArray` -/

#guard (∅ : OAMap.HashMap Nat Nat).values == []
#guard (∅ : OAMap.HashMap Nat Nat).valuesArray == #[]
#guard ((∅ : OAMap.HashMap Nat Nat).insert 1 2).values == [2]
#guard ((∅ : OAMap.HashMap Nat Nat).insert 1 2).valuesArray == #[2]
-- `values` and `valuesArray` enumerate the entries in the order of `toList`
#guard m.values == m.toList.map Prod.snd
#guard m.valuesArray == (m.toList.map Prod.snd).toArray
#guard big.values == big.toList.map Prod.snd
#guard big.valuesArray.toList == big.values
-- the same values as Std's (the last value for the repeated key)
#guard m.values.mergeSort == [10, 21, 30, 40, 50, 80]
#guard m.values.mergeSort == sm.values.mergeSort
#guard big.values.length == 298
#guard big.values.mergeSort == sbig.values.mergeSort
#guard (m.erase 2).values.mergeSort == [10, 30, 40, 50, 80]

/-! ## `HashMap.partition` -/

#guard probe.all fun k => (m.partition even).1[k]? == (sm.partition even).1[k]?
#guard probe.all fun k => (m.partition even).2[k]? == (sm.partition even).2[k]?
#guard sortE (m.partition even).1.toList == [(2, 21), (4, 40), (8, 80)]
#guard sortE (m.partition even).2.toList == [(1, 10), (3, 30), (5, 50)]
#guard (List.range 310).all fun k =>
  (big.partition even).1[k]? == (sbig.partition even).1[k]? &&
    (big.partition even).2[k]? == (sbig.partition even).2[k]?
#guard (big.partition even).1.size + (big.partition even).2.size == big.size
#guard (big.partition even).1.toList.all fun (k, v) => even k v
#guard (big.partition even).2.toList.all fun (k, v) => !even k v
#guard ((∅ : OAMap.HashMap Nat Nat).partition even).1.isEmpty
#guard ((∅ : OAMap.HashMap Nat Nat).partition even).2.isEmpty
#guard (m.partition fun _ _ => true).2.isEmpty && (m.partition fun _ _ => true).1.size == m.size
-- the stored key is kept (`insert` replaced `⟨1, 0⟩` by `⟨1, 1⟩`), as on Std
#guard
  let l : List (K × Nat) := [(⟨1, 0⟩, 1), (⟨1, 1⟩, 2), (⟨2, 0⟩, 3)]
  let p := (OAMap.HashMap.ofList l).partition fun _ v => v ≥ 2
  let sp := (Std.HashMap.ofList l).partition fun _ v => v ≥ 2
  (p.1.getKey? ⟨1, 9⟩).map (·.tag) == some 1 &&
    (p.1.getKey? ⟨1, 9⟩).map (·.tag) == (sp.1.getKey? ⟨1, 9⟩).map (·.tag) &&
    p.1[(⟨2, 9⟩ : K)]? == some 3 && p.2.isEmpty

/-! ## `Repr` -/

#guard toString (repr (∅ : OAMap.HashMap Nat Nat)) == "OAMap.HashMap.ofList []"
#guard toString (repr ((∅ : OAMap.HashMap Nat Nat).insert 1 2)) == "OAMap.HashMap.ofList [(1, 2)]"
#guard toString (repr (some ((∅ : OAMap.HashMap Nat Nat).insert 1 2))) ==
  "some (OAMap.HashMap.ofList [(1, 2)])"
#guard toString (repr m) == "OAMap.HashMap.ofList " ++ toString (repr m.toList)
-- Std's output, with `Std.` replaced by `OAMap.`
#guard toString (repr ((∅ : OAMap.HashMap Nat String).insert 1 "a")) ==
  (toString (repr ((∅ : Std.HashMap Nat String).insert 1 "a"))).replace "Std." "OAMap."
#guard toString (repr (some ((∅ : OAMap.HashMap Nat Nat).insert 1 2))) ==
  (toString (repr (some ((∅ : Std.HashMap Nat Nat).insert 1 2)))).replace "Std." "OAMap."
#guard toString (repr (∅ : OAMap.HashSet Nat)) == "OAMap.HashSet.ofList []"
#guard toString (repr ((∅ : OAMap.HashSet Nat).insert 1)) == "OAMap.HashSet.ofList [1]"
#guard toString (repr (some ((∅ : OAMap.HashSet Nat).insert 1))) ==
  "some (OAMap.HashSet.ofList [1])"
#guard toString (repr (OAMap.HashSet.ofList [1, 2, 3])) ==
  "OAMap.HashSet.ofList " ++ toString (repr (OAMap.HashSet.ofList [1, 2, 3]).toList)
#guard toString (repr (some ((∅ : OAMap.HashSet Nat).insert 1))) ==
  (toString (repr (some ((∅ : Std.HashSet Nat).insert 1)))).replace "Std." "OAMap."

/-! ## `HashSet.ofArray` -/

#guard (OAMap.HashSet.ofArray (#[] : Array Nat)).isEmpty
#guard (OAMap.HashSet.ofArray #[3, 1, 2, 1, 3]).size == 3
#guard (OAMap.HashSet.ofArray #[3, 1, 2, 1, 3]).toList.mergeSort == [1, 2, 3]
#guard probe.all fun k =>
  (OAMap.HashSet.ofArray #[3, 1, 2, 1, 3]).contains k ==
    (Std.HashSet.ofArray #[3, 1, 2, 1, 3]).contains k
#guard (OAMap.HashSet.ofArray ((List.range 200).toArray ++ (List.range 100).toArray)).size == 200
-- the first of several equal elements is the one kept, as on Std
#guard
  let a : Array K := #[⟨1, 0⟩, ⟨2, 0⟩, ⟨1, 1⟩, ⟨2, 1⟩]
  let s := OAMap.HashSet.ofArray a
  let ss := Std.HashSet.ofArray a
  (s.get? ⟨1, 9⟩).map (·.tag) == some 0 && (s.get? ⟨2, 9⟩).map (·.tag) == some 0 &&
    (s.get? ⟨1, 9⟩).map (·.tag) == (ss.get? ⟨1, 9⟩).map (·.tag) && s.size == 2
-- `ofArray` agrees with `ofList` on the same elements
#guard
  let a : Array K := #[⟨1, 0⟩, ⟨2, 0⟩, ⟨1, 1⟩, ⟨3, 4⟩]
  [1, 2, 3, 4].all fun k =>
    ((OAMap.HashSet.ofArray a).get? ⟨k, 9⟩).map (·.tag) ==
      ((OAMap.HashSet.ofList a.toList).get? ⟨k, 9⟩).map (·.tag)

/-! ## `HashSet.partition` -/

def s : OAMap.HashSet Nat := .ofList [1, 2, 3, 4, 5, 8, 2]
def ss : Std.HashSet Nat := .ofList [1, 2, 3, 4, 5, 8, 2]

#guard (s.partition (· % 2 == 0)).1.toList.mergeSort == [2, 4, 8]
#guard (s.partition (· % 2 == 0)).2.toList.mergeSort == [1, 3, 5]
#guard probe.all fun k =>
  (s.partition (· % 2 == 0)).1.contains k == (ss.partition (· % 2 == 0)).1.contains k &&
    (s.partition (· % 2 == 0)).2.contains k == (ss.partition (· % 2 == 0)).2.contains k
#guard ((∅ : OAMap.HashSet Nat).partition (· % 2 == 0)).1.isEmpty
#guard
  let t := OAMap.HashSet.ofList (List.range 250)
  (t.partition (· < 100)).1.size == 100 && (t.partition (· < 100)).2.size == 150
-- the stored element is kept, as on Std
#guard
  let l : List K := [⟨1, 0⟩, ⟨1, 1⟩, ⟨2, 0⟩]
  let p := (OAMap.HashSet.ofList l).partition fun e => e.key == 1
  let sp := (Std.HashSet.ofList l).partition fun e => e.key == 1
  (p.1.get? ⟨1, 9⟩).map (·.tag) == some 0 &&
    (p.1.get? ⟨1, 9⟩).map (·.tag) == (sp.1.get? ⟨1, 9⟩).map (·.tag) &&
    p.2.contains ⟨2, 9⟩ && p.2.size == 1

/-! ## `Internal.numBuckets` -/

-- the set's count is its map's
#guard OAMap.HashSet.Internal.numBuckets s == OAMap.HashMap.Internal.numBuckets s.inner
#guard OAMap.HashSet.Internal.numBuckets (∅ : OAMap.HashSet Nat) ==
  OAMap.HashMap.Internal.numBuckets (∅ : OAMap.HashMap Nat Unit)

/-! ### Revisit at INTEG

`numBuckets` is the core's own count, and the list-backed reference core
`OAMap.Core.ListRef` returns `1` for every table, so only positivity is checked. Std's is the
length of its bucket array, a power of two: `16` for `∅`, `1` for `emptyWithCapacity 0`, `256`
for `emptyWithCapacity 100`, doubling as the map grows (`32` from 13 entries inserted into `∅`).
When the real core is selected, add guards on its exact values (for instance `numBuckets ∅`,
`numBuckets (emptyWithCapacity 100)`, and `numBuckets big ≥ big.size` for an open-addressing
table). -/

#guard 0 < OAMap.HashMap.Internal.numBuckets (∅ : OAMap.HashMap Nat Nat)
#guard 0 < OAMap.HashMap.Internal.numBuckets big
#guard 0 < OAMap.HashSet.Internal.numBuckets s

end OAMapTest.Unverified
