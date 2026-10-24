import Std.Data.HashMap
import Std.Data.HashSet
import SwissTable
import Lean.Elab.Command

/-!
# Semantics that parity cannot see

`#guard` tests of which key and value an operation keeps, of one iteration order for every
traversal, and of the scoping of the `~m` notation. Every check compares with Std where Std's
behaviour does not depend on the layout. Most of them restate Std lemmas (`getKey?_insert`,
`getKey?_union`, `getKey?_inter`, `getKey?_modify`, `fold_eq_foldl_toList`, ...), so they mainly
catch a wrong reading of the contract early, in a new core, before a proof fails.
-/

namespace SwissTableTest.Semantics

structure K where
  key : Nat
  tag : Nat
  deriving Repr

instance : BEq K := ⟨fun a b => a.key == b.key⟩
instance : Hashable K := ⟨fun a => hash a.key⟩

def tagOf (o : Option K) : Option Nat := o.map (·.tag)

abbrev OM := SwissTable.HashMap K Nat
abbrev SM := Std.HashMap K Nat

def k (n t : Nat) : K := ⟨n, t⟩

/-! ## insert replaces key and value; insertIfNew keeps both -/
#guard
  let m : OM := (∅ : OM).insert (k 1 0) 10 |>.insert (k 1 1) 11
  let s : SM := (∅ : SM).insert (k 1 0) 10 |>.insert (k 1 1) 11
  tagOf (m.getKey? (k 1 9)) == some 1 && m[k 1 9]? == some 11 &&
  tagOf (m.getKey? (k 1 9)) == tagOf (s.getKey? (k 1 9)) && m[k 1 9]? == s[k 1 9]? && m.size == 1
#guard
  let m : OM := (∅ : OM).insert (k 1 0) 10 |>.insertIfNew (k 1 1) 11
  let s : SM := (∅ : SM).insert (k 1 0) 10 |>.insertIfNew (k 1 1) 11
  tagOf (m.getKey? (k 1 9)) == some 0 && m[k 1 9]? == some 10 &&
  tagOf (m.getKey? (k 1 9)) == tagOf (s.getKey? (k 1 9))
-- containsThenInsert / getThenInsertIfNew?
#guard
  let m : OM := (∅ : OM).insert (k 1 0) 10
  let (b, m') := m.containsThenInsert (k 1 1) 11
  b && tagOf (m'.getKey? (k 1 9)) == some 1 && m'[k 1 9]? == some 11
#guard
  let m : OM := (∅ : OM).insert (k 1 0) 10
  let (o, m') := m.getThenInsertIfNew? (k 1 1) 11
  o == some 10 && tagOf (m'.getKey? (k 1 9)) == some 0 && m'[k 1 9]? == some 10
-- modify and alter (`some`) replace the stored key by the argument key, as on Std
-- (`Const.modifyKey` is `replaceEntry`, `Const.alterKey` is `insertEntry`)
#guard
  let m : OM := (∅ : OM).insert (k 1 0) 10 |>.modify (k 1 1) (· + 1)
  let s : SM := (∅ : SM).insert (k 1 0) 10 |>.modify (k 1 1) (· + 1)
  tagOf (m.getKey? (k 1 9)) == some 1 && m[k 1 9]? == some 11 &&
    tagOf (m.getKey? (k 1 9)) == tagOf (s.getKey? (k 1 9)) && m[k 1 9]? == s[k 1 9]?
#guard
  let m : OM := (∅ : OM).insert (k 1 0) 10 |>.alter (k 1 1) (fun o => o.map (· + 1))
  let s : SM := (∅ : SM).insert (k 1 0) 10 |>.alter (k 1 1) (fun o => o.map (· + 1))
  tagOf (m.getKey? (k 1 9)) == some 1 && m[k 1 9]? == some 11 &&
    tagOf (m.getKey? (k 1 9)) == tagOf (s.getKey? (k 1 9)) && m[k 1 9]? == s[k 1 9]?
-- modify and alter on a missing key
#guard
  let m : OM := (∅ : OM).insert (k 1 0) 10 |>.modify (k 2 1) (· + 1)
  m.size == 1 && m[k 2 9]? == none && tagOf (m.getKey? (k 1 9)) == some 0
#guard
  let m : OM := (∅ : OM).insert (k 1 0) 10 |>.alter (k 2 1) (fun _ => some 20)
  m.size == 2 && m[k 2 9]? == some 20 && tagOf (m.getKey? (k 2 9)) == some 1
#guard
  let m : OM := (∅ : OM).insert (k 1 0) 10 |>.alter (k 1 1) (fun _ => none)
  m.isEmpty && m[k 1 9]? == none

/-! ## HashSet.insert keeps the old element -/
#guard
  let m : SwissTable.HashSet K := (∅ : SwissTable.HashSet K).insert (k 1 0) |>.insert (k 1 1)
  let s : Std.HashSet K := (∅ : Std.HashSet K).insert (k 1 0) |>.insert (k 1 1)
  tagOf (m.get? (k 1 9)) == some 0 && tagOf (m.get? (k 1 9)) == tagOf (s.get? (k 1 9))

/-! ## union is right-biased (keys and values), in both size branches -/
def small1 : List (K × Nat) := [(k 1 0, 10), (k 2 0, 20)]
def big2 : List (K × Nat) := [(k 1 1, 11), (k 3 1, 31), (k 4 1, 41)]
def big1 : List (K × Nat) := [(k 1 0, 10), (k 2 0, 20), (k 5 0, 50)]
def small2 : List (K × Nat) := [(k 1 1, 11)]

def agree (m : OM) (s : SM) : Bool :=
  (List.range 7).all fun i =>
    tagOf (m.getKey? (k i 9)) == tagOf (s.getKey? (k i 9)) && m[k i 9]? == s[k i 9]?

-- |m₁| ≤ |m₂|
#guard
  let m := (SwissTable.HashMap.ofList small1 : OM) ∪ SwissTable.HashMap.ofList big2
  let s := (Std.HashMap.ofList small1 : SM) ∪ Std.HashMap.ofList big2
  tagOf (m.getKey? (k 1 9)) == some 1 && m[k 1 9]? == some 11 && agree m s && m.size == 4
-- |m₁| > |m₂|
#guard
  let m := (SwissTable.HashMap.ofList big1 : OM) ∪ SwissTable.HashMap.ofList small2
  let s := (Std.HashMap.ofList big1 : SM) ∪ Std.HashMap.ofList small2
  tagOf (m.getKey? (k 1 9)) == some 1 && m[k 1 9]? == some 11 && agree m s && m.size == 3

/-! ## inter keeps m₁'s entries (keys and values), in both size branches -/
#guard
  let m := (SwissTable.HashMap.ofList small1 : OM) ∩ SwissTable.HashMap.ofList big2
  let s := (Std.HashMap.ofList small1 : SM) ∩ Std.HashMap.ofList big2
  tagOf (m.getKey? (k 1 9)) == some 0 && m[k 1 9]? == some 10 && agree m s && m.size == 1
#guard
  let m := (SwissTable.HashMap.ofList big1 : OM) ∩ SwissTable.HashMap.ofList small2
  let s := (Std.HashMap.ofList big1 : SM) ∩ Std.HashMap.ofList small2
  tagOf (m.getKey? (k 1 9)) == some 0 && m[k 1 9]? == some 10 && agree m s && m.size == 1

/-! ## diff keeps m₁'s entries, in both size branches -/
#guard
  let m := (SwissTable.HashMap.ofList small1 : OM) \ SwissTable.HashMap.ofList big2
  let s := (Std.HashMap.ofList small1 : SM) \ Std.HashMap.ofList big2
  tagOf (m.getKey? (k 2 9)) == some 0 && agree m s && m.size == 1
#guard
  let m := (SwissTable.HashMap.ofList big1 : OM) \ SwissTable.HashMap.ofList small2
  let s := (Std.HashMap.ofList big1 : SM) \ Std.HashMap.ofList small2
  agree m s && m.size == 2

/-! ## ofList / ofArray / insertMany: last wins (key and value) -/
def dup : List (K × Nat) := [(k 1 0, 10), (k 2 0, 20), (k 1 1, 11), (k 1 2, 12)]
#guard
  let m : OM := SwissTable.HashMap.ofList dup
  tagOf (m.getKey? (k 1 9)) == some 2 && m[k 1 9]? == some 12 &&
    agree m (Std.HashMap.ofList dup) && m.size == 2
#guard agree (SwissTable.HashMap.ofArray dup.toArray) (Std.HashMap.ofArray dup.toArray)
#guard agree ((SwissTable.HashMap.ofList [(k 1 5, 0)] : OM).insertMany dup)
  ((Std.HashMap.ofList [(k 1 5, 0)] : SM).insertMany dup)
#guard agree ((SwissTable.HashMap.ofList [(k 1 5, 0)] : OM).insertMany dup.toArray)
  ((Std.HashMap.ofList [(k 1 5, 0)] : SM).insertMany dup.toArray)

/-! ## HashSet.ofList / ofArray / insertMany: first wins; unitOfList too -/
def dupS : List K := [k 1 0, k 2 0, k 1 1, k 1 2]
#guard
  let m : SwissTable.HashSet K := SwissTable.HashSet.ofList dupS
  let s : Std.HashSet K := Std.HashSet.ofList dupS
  tagOf (m.get? (k 1 9)) == some 0 && tagOf (m.get? (k 1 9)) == tagOf (s.get? (k 1 9)) &&
    m.size == 2
#guard
  let m : SwissTable.HashSet K := (SwissTable.HashSet.ofList [k 1 7]).insertMany dupS
  let s : Std.HashSet K := (Std.HashSet.ofList [k 1 7]).insertMany dupS
  tagOf (m.get? (k 1 9)) == some 7 && tagOf (m.get? (k 1 9)) == tagOf (s.get? (k 1 9))
#guard
  let m : SwissTable.HashSet K := (∅ : SwissTable.HashSet K).insertMany dupS.toArray
  tagOf (m.get? (k 1 9)) == some 0
#guard
  let m := SwissTable.HashMap.unitOfList dupS
  let s := Std.HashMap.unitOfList dupS
  tagOf (m.getKey? (k 1 9)) == some 0 && tagOf (m.getKey? (k 1 9)) == tagOf (s.getKey? (k 1 9))
#guard
  let m := SwissTable.HashMap.unitOfArray dupS.toArray
  tagOf (m.getKey? (k 1 9)) == some 0
-- HashSet union / inter keys (union: Std's HashSet.union is HashMap.union of Unit maps)
#guard
  let a : SwissTable.HashSet K := .ofList [k 1 0, k 2 0]
  let b : SwissTable.HashSet K := .ofList [k 1 1, k 3 1, k 4 1]
  let sa : Std.HashSet K := .ofList [k 1 0, k 2 0]
  let sb : Std.HashSet K := .ofList [k 1 1, k 3 1, k 4 1]
  tagOf ((a ∪ b).get? (k 1 9)) == tagOf ((sa ∪ sb).get? (k 1 9)) &&
  tagOf ((b ∪ a).get? (k 1 9)) == tagOf ((sb ∪ sa).get? (k 1 9)) &&
  tagOf ((a ∩ b).get? (k 1 9)) == tagOf ((sa ∩ sb).get? (k 1 9)) &&
  tagOf ((b ∩ a).get? (k 1 9)) == tagOf ((sb ∩ sa).get? (k 1 9))

/-! ## one iteration order for every traversal -/
def bigM : SwissTable.HashMap Nat Nat :=
  let t := (List.range 200).foldl
    (fun (acc : SwissTable.HashMap Nat Nat) i => acc.insert (i * 7 % 200) i) ∅
  ((t.erase 3).erase 50).insert 3 1000

def recFold (m : SwissTable.HashMap Nat Nat) : List (Nat × Nat) :=
  (m.fold (fun acc k v => (k, v) :: acc) []).reverse
def recFoldM (m : SwissTable.HashMap Nat Nat) : List (Nat × Nat) :=
  ((m.foldM (m := StateM (List (Nat × Nat))) (fun _ k v => modify ((k, v) :: ·)) ()).run
    []).2.reverse
def recForM (m : SwissTable.HashMap Nat Nat) : List (Nat × Nat) :=
  ((m.forM (m := StateM (List (Nat × Nat))) (fun k v => modify ((k, v) :: ·))).run []).2.reverse
def recForIn (m : SwissTable.HashMap Nat Nat) : List (Nat × Nat) := Id.run do
  let mut acc := []
  for (k, v) in m do
    acc := (k, v) :: acc
  return acc.reverse
def recForInBreak (m : SwissTable.HashMap Nat Nat) (n : Nat) : List (Nat × Nat) := Id.run do
  let mut acc := []
  for (k, v) in m do
    if acc.length == n then break
    acc := (k, v) :: acc
  return acc.reverse
def recForMClass (m : SwissTable.HashMap Nat Nat) : List (Nat × Nat) :=
  ((ForM.forM (m := StateM (List (Nat × Nat))) m (fun p => modify (p :: ·))).run []).2.reverse
def recIter (m : SwissTable.HashMap Nat Nat) : List (Nat × Nat) := Id.run do
  let mut acc := []
  for p in m.iter do
    acc := p :: acc
  return acc.reverse
-- `any` stops at the first hit: the first entry satisfying p is the first in toList
def firstAny (m : SwissTable.HashMap Nat Nat) (p : Nat → Bool) : Option Nat :=
  (m.toList.find? (fun e => p e.1)).map (·.1)

#guard bigM.size == 199
#guard recFold bigM == bigM.toList
#guard recFoldM bigM == bigM.toList
#guard recForM bigM == bigM.toList
#guard recForMClass bigM == bigM.toList
#guard recForIn bigM == bigM.toList
#guard recForInBreak bigM 17 == bigM.toList.take 17
#guard recIter bigM == bigM.toList
#guard bigM.iter.toList == bigM.toList
#guard bigM.keysIter.toList == bigM.keys
#guard bigM.valuesIter.toList == bigM.values
#guard bigM.keys == bigM.toList.map Prod.fst
#guard bigM.values == bigM.toList.map Prod.snd
#guard bigM.toArray.toList == bigM.toList
#guard bigM.keysArray.toList == bigM.keys
#guard bigM.valuesArray.toList == bigM.values
#guard (bigM.filter fun k _ => k % 3 == 0).toList == bigM.toList.filter (fun e => e.1 % 3 == 0)
#guard (bigM.map fun _ v => v + 1).toList == bigM.toList.map (fun e => (e.1, e.2 + 1))
#guard bigM.toList.mergeSort (fun a b => a.1 ≤ b.1) ==
  ((List.range 200).foldl (fun (acc : Std.HashMap Nat Nat) i => acc.insert (i * 7 % 200) i) ∅
    |>.erase 3 |>.erase 50 |>.insert 3 1000).toList.mergeSort (fun a b => a.1 ≤ b.1)
-- HashSet traversals
def bigS : SwissTable.HashSet Nat := .ofList ((List.range 150).map (· * 11 % 150))
#guard bigS.size == 150
#guard bigS.toArray.toList == bigS.toList
#guard (bigS.fold (fun acc a => a :: acc) []).reverse == bigS.toList
#guard bigS.iter.toList == bigS.toList
#guard (Id.run do
    let mut acc := []
    for a in bigS do acc := a :: acc
    return acc.reverse) == bigS.toList
#guard bigS.toList == bigS.inner.keys

#guard (∅ : SwissTable.HashMap Nat Nat).getD 3 7 == 7

/-! ## `~m` is scoped, as in Std

Parity compares the notation's parser description, not whether it is `scoped`. -/

open Lean Elab Command in
/-- Whether `s` parses as a term with the notations active at this point. -/
def parsesAsTerm (s : String) : CommandElabM Bool :=
  return (Parser.runParserCategory (← getEnv) `term s).isOk

run_cmd do
  if (← parsesAsTerm "a ~m b") then
    throwError "`~m` parses without `open SwissTable.HashMap` or `open SwissTable.HashSet`"

section
open SwissTable.HashMap
run_cmd do
  unless (← parsesAsTerm "a ~m b") do throwError "`~m` does not parse under `open SwissTable.HashMap`"
example (a b : SwissTable.HashMap Nat Nat) : (a ~m b) = SwissTable.HashMap.Equiv a b := rfl
end

section
open SwissTable.HashSet
run_cmd do
  unless (← parsesAsTerm "a ~m b") do throwError "`~m` does not parse under `open SwissTable.HashSet`"
example (a b : SwissTable.HashSet Nat) : (a ~m b) = SwissTable.HashSet.Equiv a b := rfl
end

end SwissTableTest.Semantics
