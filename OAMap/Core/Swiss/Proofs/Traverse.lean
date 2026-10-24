module

public import OAMap.Core.Swiss.Table
public import Std.Data.Internal.List.Associative

/-!
# Swiss core proofs, part 8: filter, filterMap, map and the traversals (contract 17–22)

A proof file of the SwissTable core (`OAMap/Core/Swiss/Table.lean`, "Proof structure"). Its
owner edits only this file: the proofs, and any private helper lemmas or definitions. The
contract lemmas (`docs/ARCHITECTURE.md` §3.3) are fixed word for word; the helpers below are the
suggested route and may be changed or dropped (no other file uses them). All six lemmas are
**U**: no lawfulness, only the invariant's unconditional part (`WF.shape`, `WF.size_eq`).

* **The traversals** (`foldM`, `foldRev`, `forIn`) go a group at a time over the `matchFull` mask
  of each group, lowest lane first (`foldRev`: highest lane first, last group first); the groups
  at `0, 8, …, cap - 8` never wrap, so byte `j` of the group at `p` is slot `p + j`
  (`byte_ctrlWord'`, `byte_ctrlWordN`) and a lane's flag says the slot is full
  (`flag_matchFull`); `lowestLane_spec` and `flag_clearLowest` walk the lanes in order. So each
  loop folds over `entryAt` of the slots in (reverse) order: `(List.range cap).filterMap entryAt`
  is the model. The machine-word loops are the `Nat` ones (`foldMLoop_eq_foldMLoopN`, ...).
  The unallocated table has no group to visit (`cap = 0`).
* **filter** erases the rejected entries in slot order (`filterLoop`, `eraseAtN`: pointwise, an
  erasure removes exactly its slot, `entryAt_eraseN` of `Proofs/Write.lean`).
* **filterMap** is `filterMap_entries_raw` of `Proofs/Bulk.lean`, or the unallocated table when
  `firstSome` finds nothing (`firstSome_none`: every entry is rejected).
* **map** rewrites the value of each full slot (`firstFull_spec`, `Array.getElem_mapFinIdx`,
  `entryAt_valN`-like reasoning on the new value array).
-/

@[expose] public section

universe u v w w'

open Std.Internal.List

namespace OAMap.Core

namespace Swiss

variable {α : Type u} {β : Type v} {γ : Type w}

section Helpers

variable [BEq α] [Hashable α]

/-- *Suggested route.* An erasure on `Nat` indices removes exactly its slot. -/
theorem eraseAtN_entryAt (t : Table α β) (i : Nat) (hi : t.slots.IsFull i) {j : Nat}
    (hj : j < t.slots.cap) :
    (eraseAtN t i hi).slots.entryAt j = if j = i then none else t.slots.entryAt j := by
  sorry

/-- *Suggested route.* `filterLoop` from slot `i`: the slots below `i` are untouched, the others
filtered. -/
theorem filterLoop_entries (f : α → β → Bool) (cap i : Nat) (t : Table α β)
    (hc : cap = t.ctrl.size - 8) (hi : i ≤ cap) :
    (filterLoop f cap i t hc).slots.entries =
      (List.range cap).filterMap fun j =>
        if j < i then t.slots.entryAt j else (t.slots.entryAt j).filter fun e => f e.1 e.2 := by
  sorry

/-- *Suggested route.* The machine-word fold is the one on `Nat` indices. -/
theorem foldMLoop_eq_foldMLoopN {ε : Type w} {m : Type w → Type w'} [Monad m]
    (f : ε → α → β → m ε) {ctrl : ByteArray} {keys : Array α} {vals : Array β} {cap p : USize}
    {fm : UInt64} {acc : ε} {hF : FoldU ctrl keys vals cap} {hp : GroupAt cap p}
    {hm : IsMask fm} {hF' : FoldN ctrl keys vals cap.toNat} {hp' : GroupAtN cap.toNat p.toNat} :
    foldMLoop f ctrl keys vals cap p fm acc hF hp hm =
      foldMLoopN f ctrl keys vals cap.toNat p.toNat fm acc hF' hp' hm := by
  sorry

end Helpers

end Swiss

namespace Table

open Swiss

variable {α : Type u} {β : Type v} {γ : Type w} {_ : BEq α} {_ : Hashable α}

theorem toListModel_filter (t : Table α β) (f : α → β → Bool) :
    (t.filter f).toListModel.Perm (t.toListModel.filter fun p => f p.1 p.2) := sorry

theorem toListModel_filterMap (t : Table α β) (f : α → β → Option γ) :
    (t.filterMap f).toListModel.Perm
      (t.toListModel.filterMap fun p => (f p.1 p.2).map (⟨p.1, ·⟩)) := sorry

theorem toListModel_map (t : Table α β) (f : α → β → γ) :
    (t.map f).toListModel.Perm (t.toListModel.map fun p => ⟨p.1, f p.1 p.2⟩) := sorry

theorem foldM_eq_foldlM_toListModel {ε : Type w} {m : Type w → Type w'} [Monad m]
    [LawfulMonad m] (t : Table α β) (f : ε → α → β → m ε) (init : ε) :
    t.foldM f init = t.toListModel.foldlM (fun d e => f d e.1 e.2) init := sorry

theorem foldRev_eq_foldr_toListModel {ε : Type w} (t : Table α β) (f : ε → α → β → ε)
    (init : ε) : t.foldRev f init = t.toListModel.foldr (fun e d => f d e.1 e.2) init := sorry

theorem forIn_eq_forIn_toListModel {ε : Type w} {m : Type w → Type w'} [Monad m]
    [LawfulMonad m] (t : Table α β) (f : α → β → ε → m (ForInStep ε)) (init : ε) :
    t.forIn f init = ForIn.forIn t.toListModel init (fun e d => f e.1 e.2 d) := sorry

end Table

end OAMap.Core
