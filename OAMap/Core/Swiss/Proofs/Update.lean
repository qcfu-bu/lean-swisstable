module

public import OAMap.Core.Swiss.Proofs.Query

/-!
# Swiss core proofs, part 7: insert, insertIfNew, erase, alter, modify (contract 12–16)

A proof file of the SwissTable core (`OAMap/Core/Swiss/Table.lean`, "Proof structure"). Its
owner edits only this file: the proofs, and any private helper lemmas or definitions. The
contract lemmas (`docs/ARCHITECTURE.md` §3.3) are fixed word for word; the helpers below are the
suggested route and may be changed or dropped (no other file uses them).

Every operation takes one of two paths (machine words below `2 ^ 31` slots, `Nat` indices beyond),
and on each path ends in one of the writes of `Proofs/Write.lean`, whose entries are known:

* a hit (`WF.insProbeU_hit`, `WF.insSlotN_hit`, ...): the key and value of the slot replaced,
  `replaceEntry` (`WF.entries_kvN_replace`), which is `insertEntry` since the key is present;
  `modify` and `alter` write the placeholder value first (`Array.set_set`/`Array.uset_eq_set`
  make it one write); an erasure is `eraseKey` (`WF.entries_eraseN_eraseKey`);
* a new key (`WF.insProbeU_new`, `WF.fast_new`, `WF.insSlotN_new`, ...): a `NewSlot`, absent for
  lawful instances, so `insertEntry` is a cons; the write adds the entry
  (`WF.entries_newN_perm`), directly or after `reserveInsert` rebuilt the table
  (`reserveTable_perm`, then `insertFresh` with `WF.findFree_slot`).

The machine-word writes are the `Nat` ones through `setCtrl_eq_setCtrlN`, `Array.uset_eq_set`,
`WF.geom` and `homeU_toNat`. The values the list operations read (`getValue?`) come from the hit
(`WF.getEntry?_hit`).
-/

@[expose] public section

universe u v w w'

open Std.Internal.List

namespace OAMap.Core

namespace Swiss

variable {α : Type u} {β : Type v}

section Writes

variable [BEq α] [Hashable α]

/-- *Suggested route.* `insertFresh` adds its entry. -/
theorem insertFresh_perm (t : Table α β) (a : α) (b : β) (h : FreshPre t.slots t.growthLeft a) :
    (insertFresh t a b h).slots.entries.Perm (⟨a, b⟩ :: t.slots.entries) := by
  sorry

/-- *Suggested route.* `reserveInsert` adds its entry. -/
theorem reserveInsert_perm (t : Table α β) (a : α) (b : β)
    (h : ∀ [EquivBEq α] [LawfulHashable α], t.slots.Absent a) :
    (reserveInsert t a b h).slots.entries.Perm (⟨a, b⟩ :: t.slots.entries) := by
  sorry

/-- *Suggested route.* A new key written on machine words adds its entry. -/
theorem insertNewU_perm (t : Table α β) (a : α) (b : β) (q : UInt64) (i : USize)
    (hs : smallMask t.mask = true) (h : NewSlot t.slots t.shift a q i.toNat) :
    (insertNewU t a b q i hs h).slots.entries.Perm (⟨a, b⟩ :: t.slots.entries) := by
  sorry

/-- *Suggested route.* A new key written on `Nat` indices adds its entry. -/
theorem insertNewN_perm (t : Table α β) (a : α) (b : β) (q : UInt64) (i : Nat)
    (h : NewSlot t.slots t.shift a q i) :
    (insertNewN t a b q i h).slots.entries.Perm (⟨a, b⟩ :: t.slots.entries) := by
  sorry

/-- *Suggested route.* Erasing the hit for `a` on machine words is `eraseKey`. -/
theorem eraseAtU_eraseKey (t : Table α β) (i : USize) (hs : smallMask t.mask = true)
    (hi : t.slots.IsFull i.toNat) {a : α} (hit : t.slots.Hit t.shift a i.toNat) [EquivBEq α]
    [LawfulHashable α] : (eraseAtU t i hs hi).slots.entries = eraseKey a t.slots.entries := by
  sorry

/-- *Suggested route.* Erasing the hit for `a` on `Nat` indices is `eraseKey`. -/
theorem eraseAtN_eraseKey (t : Table α β) (i : Nat) (hi : t.slots.IsFull i) {a : α}
    (hit : t.slots.Hit t.shift a i) [EquivBEq α] [LawfulHashable α] :
    (eraseAtN t i hi).slots.entries = eraseKey a t.slots.entries := by
  sorry

/-- *Suggested route.* `modifyAtU` is `Const.modifyKey`. -/
theorem modifyAtU_modifyKey (t : Table α β) (i : USize) (a : α) (f : β → β)
    (hs : smallMask t.mask = true) (hit : t.slots.Hit t.shift a i.toNat) [EquivBEq α]
    [LawfulHashable α] :
    (modifyAtU t i a f hs hit).slots.entries = Const.modifyKey a f t.slots.entries := by
  sorry

/-- *Suggested route.* `modifyAtN` is `Const.modifyKey`. -/
theorem modifyAtN_modifyKey (t : Table α β) (i : Nat) (a : α) (f : β → β)
    (hit : t.slots.Hit t.shift a i) [EquivBEq α] [LawfulHashable α] :
    (modifyAtN t i a f hit).slots.entries = Const.modifyKey a f t.slots.entries := by
  sorry

end Writes

end Swiss

namespace Table

open Swiss

variable {α : Type u} {β : Type v} {γ : Type w} {_ : BEq α} {_ : Hashable α}

theorem toListModel_insert [EquivBEq α] [LawfulHashable α] (t : Table α β) (a : α) (b : β) :
    (t.insert a b).toListModel.Perm (insertEntry a b t.toListModel) := sorry

theorem toListModel_insertIfNew [EquivBEq α] [LawfulHashable α] (t : Table α β) (a : α)
    (b : β) : (t.insertIfNew a b).toListModel.Perm (insertEntryIfNew a b t.toListModel) := sorry

theorem toListModel_erase [EquivBEq α] [LawfulHashable α] (t : Table α β) (a : α) :
    (t.erase a).toListModel.Perm (eraseKey a t.toListModel) := sorry

theorem toListModel_alter [EquivBEq α] [LawfulHashable α] (t : Table α β) (a : α)
    (f : Option β → Option β) :
    (t.alter a f).toListModel.Perm (Const.alterKey a f t.toListModel) := sorry

theorem toListModel_modify [EquivBEq α] [LawfulHashable α] (t : Table α β) (a : α)
    (f : β → β) : (t.modify a f).toListModel.Perm (Const.modifyKey a f t.toListModel) := sorry

end Table

end OAMap.Core
