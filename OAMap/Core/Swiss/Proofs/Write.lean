module

public import OAMap.Core.Swiss.Build
public import OAMap.Core.Swiss.Proofs.Probe
public import Std.Data.Internal.List.Associative

/-!
# Swiss core proofs, part 4: single-slot writes, and the rebuilt table

A proof file of the SwissTable core (`OAMap/Core/Swiss/Table.lean`, "Proof structure"). Its
owner edits only this file: the proofs, and any private helper lemmas or definitions. The
statements are fixed: `Table.lean` and the later proof files use them.

* **The invariant after each write of `Table.lean`** (stated on the code's terms, machine-word and
  `Nat` forms): a value (`WF.replaceVals`), the key of a hit (`WF.keyU`, `WF.keyN`: `==` keys have
  the same hash and tag under lawfulness, and `TagInv` holds because the hit's byte is the tag of
  `a`), a new key at the slot of a `NewSlot` (`WF.newU_empty`, `WF.newU_del`, `WF.newN_empty`,
  `WF.newN_del`, `WF.freshU`, `WF.freshN`: `TagInv` by the tag written, `ProbeInv` by
  `FreeSlot.reach`, `Distinct` by `NewSlot.absent`, the counts by the EMPTY/DELETED accounting),
  and an erasure (`WF.eraseU`, `WF.eraseN`: writing EMPTY keeps `ProbeInv` because every group
  containing the slot already has an EMPTY slot, `exists_empty_of_needsTombstone_eq_false`;
  DELETED keeps it trivially; tombstone rule B only lowers `growthLeft`).
* **The entries after each write** (`Nat` forms; the machine-word forms reduce to them through
  `setCtrl_eq_setCtrlN`, `ctrlWord_eq_ctrlWordN` and `Array.uset_eq_set`): pointwise
  (`entryAt_newN`, `entryAt_kvN`, `entryAt_valN`, `entryAt_eraseN`), and as the list operations
  of the contract (`WF.entries_newN_perm`, `WF.entries_kvN_replace`, `WF.entries_eraseN_eraseKey`).
* **The rebuilt table** (`Table.lean`'s `reserveInsert`, `Proofs/Update.lean`): its entries
  (`rebuild_perm`, `emptyTable_entries`, `reserveTable_perm`) and its room for the new key
  (`freshPre_reserve`).

Proof hints: the earlier linear-probing map's `Insert.lean` (`Slots.entries_setNew_perm`,
`filterMap_perm_cons`, `TagInv.setNew`, `ProbeInv.setNew`); `numDeleted` is a `countP` over the
slots, so a write at slot `i` changes it by the change at `i` only.
-/

@[expose] public section

universe u v w

namespace OAMap.Core.Swiss

open Std.Internal.List

variable {α : Type u} {β : Type v} {γ : Type w}

section Writes

variable [BEq α] [Hashable α] {ctrl : ByteArray} {keys : Array α} {vals : Array β}
  {size gl : Nat} {mask : USize} {shift : UInt64}

/-! ## The invariant after a write -/

/-- The invariant reads the value array only through its size. -/
theorem WF.replaceVals (wf : WF ⟨ctrl, keys, vals⟩ size gl mask shift) {vals' : Array γ}
    (h : vals'.size = vals.size) : WF ⟨ctrl, keys, vals'⟩ size gl mask shift := by
  sorry

/-- Writing `a` over the key of a hit for `a` (machine-word index). -/
theorem WF.keyU (wf : WF ⟨ctrl, keys, vals⟩ size gl mask shift) {a : α} {i : USize}
    (hi : Slots.Hit ⟨ctrl, keys, vals⟩ shift a i.toNat) {h : i.toNat < keys.size} :
    WF ⟨ctrl, keys.uset i a h, vals⟩ size gl mask shift := by
  sorry

/-- Writing `a` over the key of a hit for `a`. -/
theorem WF.keyN (wf : WF ⟨ctrl, keys, vals⟩ size gl mask shift) {a : α} {i : Nat}
    (hi : Slots.Hit ⟨ctrl, keys, vals⟩ shift a i) {h : i < keys.size} :
    WF ⟨ctrl, keys.set i a h, vals⟩ size gl mask shift := by
  sorry

/-- A new key at an EMPTY slot, with room (machine words). -/
theorem WF.newU_empty (wf : WF ⟨ctrl, keys, vals⟩ size gl mask shift)
    (hs : smallMask mask = true) {a : α} {b : β} {q : UInt64} {i : USize}
    (h : NewSlot ⟨ctrl, keys, vals⟩ shift a q i.toNat) {h0 : i.toNat < ctrl.size}
    (hold : (ctrl.uget i h0 == EMPTY) = true) (hgl : ¬(gl == 0) = true)
    {h1 : i.toNat < ctrl.size} {h2 : mask.toNat + 8 < ctrl.size} {h3 : i.toNat < keys.size}
    {h4 : i.toNat < vals.size} :
    WF ⟨setCtrl ctrl mask i (tagOf q) h1 h2, keys.uset i a h3, vals.uset i b h4⟩ (size + 1)
      (gl - 1) mask shift := by
  sorry

/-- A new key at a DELETED slot (machine words). -/
theorem WF.newU_del (wf : WF ⟨ctrl, keys, vals⟩ size gl mask shift)
    (hs : smallMask mask = true) {a : α} {b : β} {q : UInt64} {i : USize}
    (h : NewSlot ⟨ctrl, keys, vals⟩ shift a q i.toNat) {h0 : i.toNat < ctrl.size}
    (hold : ¬(ctrl.uget i h0 == EMPTY) = true)
    {h1 : i.toNat < ctrl.size} {h2 : mask.toNat + 8 < ctrl.size} {h3 : i.toNat < keys.size}
    {h4 : i.toNat < vals.size} :
    WF ⟨setCtrl ctrl mask i (tagOf q) h1 h2, keys.uset i a h3, vals.uset i b h4⟩ (size + 1)
      gl mask shift := by
  sorry

/-- A new key at an EMPTY slot, with room. -/
theorem WF.newN_empty (wf : WF ⟨ctrl, keys, vals⟩ size gl mask shift) {a : α} {b : β}
    {q : UInt64} {i : Nat} (h : NewSlot ⟨ctrl, keys, vals⟩ shift a q i) {h0 : i < ctrl.size}
    (hold : (ctrl[i]'h0 == EMPTY) = true) (hgl : ¬(gl == 0) = true) {h1 : i < ctrl.size}
    {h2 : ctrl.size - 8 + 8 ≤ ctrl.size} {h3 : 0 < ctrl.size - 8} {h4 : i < keys.size}
    {h5 : i < vals.size} :
    WF ⟨setCtrlN ctrl (ctrl.size - 8) i (tagOf q) h1 h2 h3, keys.set i a h4, vals.set i b h5⟩
      (size + 1) (gl - 1) mask shift := by
  sorry

/-- A new key at a DELETED slot. -/
theorem WF.newN_del (wf : WF ⟨ctrl, keys, vals⟩ size gl mask shift) {a : α} {b : β}
    {q : UInt64} {i : Nat} (h : NewSlot ⟨ctrl, keys, vals⟩ shift a q i) {h0 : i < ctrl.size}
    (hold : ¬(ctrl[i]'h0 == EMPTY) = true) {h1 : i < ctrl.size}
    {h2 : ctrl.size - 8 + 8 ≤ ctrl.size} {h3 : 0 < ctrl.size - 8} {h4 : i < keys.size}
    {h5 : i < vals.size} :
    WF ⟨setCtrlN ctrl (ctrl.size - 8) i (tagOf q) h1 h2 h3, keys.set i a h4, vals.set i b h5⟩
      (size + 1) gl mask shift := by
  sorry

/-- `insertFresh`'s write (machine words): the absent key at the free slot `findFree` finds. -/
theorem WF.freshU (wf : WF ⟨ctrl, keys, vals⟩ size gl mask shift) (hs : smallMask mask = true)
    {a : α} {b : β} (h : FreshPre ⟨ctrl, keys, vals⟩ gl a) {i : USize}
    (hi : i = findFree ctrl mask (homeU (hashBits shift a) mask) 0 (wf.loopU' hs).arr
      (and_mask_le _ _) stride_zero)
    {h1 : i.toNat < ctrl.size} {h2 : mask.toNat + 8 < ctrl.size} {h3 : i.toNat < keys.size}
    {h4 : i.toNat < vals.size} {h5 : i.toNat < ctrl.size} :
    WF ⟨setCtrl ctrl mask i (tagOf (hashBits shift a)) h1 h2, keys.uset i a h3, vals.uset i b h4⟩
      (size + 1) (if ctrl.uget i h5 == EMPTY then gl - 1 else gl) mask shift := by
  sorry

/-- `insertFresh`'s write on `Nat` indices. -/
theorem WF.freshN (wf : WF ⟨ctrl, keys, vals⟩ size gl mask shift) (hs : ¬smallMask mask = true)
    {a : α} {b : β} (h : FreshPre ⟨ctrl, keys, vals⟩ gl a) {i : Nat}
    (hi : i = findFreeN ctrl (ctrl.size - 8) (homeN (hashBits shift a) (ctrl.size - 8)) 0
      (wf.ctrlN' hs) (Nat.mod_lt _ (wf.ctrlN' hs).pos))
    {h1 : i < ctrl.size} {h2 : ctrl.size - 8 + 8 ≤ ctrl.size} {h3 : 0 < ctrl.size - 8}
    {h4 : i < keys.size} {h5 : i < vals.size} {h6 : i < ctrl.size} :
    WF ⟨setCtrlN ctrl (ctrl.size - 8) i (tagOf (hashBits shift a)) h1 h2 h3, keys.set i a h4,
      vals.set i b h5⟩ (size + 1) (if ctrl[i]'h6 == EMPTY then gl - 1 else gl) mask shift := by
  sorry

/-- The erasure of a full slot by the tombstone rule (machine words), with any placeholders. -/
theorem WF.eraseU (wf : WF ⟨ctrl, keys, vals⟩ size gl mask shift) (hs : smallMask mask = true)
    {i : USize} (hi : Slots.IsFull ⟨ctrl, keys, vals⟩ i.toNat) {del : Bool}
    {hw1 : i.toNat + 8 ≤ ctrl.size} {hw2 : ((i - 8) &&& mask).toNat + 8 ≤ ctrl.size}
    (hdel : del = needsTombstone (matchEmpty (ctrlWord ctrl i hw1))
      (matchEmpty (ctrlWord ctrl ((i - 8) &&& mask) hw2)))
    {c : Prop} [Decidable c] {gl' : Nat} (hgl : gl' = if del then (if c then 0 else gl) else gl + 1)
    {k0 : α} {v0 : β} {h1 : i.toNat < ctrl.size} {h2 : mask.toNat + 8 < ctrl.size}
    {h3 : i.toNat < keys.size} {h4 : i.toNat < vals.size} :
    WF ⟨setCtrl ctrl mask i (if del then DELETED else EMPTY) h1 h2, keys.uset i k0 h3,
      vals.uset i v0 h4⟩ (size - 1) gl' mask shift := by
  sorry

/-- The erasure of a full slot by the tombstone rule, with any placeholders. -/
theorem WF.eraseN (wf : WF ⟨ctrl, keys, vals⟩ size gl mask shift) {i : Nat}
    (hi : Slots.IsFull ⟨ctrl, keys, vals⟩ i) {hic : i < ctrl.size - 8}
    {hc : ctrl.size - 8 + 8 ≤ ctrl.size} {c' : ByteArray} {gl' : Nat}
    (he : eraseCtrlN ctrl size gl (ctrl.size - 8) i hic hc = (c', gl')) {k0 : α} {v0 : β}
    {h1 : i < keys.size} {h2 : i < vals.size} :
    WF ⟨c', keys.set i k0 h1, vals.set i v0 h2⟩ (size - 1) gl' mask shift := by
  sorry

/-! ## The entries after a write (`Nat` forms) -/

/-- A new entry at slot `i` (any control byte below `0x80`, any free slot `i`). -/
theorem entryAt_newN (wf : WF ⟨ctrl, keys, vals⟩ size gl mask shift) {i : Nat}
    (hi : i < ctrl.size - 8) {t : UInt8} (ht : t < 0x80) (a : α) (b : β) {h1 : i < ctrl.size}
    {h2 : ctrl.size - 8 + 8 ≤ ctrl.size} {h3 : 0 < ctrl.size - 8} {h4 : i < keys.size}
    {h5 : i < vals.size} {j : Nat} (hj : j < ctrl.size - 8) :
    (Slots.mk (setCtrlN ctrl (ctrl.size - 8) i t h1 h2 h3) (keys.set i a h4)
      (vals.set i b h5)).entryAt j =
      if j = i then some ⟨a, b⟩ else Slots.entryAt ⟨ctrl, keys, vals⟩ j := by
  sorry

/-- The erasure of slot `i` by the tombstone rule. -/
theorem entryAt_eraseN (wf : WF ⟨ctrl, keys, vals⟩ size gl mask shift) {i : Nat}
    (hi : Slots.IsFull ⟨ctrl, keys, vals⟩ i) {sz g : Nat} {hic : i < ctrl.size - 8}
    {hc : ctrl.size - 8 + 8 ≤ ctrl.size} {c' : ByteArray} {gl' : Nat}
    (he : eraseCtrlN ctrl sz g (ctrl.size - 8) i hic hc = (c', gl')) {k0 : α} {v0 : β}
    {h1 : i < keys.size} {h2 : i < vals.size} {j : Nat} (hj : j < ctrl.size - 8) :
    (Slots.mk c' (keys.set i k0 h1) (vals.set i v0 h2)).entryAt j =
      if j = i then none else Slots.entryAt ⟨ctrl, keys, vals⟩ j := by
  sorry

/-- The control array after an erasure has the same slots. -/
theorem cap_eraseN {ctrl : ByteArray} {sz g cap i : Nat} {hic : i < cap} {hc : cap + 8 ≤ ctrl.size}
    {c' : ByteArray} {gl' : Nat} (he : eraseCtrlN ctrl sz g cap i hic hc = (c', gl')) :
    c'.size = ctrl.size := by
  sorry

end Writes

/-- The key and value of a full slot. -/
theorem entryAt_kvN (s : Slots α β) {i : Nat} (hi : s.IsFull i) (a : α) (b : β)
    {h1 : i < s.keys.size} {h2 : i < s.vals.size} (j : Nat) :
    (Slots.mk s.ctrl (s.keys.set i a h1) (s.vals.set i b h2)).entryAt j =
      if j = i then some ⟨a, b⟩ else s.entryAt j := by
  sorry

/-- The value of slot `i` (a full slot shows the new value; any other slot is unchanged). -/
theorem entryAt_valN (s : Slots α β) {i : Nat} (v : β) {h : i < s.vals.size} (j : Nat) :
    (Slots.mk s.ctrl s.keys (s.vals.set i v h)).entryAt j =
      if j = i then (s.entryAt i).map (fun e => ⟨e.1, v⟩) else s.entryAt j := by
  sorry

section Lists

variable [BEq α] [Hashable α] {ctrl : ByteArray} {keys : Array α} {vals : Array β}
  {size gl : Nat} {mask : USize} {shift : UInt64}

/-- A new entry at a free slot: the entries gain it, up to order (no lawfulness). -/
theorem WF.entries_newN_perm (wf : WF ⟨ctrl, keys, vals⟩ size gl mask shift) {p₀ i : Nat}
    (hslot : Slots.FreeSlot ⟨ctrl, keys, vals⟩ p₀ i) {t : UInt8} (ht : t < 0x80) (a : α) (b : β)
    {h1 : i < ctrl.size} {h2 : ctrl.size - 8 + 8 ≤ ctrl.size} {h3 : 0 < ctrl.size - 8}
    {h4 : i < keys.size} {h5 : i < vals.size} :
    (Slots.mk (setCtrlN ctrl (ctrl.size - 8) i t h1 h2 h3) (keys.set i a h4)
      (vals.set i b h5)).entries.Perm (⟨a, b⟩ :: Slots.entries ⟨ctrl, keys, vals⟩) := by
  sorry

/-- The key and value of a hit for `a` replaced: `replaceEntry` (lawful instances). -/
theorem WF.entries_kvN_replace (wf : WF ⟨ctrl, keys, vals⟩ size gl mask shift) {a : α} {i : Nat}
    (hit : Slots.Hit ⟨ctrl, keys, vals⟩ shift a i) (b : β) {h1 : i < keys.size}
    {h2 : i < vals.size} [EquivBEq α] [LawfulHashable α] :
    (Slots.mk ctrl (keys.set i a h1) (vals.set i b h2)).entries =
      replaceEntry a b (Slots.entries ⟨ctrl, keys, vals⟩) := by
  sorry

/-- The erasure of the hit for `a`: `eraseKey` (lawful instances). -/
theorem WF.entries_eraseN_eraseKey (wf : WF ⟨ctrl, keys, vals⟩ size gl mask shift) {a : α}
    {i : Nat} (hit : Slots.Hit ⟨ctrl, keys, vals⟩ shift a i) {sz g : Nat}
    {hic : i < ctrl.size - 8} {hc : ctrl.size - 8 + 8 ≤ ctrl.size} {c' : ByteArray} {gl' : Nat}
    (he : eraseCtrlN ctrl sz g (ctrl.size - 8) i hic hc = (c', gl')) {k0 : α} {v0 : β}
    {h1 : i < keys.size} {h2 : i < vals.size} [EquivBEq α] [LawfulHashable α] :
    (Slots.mk c' (keys.set i k0 h1) (vals.set i v0 h2)).entries =
      eraseKey a (Slots.entries ⟨ctrl, keys, vals⟩) := by
  sorry

end Lists

/-! ## The rebuilt table (`Build.lean`) -/

section Rebuilt

variable [BEq α] [Hashable α]

/-- A rebuild keeps the entries, up to order. -/
theorem rebuild_perm (t : Table α β) (lg : Nat) (k0 : α) (v0 : β)
    (h : RebuildPre t.slots t.size lg) :
    (rebuild t lg k0 v0 h).slots.entries.Perm t.slots.entries := by
  sorry

/-- A rebuild keeps the size. -/
theorem rebuild_size (t : Table α β) (lg : Nat) (k0 : α) (v0 : β)
    (h : RebuildPre t.slots t.size lg) : (rebuild t lg k0 v0 h).size = t.size := by
  sorry

/-- A fresh table has no entries. -/
theorem emptyTable_entries (lg : Nat) (k0 : α) (v0 : β) (req : Nat) (h : 3 ≤ lg) :
    (emptyTable lg k0 v0 req h : Table α β).slots.entries = [] := by
  sorry

/-- The table an insert that found no room writes into has the same entries, up to order. -/
theorem reserveTable_perm (t : Table α β) (a : α) (b : β) :
    (reserveTable t a b).slots.entries.Perm t.slots.entries := by
  sorry

/-- The table an insert that found no room writes into has room for the absent key. -/
theorem freshPre_reserve (t : Table α β) (a : α) (b : β)
    (h : ∀ [EquivBEq α] [LawfulHashable α], t.slots.Absent a) :
    FreshPre (reserveTable t a b).slots (reserveTable t a b).growthLeft a := by
  sorry

end Rebuilt

end OAMap.Core.Swiss
