module

public import OAMap.Core.Swiss.Loops

/-!
# Swiss core proofs, part 2: the probe lemmas

A proof file of the SwissTable core (`OAMap/Core/Swiss/Table.lean`, "Proof structure"). Its
owner edits only this file: the proofs, and any private helper lemmas or definitions. The
statements are fixed (the code and later files use them), except those marked *suggested route*,
which no other file uses and which may be changed or dropped.

What a probe returns, in a well-formed table:

* **Lookup** (`findU`, `findN`): a hit (`Slots.Hit`: a full slot with the tag of `a` and a key
  `== a`), or, for lawful instances, a proof that no stored key is `== a` (`Slots.Absent`).
* **Insertion** (`insProbeU`, `insProbeN`, `insSlotN` with fast path C, and the fast path of
  `containsThenInsert` on machine words, `WF.fast_new`): a hit, or a `NewSlot` for `a`: a free
  slot that the probe of `a` reaches (or slot `0` of the unallocated table), with `a` absent for
  lawful instances. A free slot exists because `size < cap` (the load bound `WF.room`).
* **The fused operations' U facts** (`Proofs/Query.lean`): the insertion probe hits exactly where
  the lookup probe does, and fast path C applies only where the lookup misses. No lawfulness.

The probe invariant (`Slots.ProbeInv`) and `Distinct` are what make a miss an absence: the slot
`i` of a stored key `k == a` lies in group `k'` of the probe from the home slot of `a` (the same
as that of `k`, by `LawfulHashable`), no group before `k'` has an EMPTY slot, so the probe reaches
group `k'`, where slot `i` carries the tag of `a` (`TagInv`) and is compared. A probe that visits
all `cap / 8` groups visits every slot (`probe_cover`, `probe_unique`).

Suggested route (the earlier linear-probing map's `Probe.lean`: `walk_spec`, `probeN_eq`,
`slotOf_of_beq`, `slotOf_absent`): state the loop invariant of `findLoopN`/`findInsLoopN` at group
`k` of the probe from `p₀` (`pos = probePos cap p₀ k`, `stride = 8 * k`, `g` the group word, `m`
the tag matches of `g` not yet compared, every tag match of the earlier groups and of the
compared lanes compared and not `== a`, no EMPTY slot in the earlier groups, and for the
insertion probe `ins` the first free slot passed or `cap`), prove the `Nat` loops by induction on
the measure, and reduce the machine-word loops to them (`findU_toNat`, `insProbeU_toNat`) through
`Geom` and `ctrlWord_eq_ctrlWordN`; the unallocated table is the separate case of `firstGroup`.
-/

@[expose] public section

universe u v w

namespace OAMap.Core.Swiss

variable {α : Type u} {β : Type v}

section Spec

variable [BEq α] [Hashable α] {s : Slots α β} {size gl : Nat} {mask : USize} {shift : UInt64}

/-! ## The lookup probe -/

/-- A machine-word lookup that ends at a slot ends at a hit. -/
theorem WF.findU_hit (wf : WF s size gl mask shift) (h : LoopU s.ctrl s.keys mask) {a : α}
    (hi : findU s.ctrl s.keys mask shift a h ≤ mask) :
    s.Hit shift a (findU s.ctrl s.keys mask shift a h).toNat := by
  sorry

/-- A machine-word lookup that ends past the slots proves `a` absent (lawful instances). -/
theorem WF.findU_absent (wf : WF s size gl mask shift) (h : LoopU s.ctrl s.keys mask) {a : α}
    (hi : ¬findU s.ctrl s.keys mask shift a h ≤ mask) [EquivBEq α] [LawfulHashable α] :
    s.Absent a := by
  sorry

/-- A lookup on `Nat` indices that finds a slot finds a hit. -/
theorem WF.findN_hit (wf : WF s size gl mask shift) (hA : ArrN s.ctrl s.keys (s.ctrl.size - 8))
    {a : α} {i : Nat} (he : findN s.ctrl s.keys (s.ctrl.size - 8) shift a hA = some i) :
    s.Hit shift a i := by
  sorry

/-- A lookup on `Nat` indices that finds none proves `a` absent (lawful instances). -/
theorem WF.findN_absent (wf : WF s size gl mask shift)
    (hA : ArrN s.ctrl s.keys (s.ctrl.size - 8)) {a : α}
    (he : findN s.ctrl s.keys (s.ctrl.size - 8) shift a hA = none) [EquivBEq α]
    [LawfulHashable α] : s.Absent a := by
  sorry

/-! ## The insertion probe -/

/-- The machine-word insertion probe that ends at a slot ends at a hit. -/
theorem WF.insProbeU_hit (wf : WF s size gl mask shift) (h : LoopU s.ctrl s.keys mask) {a : α}
    (hr : insProbeU s.ctrl s.keys mask shift a h ≤ mask) :
    s.Hit shift a (insProbeU s.ctrl s.keys mask shift a h).toNat := by
  sorry

/-- The machine-word insertion probe that ends past the slots ends at `mask + 1` plus the slot
where the new key goes. -/
theorem WF.insProbeU_new (wf : WF s size gl mask shift) (h : LoopU s.ctrl s.keys mask) {a : α}
    (hr : ¬insProbeU s.ctrl s.keys mask shift a h ≤ mask) :
    NewSlot s shift a (hashBits shift a)
      (insProbeU s.ctrl s.keys mask shift a h - (mask + 1)).toNat := by
  sorry

/-- **Fast path C**: when no lane of the home group carries the tag and the home slot is EMPTY,
the new key goes to the home slot. -/
theorem WF.fast_new (wf : WF s size gl mask shift) (h : LoopU s.ctrl s.keys mask) {a : α}
    (hmt : (matchTag (ctrlWord s.ctrl (homeU (hashBits shift a) mask) (and_mask_word h.arr.word))
      (repTag (tagOf (hashBits shift a))) == 0) = true)
    (hg : (ctrlWord s.ctrl (homeU (hashBits shift a) mask) (and_mask_word h.arr.word) &&& 0xFF ==
      0xFF) = true) :
    NewSlot s shift a (hashBits shift a) (homeU (hashBits shift a) mask).toNat := by
  sorry

/-- The insertion probe of `containsThenInsertN` (with fast path C) that finds a slot finds a
hit. -/
theorem WF.insSlotN_hit (wf : WF s size gl mask shift)
    (hA : ArrN s.ctrl s.keys (s.ctrl.size - 8)) {a : α} {i : Nat}
    (he : insSlotN s.ctrl s.keys a (s.ctrl.size - 8) (hashBits shift a) hA = .inl i) :
    s.Hit shift a i := by
  sorry

/-- The insertion probe of `containsThenInsertN` that finds no hit returns where the new key
goes. -/
theorem WF.insSlotN_new (wf : WF s size gl mask shift)
    (hA : ArrN s.ctrl s.keys (s.ctrl.size - 8)) {a : α} {j : Nat}
    (he : insSlotN s.ctrl s.keys a (s.ctrl.size - 8) (hashBits shift a) hA = .inr j) :
    NewSlot s shift a (hashBits shift a) j := by
  sorry

/-- The insertion probe on `Nat` indices that finds a slot finds a hit. -/
theorem WF.insProbeN_hit (wf : WF s size gl mask shift)
    (hA : ArrN s.ctrl s.keys (s.ctrl.size - 8)) {a : α} {i : Nat}
    (he : insProbeN s.ctrl s.keys (s.ctrl.size - 8) shift a hA = .inl i) : s.Hit shift a i := by
  sorry

/-- The insertion probe on `Nat` indices that finds no hit returns where the new key goes. -/
theorem WF.insProbeN_new (wf : WF s size gl mask shift)
    (hA : ArrN s.ctrl s.keys (s.ctrl.size - 8)) {a : α} {j : Nat}
    (he : insProbeN s.ctrl s.keys (s.ctrl.size - 8) shift a hA = .inr j) :
    NewSlot s shift a (hashBits shift a) j := by
  sorry

end Spec

/-! ## The fused operations: the insertion probe hits where the lookup does (no lawfulness) -/

section Fused

variable [BEq α] [Hashable α] {ctrl : ByteArray} {keys : Array α} {mask : USize} {cap : Nat}
  {shift : UInt64} {a : α}

/-- The insertion probe ends at a slot exactly when the lookup does. (The invariant is needed only
on 32-bit platforms: in a full table of `2 ^ 31` slots, `ins + (mask + 1)` would wrap to `0`;
`WF.room` leaves a free slot.) -/
theorem WF.insProbeU_le_iff {vals : Array β} {size gl : Nat}
    (wf : WF ⟨ctrl, keys, vals⟩ size gl mask shift) (h : LoopU ctrl keys mask) :
    insProbeU ctrl keys mask shift a h ≤ mask ↔ findU ctrl keys mask shift a h ≤ mask := by
  sorry

theorem insProbeU_eq_findU (h : LoopU ctrl keys mask)
    (hr : findU ctrl keys mask shift a h ≤ mask) :
    insProbeU ctrl keys mask shift a h = findU ctrl keys mask shift a h := by
  sorry

/-- Fast path C applies only where the lookup misses. -/
theorem fast_findU (h : LoopU ctrl keys mask)
    (hmt : (matchTag (ctrlWord ctrl (homeU (hashBits shift a) mask) (and_mask_word h.arr.word))
      (repTag (tagOf (hashBits shift a))) == 0) = true)
    (hg : (ctrlWord ctrl (homeU (hashBits shift a) mask) (and_mask_word h.arr.word) &&& 0xFF ==
      0xFF) = true) :
    ¬findU ctrl keys mask shift a h ≤ mask := by
  sorry

theorem insSlotN_inl_iff (hA : ArrN ctrl keys cap) {i : Nat} :
    insSlotN ctrl keys a cap (hashBits shift a) hA = .inl i ↔
      findN ctrl keys cap shift a hA = some i := by
  sorry

theorem insProbeN_inl_iff (hA : ArrN ctrl keys cap) {i : Nat} :
    insProbeN ctrl keys cap shift a hA = .inl i ↔ findN ctrl keys cap shift a hA = some i := by
  sorry

end Fused

/-! ## Machine words against `Nat` indices (suggested route) -/

section Words

variable [BEq α] [Hashable α] {ctrl : ByteArray} {keys : Array α} {mask : USize} {cap : Nat}
  {shift : UInt64} {a : α}

/-- *Suggested route.* The machine-word lookup is the one on `Nat` indices. -/
theorem findU_toNat (hg : Geom cap mask) (hsz : ctrl.size = cap + 8) (h : LoopU ctrl keys mask)
    (hA : ArrN ctrl keys cap) :
    (if findU ctrl keys mask shift a h ≤ mask then some (findU ctrl keys mask shift a h).toNat
      else none) = findN ctrl keys cap shift a hA := by
  sorry

/-- *Suggested route.* The machine-word insertion probe is the one on `Nat` indices (in a table
with the invariant, which leaves a free slot: see `WF.insProbeU_le_iff`). -/
theorem insProbeU_toNat {vals : Array β} {size gl : Nat}
    (wf : WF ⟨ctrl, keys, vals⟩ size gl mask shift) (hg : Geom cap mask) (hsz : ctrl.size = cap + 8)
    (h : LoopU ctrl keys mask) (hA : ArrN ctrl keys cap) :
    (if insProbeU ctrl keys mask shift a h ≤ mask then
      Sum.inl (insProbeU ctrl keys mask shift a h).toNat
      else Sum.inr (insProbeU ctrl keys mask shift a h - (mask + 1)).toNat) =
      insProbeN ctrl keys cap shift a hA := by
  sorry

end Words

end OAMap.Core.Swiss
