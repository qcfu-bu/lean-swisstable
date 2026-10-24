module

public import OAMap.Core.Swiss.Loops

/-!
# Swiss core proofs, part 3: the empty table, `findFree`, and the rebuild's move loops

A proof file of the SwissTable core (`OAMap/Core/Swiss/Table.lean`, "Proof structure"). Its
owner edits only this file: the proofs, and any private helper lemmas or definitions. The
statements are fixed (later files use them), except those marked *suggested route*, which no
other file uses and which may be changed or dropped.

* **The empty table** (`Build.lean`: `emptyTable`, `rebuild`): `emptyCtrl (2 ^ lg)` is `2 ^ lg + 8`
  EMPTY bytes (`dblTo` doubles `emptyGroup` exactly up to `2 ^ lg`), so the fresh arrays are a
  well-formed empty table (`WF.empty`) and satisfy the move loops' hypotheses (`moveDstU`,
  `moveDstN`).
* **`findFree`** (`Build.lean`, `Table.lean`'s `insertFresh`, `Write.lean`): it ends at a slot or
  `mask + 1` (`freeBound`, `freeBoundN`), and, when the table has a free slot, at a free slot its
  probe reaches (`WF.findFree_slot`, `WF.findFreeN_slot`): the first group with a free byte, so
  no earlier group has an EMPTY byte.
* **The rebuild** (`Build.lean`'s `rebuild`; `Write.lean` lifts the entries to `Table`): the move
  loops build a well-formed table (`WF.rebuild`) with the same entries up to order
  (`rebuild_perm_raw`), with no key comparison and no lawfulness.

Suggested route (the earlier linear-probing map's `Grow.lean`: `ReinsertInv`, `reinsertN_inv`,
`entries_grow_perm`): first `moveLoop_eq_moveLoopN` and `findFree_toNat` (the machine-word loops
are the `Nat` ones, through `setCtrl_eq_setCtrlN`, `ctrlWord_eq_ctrlWordN`, `homeU_toNat` and
`Array.uset_eq_set`), then an invariant of `moveLoopN` after the old slots below `i` are moved:
the new arrays are mirrored, of the right sizes, hold only EMPTY and FULL bytes, carry the tags of
the new shift, satisfy `Distinct`/`ProbeInv` under lawfulness (a moved key is not `==` to any key
moved before it, by the old table's `Distinct`), have no tombstones, and hold the entries of the
old slots below `i` up to order. The probe of a moved key passes only groups without a free byte
(`findFree`), hence without an EMPTY byte.
-/

-- Some fixed statements take hypotheses that their proofs do not need (`findFree_toNat`'s size
-- fact, the guards of `WF.fresh_*`).
set_option linter.unusedVariables false

@[expose] public section

universe u v w

namespace OAMap.Core.Swiss

variable {α : Type u} {β : Type v}

/-! ## Private helpers: the guard, control bytes, slots -/

/-- The machine-word guard on `(2 ^ lg - 1).toUSize` says `lg ≤ 31`. -/
private theorem lg_le_of_smallMask {lg : Nat}
    (h : smallMask (((2 : Nat) ^ lg - 1).toUSize) = true) : lg ≤ 31 := by
  refine Nat.le_of_not_lt fun hlt => ?_
  unfold smallMask at h
  have h0 : ((2 : Nat) ^ lg - 1).toUSize &&& 0x80000000 = 0 := by simpa using h
  have := congrArg (fun x : USize => x.toNat.testBit 31) h0
  have hb : System.Platform.numBits = 32 ∨ System.Platform.numBits = 64 :=
    System.Platform.numBits_eq
  have hl : (0x80000000 : USize).toNat = 2 ^ 31 :=
    USize.toNat_ofNat_of_lt (Nat.lt_of_lt_of_le (by decide) USize.le_size)
  simp only [USize.toNat_and, Nat.testBit_and, hl, Nat.toUSize, USize.toNat_ofNat',
    Nat.testBit_mod_two_pow, Nat.testBit_two_pow_sub_one, USize.toNat_zero, Nat.zero_testBit,
    Nat.testBit_two_pow_self] at this
  rcases hb with hb | hb <;> simp [hb, hlt] at this <;> omega

/-- Below `2 ^ 31` slots the mask does not wrap. -/
private theorem toNat_mask_of_le {lg : Nat} (h : lg ≤ 31) :
    (((2 : Nat) ^ lg - 1).toUSize).toNat = 2 ^ lg - 1 := by
  simp only [Nat.toUSize, USize.toNat_ofNat']
  apply Nat.mod_eq_of_lt
  have h1 : 2 ^ lg ≤ 2 ^ 31 := Nat.pow_le_pow_right (by decide) h
  have h2 : 2 ^ 32 ≤ 2 ^ System.Platform.numBits := USize.le_size
  omega

/-- The geometry of the new table of a machine-word rebuild. -/
private theorem geom_of_le {lg : Nat} (h3 : 3 ≤ lg) (h : lg ≤ 31) :
    Geom ((2 : Nat) ^ lg) (((2 : Nat) ^ lg - 1).toUSize) := by
  have h1 : 2 ^ lg ≤ 2 ^ 31 := Nat.pow_le_pow_right (by decide) h
  have h2 : 2 ^ 32 ≤ USize.size := USize.le_size
  have h8 : 2 ^ 3 ≤ 2 ^ lg := Nat.pow_le_pow_right (by decide) h3
  have hp : 0 < 2 ^ lg := Nat.two_pow_pos lg
  exact ⟨by rw [toNat_mask_of_le h]; omega, ⟨lg, rfl⟩, by simpa using h8, by omega⟩

/-- The FULL test of the move loops. -/
private theorem and80_eq_zero (b : UInt8) : (b &&& 0x80 == 0) = decide (b < 0x80) := by
  have key : ∀ v < 256, (v &&& 128 = 0) = (v < 128) := by decide +kernel
  rw [Bool.eq_iff_iff, beq_iff_eq, decide_eq_true_iff, ← UInt8.toNat_inj, UInt8.toNat_and,
    UInt8.lt_iff_toNat_lt]
  simp only [UInt8.toNat_ofNat]
  rw [key _ b.toNat_lt]

private theorem not_lt_EMPTY : ¬EMPTY < 0x80 := by rw [EMPTY_eq]; decide

private theorem DELETED_not_lt : ¬DELETED < 0x80 := by rw [DELETED_eq]; decide

/-- A slot whose control byte is not FULL has no entry. -/
private theorem entryAt_none {s : Slots α β} {i : Nat} (h : ¬s.ctrl[i]! < 0x80) :
    s.entryAt i = none := by
  unfold Slots.entryAt
  by_cases hi : i < s.ctrl.size
  · rw [getElem?_pos s.ctrl i hi]
    rw [getElem!_pos s.ctrl i hi] at h
    simp only [h, ite_false]
  · rw [getElem?_neg s.ctrl i hi]

/-- The entry of a FULL slot with its cells. -/
private theorem entryAt_some {s : Slots α β} {i : Nat} (hc : i < s.ctrl.size)
    (h : s.ctrl[i] < 0x80) (hk : i < s.keys.size) (hv : i < s.vals.size) :
    s.entryAt i = some ⟨s.keys[i], s.vals[i]⟩ := by
  unfold Slots.entryAt
  rw [getElem?_pos s.ctrl i hc]
  simp only [h, ite_true, getElem?_pos s.keys i hk, getElem?_pos s.vals i hv, Option.bind_some,
    Option.map_some]

/-! ## The empty table -/

/-- Doubling a run of `2 ^ m` EMPTY bytes up to `2 ^ lg` bytes. -/
private theorem data_dblTo {lg : Nat} :
    ∀ (d : Nat) {m : Nat} {b : ByteArray}, lg = m + d →
      b.data = Array.replicate (2 ^ m) (0xFF : UInt8) →
      (dblTo (2 ^ lg) b).data = Array.replicate (2 ^ lg) (0xFF : UInt8)
  | 0, m, b, hlg, hb => by
    obtain rfl : lg = m := by omega
    have hs : b.size = 2 ^ lg := by rw [← ByteArray.size_data, hb, Array.size_replicate]
    rw [dblTo, ite_eq_right (by rw [hs]; omega), hb]
  | d + 1, m, b, hlg, hb => by
    have hs : b.size = 2 ^ m := by rw [← ByteArray.size_data, hb, Array.size_replicate]
    have hlt : 2 ^ m < 2 ^ lg := Nat.pow_lt_pow_right (by decide) (by omega)
    rw [dblTo, ite_eq_left ⟨by rw [hs]; exact hlt, by rw [hs]; exact Nat.two_pow_pos m⟩]
    refine data_dblTo d (m := m + 1) (by omega) ?_
    rw [ByteArray.data_append, hb, Array.replicate_append_replicate, Nat.pow_succ, Nat.mul_two]

/-- `emptyCtrl (2 ^ lg)` is `2 ^ lg + 8` EMPTY bytes. -/
private theorem data_emptyCtrl {lg : Nat} (h : 3 ≤ lg) :
    (emptyCtrl ((2 : Nat) ^ lg)).data = Array.replicate ((2 : Nat) ^ lg + 8) (0xFF : UInt8) := by
  have he : emptyGroup.data = Array.replicate (2 ^ 3) (0xFF : UInt8) := by decide
  unfold emptyCtrl
  rw [ByteArray.data_append, data_dblTo (lg - 3) (m := 3) (by omega) he, he,
    Array.replicate_append_replicate]

theorem size_emptyCtrl {lg : Nat} (h : 3 ≤ lg) :
    (emptyCtrl ((2 : Nat) ^ lg)).size = (2 : Nat) ^ lg + 8 := by
  rw [← ByteArray.size_data, data_emptyCtrl h, Array.size_replicate]

private theorem getElem_emptyCtrl {lg : Nat} (h : 3 ≤ lg) {i : Nat}
    (hi : i < (emptyCtrl ((2 : Nat) ^ lg)).size) : (emptyCtrl ((2 : Nat) ^ lg))[i] = EMPTY := by
  rw [ByteArray.getElem_eq_getElem_data]
  simp only [data_emptyCtrl h, Array.getElem_replicate, EMPTY_eq]

theorem getElem!_emptyCtrl {lg : Nat} (h : 3 ≤ lg) {i : Nat} (hi : i < (2 : Nat) ^ lg + 8) :
    (emptyCtrl ((2 : Nat) ^ lg))[i]! = EMPTY := by
  have hi' : i < (emptyCtrl ((2 : Nat) ^ lg)).size := by rw [size_emptyCtrl h]; exact hi
  rw [getElem!_pos _ i hi', getElem_emptyCtrl h hi']

theorem mirrored_emptyCtrl {lg : Nat} (h : 3 ≤ lg) :
    Mirrored (emptyCtrl ((2 : Nat) ^ lg)) ((2 : Nat) ^ lg) := by
  have h8 : 2 ^ 3 ≤ 2 ^ lg := Nat.pow_le_pow_right (by decide) h
  exact ⟨size_emptyCtrl h, ⟨lg, rfl⟩, by simpa using h8, fun j hj => by
    rw [getElem_emptyCtrl h, getElem_emptyCtrl h]⟩

/-- The fresh arrays of `2 ^ lg` slots are a well-formed empty table. -/
theorem WF.empty [BEq α] [Hashable α] {lg : Nat} (k0 : α) (v0 : β) (h : 3 ≤ lg) :
    WF ⟨emptyCtrl ((2 : Nat) ^ lg), Array.replicate ((2 : Nat) ^ lg + 1) k0,
        Array.replicate ((2 : Nat) ^ lg + 1) v0⟩
      0 (capacityOf ((2 : Nat) ^ lg)) (((2 : Nat) ^ lg - 1).toUSize) ((57 - lg).toUInt64) := by
  have hcap : (Slots.mk (emptyCtrl ((2 : Nat) ^ lg)) (Array.replicate ((2 : Nat) ^ lg + 1) k0)
      (Array.replicate ((2 : Nat) ^ lg + 1) v0)).cap = 2 ^ lg := by
    unfold Slots.cap; rw [size_emptyCtrl h, Nat.add_sub_cancel]
  have hE : ∀ i < (2 : Nat) ^ lg, (emptyCtrl ((2 : Nat) ^ lg))[i]! = EMPTY := fun i hi =>
    getElem!_emptyCtrl h (by omega)
  have nf : ∀ i, ¬(Slots.mk (emptyCtrl ((2 : Nat) ^ lg))
      (Array.replicate ((2 : Nat) ^ lg + 1) k0)
      (Array.replicate ((2 : Nat) ^ lg + 1) v0)).IsFull i := by
    rintro i ⟨hi, hf⟩
    rw [hcap] at hi
    exact not_lt_EMPTY (hE i hi ▸ hf)
  have hen : (Slots.mk (emptyCtrl ((2 : Nat) ^ lg)) (Array.replicate ((2 : Nat) ^ lg + 1) k0)
      (Array.replicate ((2 : Nat) ^ lg + 1) v0)).entries = [] := by
    unfold Slots.entries
    rw [List.filterMap_eq_nil_iff]
    intro i hi
    rw [List.mem_range, hcap] at hi
    exact entryAt_none (by rw [hE i hi]; exact not_lt_EMPTY)
  have hnd : (Slots.mk (emptyCtrl ((2 : Nat) ^ lg)) (Array.replicate ((2 : Nat) ^ lg + 1) k0)
      (Array.replicate ((2 : Nat) ^ lg + 1) v0)).numDeleted = 0 := by
    unfold Slots.numDeleted
    rw [List.countP_eq_zero]
    intro i hi
    rw [List.mem_range, hcap] at hi
    simp only [hE i hi, beq_iff_eq]
    exact fun e => DELETED_ne_EMPTY e.symm
  exact {
    shape := Or.inr ⟨lg, h, mirrored_emptyCtrl h, Array.size_replicate, Array.size_replicate,
      rfl, rfl⟩
    ctrl := fun i hi => by rw [hcap] at hi; rw [hE i hi]; exact isCtrl_EMPTY
    tag := fun i _ hi => absurd hi (nf i)
    size_eq := by rw [hen]; rfl
    room := by rw [hnd, hcap]; omega
    distinct := by intro _ _ i _ _ _ hi; exact absurd hi (nf i)
    probe := by intro _ _ i _ hi; exact absurd hi (nf i) }

/-- The fresh arrays of a machine-word rebuild into `2 ^ lg ≤ 2 ^ 31` slots. -/
theorem moveDstU {lg : Nat} (h3 : 3 ≤ lg) (hs : smallMask (((2 : Nat) ^ lg - 1).toUSize) = true)
    {c : ByteArray} {k : Array α} {v : Array β} {k0 : α} {v0 : β} :
    MoveDstU (c.propagateMark (emptyCtrl ((2 : Nat) ^ lg)))
      (k.propagateMark (Array.replicate ((2 : Nat) ^ lg + 1) k0))
      (v.propagateMark (Array.replicate ((2 : Nat) ^ lg + 1) v0))
      (((2 : Nat) ^ lg - 1).toUSize) := by
  have hl := lg_le_of_smallMask hs
  have hm := toNat_mask_of_le hl
  have h1 : 2 ^ lg ≤ 2 ^ 31 := Nat.pow_le_pow_right (by decide) hl
  have hp : 0 < 2 ^ lg := Nat.two_pow_pos lg
  simp only [ByteArray.propagateMark_eq, Array.propagateMark_eq]
  exact ⟨⟨by rw [size_emptyCtrl h3, hm]; omega, by omega⟩,
    by rw [size_emptyCtrl h3, hm]; omega,
    by rw [Array.size_replicate, hm]; omega, by rw [Array.size_replicate, hm]; omega⟩

/-- The fresh arrays of a rebuild on `Nat` indices into `2 ^ lg` slots. -/
theorem moveDstN {lg : Nat} (h3 : 3 ≤ lg) {c : ByteArray} {k : Array α} {v : Array β} {k0 : α}
    {v0 : β} :
    MoveDstN (c.propagateMark (emptyCtrl ((2 : Nat) ^ lg)))
      (k.propagateMark (Array.replicate ((2 : Nat) ^ lg + 1) k0))
      (v.propagateMark (Array.replicate ((2 : Nat) ^ lg + 1) v0)) ((2 : Nat) ^ lg) := by
  simp only [ByteArray.propagateMark_eq, Array.propagateMark_eq]
  exact ⟨Nat.two_pow_pos lg, size_emptyCtrl h3, Array.size_replicate, Array.size_replicate⟩

/-! ## `findFree` -/

/-- Below `2 ^ 31`, adding a small literal does not wrap. -/
private theorem toNat_add_one' {a : USize} (ha : a.toNat < 2 ^ 31) :
    (a + 1).toNat = a.toNat + 1 := by
  have h2 : 2 ^ 32 ≤ 2 ^ System.Platform.numBits := USize.le_size
  rw [USize.toNat_add, USize.toNat_one, Nat.mod_eq_of_lt (by omega)]

/-- The probe step `stride + 8` does not wrap below `2 ^ 31`. -/
private theorem toNat_add_eight {a : USize} (ha : a.toNat < 2 ^ 31) :
    (a + 8).toNat = a.toNat + 8 := by
  have h2 : 2 ^ 32 ≤ 2 ^ System.Platform.numBits := USize.le_size
  have h8 : (8 : USize).toNat = 8 := USize.toNat_ofNat_of_lt (Nat.lt_of_lt_of_le (by decide) h2)
  rw [USize.toNat_add, h8, Nat.mod_eq_of_lt (by omega)]

private theorem findFreeN_congr {c : ByteArray} {cap p p' st st' : Nat} {hA : CtrlN c cap}
    {hp : p < cap} {hp' : p' < cap} (h1 : p = p') (h2 : st = st') :
    findFreeN c cap p st hA hp = findFreeN c cap p' st' hA hp' := by
  subst h1 h2; rfl

/-- `findFree` ends at a slot or at `mask + 1`. -/
theorem freeBound {mask : USize} : FreeBound mask := by
  intro c pos stride hA hp hs
  induction h : mask.toNat + 8 - stride.toNat using Nat.strongRecOn
    generalizing pos stride with
  | _ n ih =>
    rw [findFree]
    dsimp only
    split
    · exact Nat.le_succ_of_le (and_mask_le _ _)
    · split
      · rw [toNat_add_one' hA.small]
        exact Nat.le_refl _
      · exact ih _ (h ▸ sub_group hA.small hs ‹_›) _ _ _ _ rfl

/-- `findFreeN` ends at a slot or at `cap`. -/
theorem freeBoundN {cap : Nat} : FreeBoundN cap := by
  intro c pos stride hA hp
  induction h : cap + 8 - stride using Nat.strongRecOn generalizing pos stride with
  | _ n ih =>
    rw [findFreeN]
    dsimp only
    split
    · exact Nat.le_of_lt (Nat.mod_lt _ hA.pos)
    · split
      · exact Nat.le_refl _
      · exact ih _ (h ▸ sub_groupN ‹_›) _ _ _ rfl

/-- `findFree` is `findFreeN` (suggested route; not used outside this file). -/
theorem findFree_toNat {c : ByteArray} {cap : Nat} {mask : USize} (hg : Geom cap mask)
    (hsz : c.size = cap + 8) {pos stride : USize} {hA : ArrU c mask} {hp : pos.toNat ≤ mask.toNat}
    {hs : stride.toNat ≤ mask.toNat} {hA' : CtrlN c cap} {hp' : pos.toNat < cap} :
    (findFree c mask pos stride hA hp hs).toNat =
      findFreeN c cap pos.toNat stride.toNat hA' hp' := by
  have hmc := hg.mask_add_one
  have hsm := hA.small
  induction h : mask.toNat + 8 - stride.toNat using Nat.strongRecOn
    generalizing pos stride with
  | _ n ih =>
    have hw : ctrlWord c pos (word_of_le hA.word hp) =
        ctrlWordN c pos.toNat (hA'.word_of_lt hp') := ctrlWord_eq_ctrlWordN (by omega)
    rw [findFree, findFreeN]
    dsimp only
    rw [hw]
    by_cases hf : (matchFree (ctrlWordN c pos.toNat (hA'.word_of_lt hp')) != 0) = true
    · rw [ite_eq_left hf, ite_eq_left hf, hg.toNat_add_and_mask,
        toNat_lowestLane_of_isMask (isMask_matchFree _)]
    · rw [ite_eq_right hf, ite_eq_right hf]
      have e8 := toNat_add_eight (a := stride) (by omega)
      by_cases hgt : stride + 8 > mask
      · have hle : cap ≤ stride.toNat + 8 := by
          rw [GT.gt, USize.lt_iff_toNat_lt, e8] at hgt; omega
        rw [dite_eq_left hgt, dite_eq_left hle, toNat_add_one' hsm, hmc]
      · have hle : ¬cap ≤ stride.toNat + 8 := by
          rw [GT.gt, USize.lt_iff_toNat_lt, e8] at hgt; omega
        rw [dite_eq_right hgt, dite_eq_right hle]
        rw [ih _ (h ▸ sub_group hsm hs hgt) (pos := (pos + (stride + 8)) &&& mask)
          (stride := stride + 8) (hp' := hg.and_mask_lt _) rfl]
        exact findFreeN_congr (by rw [hg.toNat_add_and_mask, e8]) e8

/-- A free (EMPTY or DELETED) control byte. -/
private def IsFree (b : UInt8) : Prop := b = EMPTY ∨ b = DELETED

private theorem le_of_isFree {b : UInt8} (h : IsFree b) : 0x80 ≤ b := by
  rcases h with rfl | rfl
  · rw [EMPTY_eq]; decide
  · rw [DELETED_eq]; decide

/-- **The free-slot probe on `Nat` indices**, from group `k` of the probe from `p₀` on, when no
earlier group has a free slot and the table has one: it ends at a free slot of a group the
probe reaches. -/
private theorem findFreeN_spec {c : ByteArray} {cap : Nat} (hm : Mirrored c cap)
    (hctrl : ∀ i < cap, IsCtrl c[i]!) (hfree : ∃ i < cap, IsFree c[i]!) {p₀ : Nat} :
    ∀ (d k : Nat) {pos stride : Nat} {hA : CtrlN c cap} {hp : pos < cap},
      k + d = cap / 8 → pos = probePos cap p₀ k → stride = 8 * k →
      (∀ k' < k, ∀ j < 8, ¬IsFree c[(probePos cap p₀ k' + j) % cap]!) →
      findFreeN c cap pos stride hA hp < cap ∧ IsFree c[findFreeN c cap pos stride hA hp]! ∧
        ∃ k₁ < cap / 8, ∃ j < 8,
          (probePos cap p₀ k₁ + j) % cap = findFreeN c cap pos stride hA hp ∧
          ∀ k' < k₁, ∀ j' < 8, c[(probePos cap p₀ k' + j') % cap]! ≠ EMPTY := by
  have h8 := hm.le_cap
  obtain ⟨n, hn⟩ := hm.pow_two
  obtain ⟨h8G, -⟩ := cap_facts hn h8
  have hc0 : 0 < cap := by omega
  -- byte `j` of the group at `pos`
  have hbyte : ∀ {pos : Nat} (hp : pos < cap) {hw : pos + 8 ≤ c.size} {j : Nat}, j < 8 →
      byte (ctrlWordN c pos hw) j = c[(pos + j) % cap]! := fun hp hw j hj => by
    rw [byte_ctrlWordN_of_mirrored hm hp hj, slotByte_def, Nat.mod_mod]
  intro d
  induction d with
  | zero =>
    intro k pos stride hA hp hkd hpos hst hprev
    exfalso
    obtain ⟨i, hi, hfi⟩ := hfree
    obtain ⟨k', hk', j, hj, he⟩ := probe_cover p₀ hn h8 hi
    exact hprev k' (by omega) j hj (he ▸ hfi)
  | succ d ih =>
    intro k pos stride hA hp hkd hpos hst hprev
    subst hpos hst
    rw [findFreeN]
    dsimp only
    have hbg : ∀ j < 8, byte (ctrlWordN c (probePos cap p₀ k) (hA.word_of_lt hp)) j =
        c[(probePos cap p₀ k + j) % cap]! := fun j hj => hbyte hp hj
    generalize ctrlWordN c (probePos cap p₀ k) (hA.word_of_lt hp) = g at hbg ⊢
    have hmf := isMask_matchFree g
    by_cases hf : (matchFree g != 0) = true
    · rw [ite_eq_left hf]
      have hf0 : matchFree g ≠ 0 := by simpa using hf
      obtain ⟨hl8, hfl, -⟩ := lowestLane_spec hmf hf0
      rw [toNat_lowestLane_of_isMask hmf] at hl8 hfl
      rw [flag_matchFree _ hl8, decide_eq_true_iff, hbg _ hl8] at hfl
      have hr := Nat.mod_lt (probePos cap p₀ k + (lowestLane64 (matchFree g)).toNat) hc0
      have hfr : IsFree c[(probePos cap p₀ k + (lowestLane64 (matchFree g)).toNat) % cap]! :=
        (isCtrl_free_iff (hctrl _ hr)).mp hfl
      refine ⟨hr, hfr, k, by omega, _, hl8, rfl, fun k' hk' j' hj' he => ?_⟩
      exact hprev k' hk' j' hj' (Or.inl he)
    · rw [ite_eq_right hf]
      have hf0 : matchFree g = 0 := by simpa using hf
      have hnf : ∀ j < 8, ¬IsFree c[(probePos cap p₀ k + j) % cap]! := by
        intro j hj hfj
        have := (isMask_eq_zero_iff hmf).mp hf0 j hj
        rw [flag_matchFree _ hj, hbg _ hj] at this
        exact absurd (le_of_isFree hfj) (by simpa using this)
      have hprev' : ∀ k' < k + 1, ∀ j < 8, ¬IsFree c[(probePos cap p₀ k' + j) % cap]! :=
        fun k' hk' => if h : k' < k then hprev k' h else (show k' = k by omega) ▸ hnf
      by_cases hle : cap ≤ 8 * k + 8
      · exfalso
        obtain ⟨i, hi, hfi⟩ := hfree
        obtain ⟨k', hk', j, hj, he⟩ := probe_cover p₀ hn h8 hi
        exact hprev' k' (by omega) j hj (he ▸ hfi)
      · rw [dite_eq_right hle]
        exact ih (k + 1) (by omega) (by rw [probePos_succ, Nat.mul_succ]) (by omega) hprev'

/-- The capacity is below the slot count. -/
private theorem capacityOf_lt {cap : Nat} (h : 8 ≤ cap) : capacityOf cap < cap := by
  unfold capacityOf; omega

/-- A table whose slots are all FULL has an entry per slot. -/
private theorem entries_length_of_full {s : Slots α β} (hk : s.cap ≤ s.keys.size)
    (hv : s.cap ≤ s.vals.size) (h : ∀ i < s.cap, s.ctrl[i]! < 0x80) :
    s.entries.length = s.cap := by
  unfold Slots.entries
  rw [List.length_filterMap_eq_countP, List.countP_eq_length.mpr, List.length_range]
  intro i hi
  rw [List.mem_range] at hi
  have hc : i < s.ctrl.size := by unfold Slots.cap at hi; omega
  have hf := h i hi
  rw [getElem!_pos s.ctrl i hc] at hf
  rw [entryAt_some hc hf (by omega) (by omega)]
  rfl

/-- A mirrored table with fewer entries than slots has a free slot. -/
private theorem exists_free {s : Slots α β} (hctrl : s.CtrlOK) (hk : s.cap ≤ s.keys.size)
    (hv : s.cap ≤ s.vals.size) (hlt : s.entries.length < s.cap) :
    ∃ i < s.cap, IsFree s.ctrl[i]! := by
  refine Classical.byContradiction fun hne => ?_
  have hfull : ∀ i < s.cap, s.ctrl[i]! < 0x80 := fun i hi => by
    rcases isCtrl_iff.mp (hctrl i hi) with h | h | h
    · exact absurd ⟨i, hi, Or.inl h⟩ hne
    · exact absurd ⟨i, hi, Or.inr h⟩ hne
    · exact h
  have := entries_length_of_full hk hv hfull
  omega

section FreeSlot

variable [BEq α] [Hashable α] {s : Slots α β} {size gl : Nat} {mask : USize} {shift : UInt64}

/-- The free-slot probe from the home slot of `a`, in a table with room. -/
private theorem WF.findFreeN_home (wf : WF s size gl mask shift) (hgl : 0 < gl) (q : UInt64)
    {hA : CtrlN s.ctrl s.cap} {hp : homeN q s.cap < s.cap} :
    s.FreeSlot (homeN q s.cap) (findFreeN s.ctrl s.cap (homeN q s.cap) 0 hA hp) := by
  have hc := wf.cap_pos_of_gl hgl
  have hm := wf.mirrored hc
  have h8 := hm.le_cap
  have hk := wf.keys_size hc
  have hv := wf.vals_size hc
  have hctrl : ∀ i < s.cap, IsCtrl s.ctrl[i]! := wf.ctrl
  have hlt : s.entries.length < s.cap := by
    have := wf.room; have := wf.size_eq; have := capacityOf_lt h8; omega
  obtain ⟨hr, hfr, k₁, hk₁, j, hj, he, hprev⟩ :=
    findFreeN_spec hm hctrl (exists_free wf.ctrl (by omega) (by omega) hlt)
      (p₀ := homeN q s.cap) (s.cap / 8) 0 (hA := hA) (hp := hp) (by omega)
      (by rw [probePos_zero, homeN, Nat.mod_mod]) rfl (fun k' hk' => absurd hk' (by omega))
  exact ⟨hr, hfr, k₁, hk₁, j, hj, he, hprev⟩

end FreeSlot

/-- **`findFree` finds a free slot that the probe reaches**, in a table with room. -/
theorem WF.findFree_slot [BEq α] [Hashable α] {s : Slots α β} {size gl : Nat} {mask : USize}
    {shift : UInt64} (wf : WF s size gl mask shift) (hs : smallMask mask = true) {a : α}
    (h : FreshPre s gl a) :
    s.FreeSlot (homeN (hashBits shift a) s.cap)
      (findFree s.ctrl mask (homeU (hashBits shift a) mask) 0 (wf.loopU' hs).arr (and_mask_le _ _)
        stride_zero).toNat := by
  have hc := wf.cap_pos_of_gl h.room
  have hg := wf.geom hs hc
  have hm := wf.mirrored hc
  have hA : CtrlN s.ctrl s.cap := ⟨hc, by have := hm.size_eq; omega⟩
  have hp : (homeU (hashBits shift a) mask).toNat < s.cap := by
    rw [homeU_toNat hg]; exact Nat.mod_lt _ hc
  have e : (findFree s.ctrl mask (homeU (hashBits shift a) mask) 0 (wf.loopU' hs).arr
      (and_mask_le _ _) stride_zero).toNat =
      findFreeN s.ctrl s.cap (homeN (hashBits shift a) s.cap) 0 hA (Nat.mod_lt _ hc) :=
    (findFree_toNat hg hm.size_eq (hA' := hA) (hp' := hp)).trans
      (findFreeN_congr (homeU_toNat hg) USize.toNat_zero)
  rw [e]
  exact wf.findFreeN_home h.room _

/-- **`findFreeN` finds a free slot that the probe reaches**, in a table with room. -/
theorem WF.findFreeN_slot [BEq α] [Hashable α] {s : Slots α β} {size gl : Nat} {mask : USize}
    {shift : UInt64} (wf : WF s size gl mask shift) (hs : ¬smallMask mask = true) {a : α}
    (h : FreshPre s gl a) :
    s.FreeSlot (homeN (hashBits shift a) s.cap)
      (findFreeN s.ctrl (s.ctrl.size - 8) (homeN (hashBits shift a) (s.ctrl.size - 8)) 0
        (wf.ctrlN' hs) (Nat.mod_lt _ (wf.ctrlN' hs).pos)) :=
  wf.findFreeN_home h.room _

section Fresh

variable [BEq α] [Hashable α] {s : Slots α β} {size gl : Nat} {mask : USize} {shift : UInt64}

/-! Bounds of `insertFresh`'s writes (`findFree` ends at most at `mask + 1`, a cell of an
allocated table). -/

theorem WF.fresh_ctrl (wf : WF s size gl mask shift) (hs : smallMask mask = true) {a : α}
    (h : FreshPre s gl a) {pos stride : USize} {hA : ArrU s.ctrl mask}
    {hp : pos.toNat ≤ mask.toNat} {hs' : stride.toNat ≤ mask.toNat} :
    (findFree s.ctrl mask pos stride hA hp hs').toNat < s.ctrl.size := by
  have := freeBound s.ctrl pos stride hA hp hs'
  have := wf.mirror_lt (wf.cap_pos_of_gl h.room)
  omega

theorem WF.fresh_keys (wf : WF s size gl mask shift) (hs : smallMask mask = true) {a : α}
    (h : FreshPre s gl a) {pos stride : USize} {hA : ArrU s.ctrl mask}
    {hp : pos.toNat ≤ mask.toNat} {hs' : stride.toNat ≤ mask.toNat} :
    (findFree s.ctrl mask pos stride hA hp hs').toNat < s.keys.size := by
  have hc := wf.cap_pos_of_gl h.room
  have := freeBound s.ctrl pos stride hA hp hs'
  have := (wf.geom hs hc).mask_add_one
  have := wf.keys_size hc
  omega

theorem WF.fresh_vals (wf : WF s size gl mask shift) (hs : smallMask mask = true) {a : α}
    (h : FreshPre s gl a) {pos stride : USize} {hA : ArrU s.ctrl mask}
    {hp : pos.toNat ≤ mask.toNat} {hs' : stride.toNat ≤ mask.toNat} :
    (findFree s.ctrl mask pos stride hA hp hs').toNat < s.vals.size := by
  have hc := wf.cap_pos_of_gl h.room
  have := freeBound s.ctrl pos stride hA hp hs'
  have := (wf.geom hs hc).mask_add_one
  have := wf.vals_size hc
  omega

theorem WF.freshN_ctrl (wf : WF s size gl mask shift) (hs : ¬smallMask mask = true) {a : α}
    (h : FreshPre s gl a) {pos stride : Nat} {hA : CtrlN s.ctrl (s.ctrl.size - 8)}
    {hp : pos < s.ctrl.size - 8} :
    findFreeN s.ctrl (s.ctrl.size - 8) pos stride hA hp < s.ctrl.size := by
  have := freeBoundN s.ctrl pos stride hA hp
  have := wf.ctrl_size_ge
  omega

theorem WF.freshN_keys (wf : WF s size gl mask shift) (hs : ¬smallMask mask = true) {a : α}
    (h : FreshPre s gl a) {pos stride : Nat} {hA : CtrlN s.ctrl (s.ctrl.size - 8)}
    {hp : pos < s.ctrl.size - 8} :
    findFreeN s.ctrl (s.ctrl.size - 8) pos stride hA hp < s.keys.size := by
  have := freeBoundN s.ctrl pos stride hA hp
  have := wf.place_keysN (wf.cap_pos_of_gl h.room)
  omega

theorem WF.freshN_vals (wf : WF s size gl mask shift) (hs : ¬smallMask mask = true) {a : α}
    (h : FreshPre s gl a) {pos stride : Nat} {hA : CtrlN s.ctrl (s.ctrl.size - 8)}
    {hp : pos < s.ctrl.size - 8} :
    findFreeN s.ctrl (s.ctrl.size - 8) pos stride hA hp < s.vals.size := by
  have := freeBoundN s.ctrl pos stride hA hp
  have := wf.place_valsN (wf.cap_pos_of_gl h.room)
  omega

end Fresh

/-! ## The move loops -/

/-- A machine-word byte read is the `Nat` one. -/
private theorem buget_eq {c : ByteArray} {i : USize} (h : i.toNat < c.size) :
    c.uget i h = c[i.toNat] := by
  cases c; rfl

/-- The bytes after `setCtrlN`, at every index (`slotByte_setCtrlN` sees only the slots). -/
private theorem getElem_setCtrlN' {c : ByteArray} {cap i : Nat} {b : UInt8} {hi : i < c.size}
    {hm : cap + 8 ≤ c.size} {hc : 0 < cap} {k : Nat} (hk : k < c.size) :
    (setCtrlN c cap i b hi hm hc)[k]'(by rw [size_setCtrlN]; exact hk) =
      if (i + cap - 8) % cap + 8 = k then b else if i = k then b else c[k] := by
  simp only [setCtrlN, ByteArray.getElem_eq_getElem_data, ByteArray.data_set, Array.getElem_set]

private theorem setCtrlN_congr {c : ByteArray} {cap i i' : Nat} {b b' : UInt8} {hi : i < c.size}
    {hi' : i' < c.size} {hm : cap + 8 ≤ c.size} {hc : 0 < cap} (h1 : i = i') (h2 : b = b') :
    setCtrlN c cap i b hi hm hc = setCtrlN c cap i' b' hi' hm hc := by
  subst h1 h2; rfl

private theorem aset_congr {γ : Type w} {xs : Array γ} {i i' : Nat} {v v' : γ} {hi : i < xs.size}
    {hi' : i' < xs.size} (h1 : i = i') (h2 : v = v') : xs.set i v hi = xs.set i' v' hi' := by
  subst h1 h2; rfl

/-- `setCtrl` is `setCtrlN`, also at the placeholder slot `cap` (where both write byte `cap`
twice). -/
private theorem setCtrl_eq_setCtrlN' {c : ByteArray} {cap : Nat} {mask i : USize}
    (hg : Geom cap mask) (hsz : c.size = cap + 8) (hic : i.toNat ≤ cap) {b : UInt8}
    {h1 : i.toNat < c.size} {h2 : mask.toNat + 8 < c.size} {h3 : i.toNat < c.size}
    {h4 : cap + 8 ≤ c.size} {h5 : 0 < cap} :
    setCtrl c mask i b h1 h2 = setCtrlN c cap i.toNat b h3 h4 h5 := by
  rcases Nat.lt_or_eq_of_le hic with hlt | heq
  · exact setCtrl_eq_setCtrlN hg hsz hlt
  · have h8 := hg.le_cap
    have hls := hg.lt_size
    have h8u : (8 : USize).toNat = 8 :=
      USize.toNat_ofNat_of_lt (Nat.lt_of_lt_of_le (by decide) USize.le_size)
    have hus : USize.size = 2 ^ System.Platform.numBits := rfl
    have hmi : (((i - 8) &&& mask) + 8).toNat = cap := by
      have e := hg.toNat_sub_eight_and_mask i
      rw [heq, show cap + (cap - 8) = (cap - 8) + cap by omega, Nat.add_mod_right,
        Nat.mod_eq_of_lt (by omega)] at e
      rw [USize.toNat_add, e, h8u, ← hus, Nat.mod_eq_of_lt (by omega)]
      omega
    have hmn : (i.toNat + cap - 8) % cap + 8 = cap := by
      rw [heq, show cap + cap - 8 = (cap - 8) + cap by omega, Nat.add_mod_right,
        Nat.mod_eq_of_lt (by omega)]
      omega
    apply ByteArray.ext_getElem (by rw [size_setCtrl, size_setCtrlN])
    intro k hk hk'
    have hkc : k < c.size := by rw [size_setCtrl] at hk; exact hk
    rw [getElem_setCtrl _ _ _ _ _ _ _ hkc, getElem_setCtrlN' hkc, hmi, hmn, heq]

/-- The free-slot probe from a home slot, on machine words and on `Nat` indices. -/
private theorem findFree_home_toNat {nc : ByteArray} {ncap : Nat} {nmask : USize}
    (hg : Geom ncap nmask) (hsz : nc.size = ncap + 8) (q : UInt64) {hA : ArrU nc nmask}
    {hp : (homeU q nmask).toNat ≤ nmask.toNat} {hs : (0 : USize).toNat ≤ nmask.toNat}
    {hA' : CtrlN nc ncap} {hp' : homeN q ncap < ncap} :
    (findFree nc nmask (homeU q nmask) 0 hA hp hs).toNat =
      findFreeN nc ncap (homeN q ncap) 0 hA' hp' := by
  have hp'' : (homeU q nmask).toNat < ncap := by rw [homeU_toNat hg]; exact hp'
  exact (findFree_toNat (pos := homeU q nmask) (stride := 0) hg hsz (hA' := hA')
    (hp' := hp'')).trans (findFreeN_congr (homeU_toNat hg) USize.toNat_zero)

/-- The control write of a move, on machine words and on `Nat` indices. -/
private theorem setCtrl_findFree {nc : ByteArray} {ncap : Nat} {nmask : USize}
    (hg : Geom ncap nmask) (hsz : nc.size = ncap + 8) (q : UInt64) (b : UInt8)
    {hA : ArrU nc nmask} {hp : (homeU q nmask).toNat ≤ nmask.toNat}
    {hs : (0 : USize).toNat ≤ nmask.toNat} {hA' : CtrlN nc ncap} {hp' : homeN q ncap < ncap}
    {h1 : (findFree nc nmask (homeU q nmask) 0 hA hp hs).toNat < nc.size}
    {h2 : nmask.toNat + 8 < nc.size} {h3 : findFreeN nc ncap (homeN q ncap) 0 hA' hp' < nc.size}
    {h4 : ncap + 8 ≤ nc.size} {h5 : 0 < ncap} :
    setCtrl nc nmask (findFree nc nmask (homeU q nmask) 0 hA hp hs) b h1 h2 =
      setCtrlN nc ncap (findFreeN nc ncap (homeN q ncap) 0 hA' hp') b h3 h4 h5 := by
  have hb := freeBound nc (homeU q nmask) 0 hA hp hs
  have := hg.mask_add_one
  exact (setCtrl_eq_setCtrlN' hg hsz (by omega) (h3 := h1)).trans
    (setCtrlN_congr (findFree_home_toNat hg hsz q) rfl)

/-- The cell writes of a move, on machine words and on `Nat` indices. -/
private theorem uset_findFree {γ : Type w} {nc : ByteArray} {ncap : Nat} {nmask : USize}
    (hg : Geom ncap nmask) (hsz : nc.size = ncap + 8) (q : UInt64) {xs : Array γ} {v v' : γ}
    (hv : v = v') {hA : ArrU nc nmask} {hp : (homeU q nmask).toNat ≤ nmask.toNat}
    {hs : (0 : USize).toNat ≤ nmask.toNat} {hA' : CtrlN nc ncap} {hp' : homeN q ncap < ncap}
    {h1 : (findFree nc nmask (homeU q nmask) 0 hA hp hs).toNat < xs.size}
    {h2 : findFreeN nc ncap (homeN q ncap) 0 hA' hp' < xs.size} :
    xs.uset (findFree nc nmask (homeU q nmask) 0 hA hp hs) v h1 =
      xs.set (findFreeN nc ncap (homeN q ncap) 0 hA' hp') v' h2 := by
  rw [Array.uset_eq_set]
  exact aset_congr (findFree_home_toNat hg hsz q) hv

private theorem moveLoopN_congr [Hashable α] {oc : ByteArray} {ok : Array α} {ov : Array β}
    {ocap i i' : Nat} {nc nc' : ByteArray} {nk nk' : Array α} {nv nv' : Array β} {ncap : Nat}
    {nshift : UInt64} {hO : MoveSrcN oc ok ov ocap} {hN : MoveDstN nc nk nv ncap}
    {hN' : MoveDstN nc' nk' nv' ncap} {hff : FreeBoundN ncap} (h1 : i = i') (h2 : nc = nc')
    (h3 : nk = nk') (h4 : nv = nv') :
    moveLoopN oc ok ov ocap i nc nk nv ncap nshift hO hN hff =
      moveLoopN oc ok ov ocap i' nc' nk' nv' ncap nshift hO hN' hff := by
  subst h1 h2 h3 h4; rfl

/-- `moveLoop` is `moveLoopN` (suggested route; not used outside this file). -/
theorem moveLoop_eq_moveLoopN [Hashable α] {oc : ByteArray} {ok : Array α} {ov : Array β}
    {omask i : USize} {nc : ByteArray} {nk : Array α} {nv : Array β} {nmask : USize}
    {nshift : UInt64} {ocap ncap : Nat} (hog : omask.toNat + 1 = ocap) (hg : Geom ncap nmask)
    (hsz : nc.size = ncap + 8) (hi : i.toNat ≤ ocap) {hO : MoveSrcU oc ok ov omask}
    {hN : MoveDstU nc nk nv nmask} {hff : FreeBound nmask} {hO' : MoveSrcN oc ok ov ocap}
    {hN' : MoveDstN nc nk nv ncap} {hff' : FreeBoundN ncap} :
    moveLoop oc ok ov omask i nc nk nv nmask nshift hO hN hff =
      moveLoopN oc ok ov ocap i.toNat nc nk nv ncap nshift hO' hN' hff' := by
  have hsm := hO.small
  have hmc := hg.mask_add_one
  induction h : ocap - i.toNat using Nat.strongRecOn generalizing i nc nk nv with
  | _ n ih =>
    rw [moveLoop, moveLoopN]
    by_cases hgt : i > omask
    · have hlt : ¬i.toNat < ocap := by rw [GT.gt, USize.lt_iff_toNat_lt] at hgt; omega
      rw [dite_eq_left hgt, dite_eq_right hlt]
    · have hle := le_of_not_gt' hgt
      have hlt : i.toNat < ocap := by omega
      have e1 := toNat_add_one' (a := i) (by omega)
      rw [dite_eq_right hgt, dite_eq_left hlt, buget_eq (hO.ctrl_lt hgt)]
      by_cases hf : (oc[i.toNat]'(hO'.ctrl_lt hlt) &&& 0x80 == 0) = true
      · rw [ite_eq_left hf, ite_eq_left hf]
        dsimp only
        exact (ih (ocap - (i + 1).toNat) (by omega) (by rw [size_setCtrl]; exact hsz) (by omega)
          (hN' := hN'.write (size_setCtrl ..) (Array.size_uset ..) (Array.size_uset ..))
          rfl).trans (moveLoopN_congr e1 (setCtrl_findFree hg hsz _ _) (uset_findFree hg hsz _ rfl)
            (uset_findFree hg hsz _ rfl))
      · rw [ite_eq_right hf, ite_eq_right hf]
        exact (ih (ocap - (i + 1).toNat) (by omega) hsz (by omega) (hN' := hN') rfl).trans
          (moveLoopN_congr e1 rfl rfl rfl)

/-! ## The move loops: the invariant -/

/-- The entries of the slots of `s` below `i`, in slot order. -/
private def entriesBelow (s : Slots α β) (i : Nat) : List ((_ : α) × β) :=
  (List.range i).filterMap s.entryAt

private theorem entriesBelow_succ (s : Slots α β) (i : Nat) :
    entriesBelow s (i + 1) = entriesBelow s i ++ (s.entryAt i).toList := by
  unfold entriesBelow
  rw [List.range_succ, List.filterMap_append, List.filterMap_cons, List.filterMap_nil]
  cases s.entryAt i <;> rfl

private theorem length_entriesBelow_le (s : Slots α β) {i : Nat} :
    ∀ {i' : Nat}, i ≤ i' → (entriesBelow s i).length ≤ (entriesBelow s i').length
  | 0, h => by
    obtain rfl : i = 0 := by omega
    exact Nat.le_refl _
  | i' + 1, h => by
    rcases Nat.lt_or_eq_of_le h with h | rfl
    · rw [entriesBelow_succ, List.length_append]
      have := length_entriesBelow_le s (i := i) (i' := i') (by omega)
      omega
    · exact Nat.le_refl _

private theorem mem_entriesBelow {s : Slots α β} {i : Nat} {e : (_ : α) × β}
    (he : e ∈ entriesBelow s i) : ∃ q < i, s.entryAt q = some e := by
  obtain ⟨q, hq, hqe⟩ := List.mem_filterMap.mp he
  exact ⟨q, List.mem_range.mp hq, hqe⟩

private theorem getElem?_eq_getElem! {c : ByteArray} {x : Nat} (hx : x < c.size) :
    c[x]? = some c[x]! := by
  rw [getElem?_pos c x hx, getElem!_pos c x hx]

/-- What an entry says about its slot. -/
private theorem entryAt_eq_some {s : Slots α β} {x : Nat} {e : (_ : α) × β}
    (h : s.entryAt x = some e) :
    x < s.ctrl.size ∧ s.ctrl[x]! < 0x80 ∧ s.keys[x]? = some e.1 ∧ s.vals[x]? = some e.2 := by
  unfold Slots.entryAt at h
  by_cases hx : x < s.ctrl.size
  · rw [getElem?_eq_getElem! hx] at h
    simp only at h
    by_cases hc : s.ctrl[x]! < 0x80
    · rw [ite_eq_left hc] at h
      refine ⟨hx, hc, ?_⟩
      cases hk : s.keys[x]? with
      | none => rw [hk] at h; simp at h
      | some k =>
        cases hv : s.vals[x]? with
        | none => rw [hk, hv] at h; simp at h
        | some v =>
          rw [hk, hv] at h
          simp only [Option.bind_some, Option.map_some, Option.some.injEq] at h
          subst h
          exact ⟨rfl, rfl⟩
    · rw [ite_eq_right hc] at h; exact absurd h (by simp)
  · rw [getElem?_neg s.ctrl x hx] at h; exact absurd h (by simp)

private theorem entryAt_congr {s t : Slots α β} {x : Nat} (hc : s.ctrl[x]? = t.ctrl[x]?)
    (hk : s.keys[x]? = t.keys[x]?) (hv : s.vals[x]? = t.vals[x]?) : s.entryAt x = t.entryAt x := by
  unfold Slots.entryAt; rw [hc, hk, hv]

private theorem filterMap_congr' {γ : Type _} {δ : Type _} {f g : γ → Option δ} :
    ∀ {l : List γ}, (∀ x ∈ l, f x = g x) → l.filterMap f = l.filterMap g
  | [], _ => rfl
  | x :: l, h => by
    rw [List.filterMap_cons, List.filterMap_cons, h x List.mem_cons_self,
      filterMap_congr' (fun y hy => h y (List.mem_cons_of_mem _ hy))]

/-- Filling one slot of a list of distinct slots adds its entry. -/
private theorem filterMap_perm_update {δ : Type w} {f g : Nat → Option δ} {e : δ} {j : Nat}
    (hf : f j = none) (hg : g j = some e) :
    ∀ {l : List Nat}, l.Nodup → j ∈ l → (∀ x ∈ l, x ≠ j → g x = f x) →
      (l.filterMap g).Perm (e :: l.filterMap f)
  | [], _, hj, _ => absurd hj List.not_mem_nil
  | x :: l, hnd, hj, hfg => by
    rw [List.nodup_cons] at hnd
    by_cases hxj : x = j
    · subst hxj
      rw [List.filterMap_cons, List.filterMap_cons, hf, hg]
      simp only
      rw [filterMap_congr' (fun y hy => hfg y (List.mem_cons_of_mem _ hy)
        (fun e => hnd.1 (e ▸ hy)))]
    · have hjl : j ∈ l := by
        rcases List.mem_cons.mp hj with h | h
        · exact absurd h.symm hxj
        · exact h
      have ih := filterMap_perm_update hf hg hnd.2 hjl
        (fun y hy => hfg y (List.mem_cons_of_mem _ hy))
      rw [List.filterMap_cons, List.filterMap_cons, hfg x List.mem_cons_self hxj]
      cases f x with
      | none => exact ih
      | some a => exact (ih.cons a).trans (List.Perm.swap e a _)

/-- The new arrays of a rebuild once the old slots below `i` are moved: mirrored, the right
sizes, only EMPTY and FULL bytes, the tags of the new shift, the probe invariant, distinct keys
(lawful instances), and the entries of the old slots below `i`. -/
private structure MoveInv [BEq α] [Hashable α] (s : Slots α β) (i : Nat) (t : Slots α β)
    (ncap : Nat) (nshift : UInt64) : Prop where
  le : i ≤ s.cap
  mirrored : Mirrored t.ctrl ncap
  keys_size : t.keys.size = ncap + 1
  vals_size : t.vals.size = ncap + 1
  bytes : ∀ x < ncap, t.ctrl[x]! = EMPTY ∨ t.ctrl[x]! < 0x80
  tag : t.TagInv nshift
  probe : t.ProbeInv nshift
  distinct [EquivBEq α] [LawfulHashable α] : t.Distinct
  perm : t.entries.Perm (entriesBelow s i)

section MoveInv

variable [BEq α] [Hashable α] {s t : Slots α β} {i ncap : Nat} {nshift : UInt64}

private theorem MoveInv.cap_eq (inv : MoveInv s i t ncap nshift) : t.cap = ncap := by
  unfold Slots.cap; rw [inv.mirrored.size_eq, Nat.add_sub_cancel]

private theorem MoveInv.ctrlOK (inv : MoveInv s i t ncap nshift) : t.CtrlOK := fun x hx => by
  rw [inv.cap_eq] at hx
  rcases inv.bytes x hx with h | h
  · rw [h]; exact isCtrl_EMPTY
  · exact isCtrl_of_lt h

private theorem MoveInv.numDeleted (inv : MoveInv s i t ncap nshift) : t.numDeleted = 0 := by
  unfold Slots.numDeleted
  rw [List.countP_eq_zero]
  intro x hx
  rw [List.mem_range, inv.cap_eq] at hx
  rcases inv.bytes x hx with h | h
  · rw [h]; simp only [beq_iff_eq]; exact fun e => DELETED_ne_EMPTY e.symm
  · simp only [beq_iff_eq]; intro e; rw [e] at h; exact DELETED_not_lt h

/-- The old slots below `i` are FULL in the new arrays only with keys of old slots below `i`. -/
private theorem MoveInv.old_of_full (inv : MoveInv s i t ncap nshift) {y : Nat} {k : α}
    (hy : t.IsFull y) (hk : t.keys[y]? = some k) :
    ∃ q < i, s.IsFull q ∧ s.keys[q]? = some k := by
  have hyc := hy.1
  rw [inv.cap_eq] at hyc
  have hyv : y < t.vals.size := by rw [inv.vals_size]; omega
  have hyk : y < t.keys.size := by rw [inv.keys_size]; omega
  have hyc' : y < t.ctrl.size := by rw [inv.mirrored.size_eq]; omega
  have hk' : t.keys[y] = k := by rw [getElem?_pos t.keys y hyk] at hk; exact Option.some.inj hk
  have hf := hy.2
  rw [getElem!_pos t.ctrl y hyc'] at hf
  have he := entryAt_some hyc' hf hyk hyv
  have hmem : (⟨t.keys[y], t.vals[y]⟩ : (_ : α) × β) ∈ t.entries :=
    List.mem_filterMap.mpr ⟨y, List.mem_range.mpr hy.1, he⟩
  obtain ⟨q, hq, hqe⟩ := mem_entriesBelow (inv.perm.subset hmem)
  obtain ⟨-, hqf, hqk, -⟩ := entryAt_eq_some hqe
  exact ⟨q, hq, ⟨by have := inv.le; omega, hqf⟩, by rw [hqk, hk']⟩

/-- Skipping an old slot without an entry. -/
private theorem MoveInv.skip (inv : MoveInv s i t ncap nshift) (hi : i < s.cap)
    (he : s.entryAt i = none) : MoveInv s (i + 1) t ncap nshift :=
  { inv with
    le := hi
    perm := by rw [entriesBelow_succ, he, Option.toList_none, List.append_nil]; exact inv.perm }

end MoveInv

/-- **One move**: the entry `⟨k, v⟩` of old slot `i` written at a free slot `j` that the probe
of `k` in the new arrays reaches keeps the invariant. -/
private theorem MoveInv.write [BEq α] [Hashable α] {s : Slots α β} {size gl : Nat}
    {mask : USize} {shift : UInt64} (wf : WF s size gl mask shift) {i : Nat} {nc : ByteArray}
    {nk : Array α} {nv : Array β} {ncap : Nat} {nshift : UInt64}
    (inv : MoveInv s i ⟨nc, nk, nv⟩ ncap nshift) (hi : i < s.cap) {k : α} {v : β}
    (he : s.entryAt i = some ⟨k, v⟩) {j : Nat} (hj : j < ncap) (hfr : IsFree nc[j]!)
    (hreach : ∃ k₁ < ncap / 8, ∃ j₁ < 8,
      (probePos ncap (homeN (hashBits nshift k) ncap) k₁ + j₁) % ncap = j ∧
      ∀ k' < k₁, ∀ j' < 8,
        nc[(probePos ncap (homeN (hashBits nshift k) ncap) k' + j') % ncap]! ≠ EMPTY)
    {h1 : j < nc.size} {h2 : ncap + 8 ≤ nc.size} {h3 : 0 < ncap} {h4 : j < nk.size}
    {h5 : j < nv.size} :
    MoveInv s (i + 1) ⟨setCtrlN nc ncap j (tagOf (hashBits nshift k)) h1 h2 h3, nk.set j k h4,
      nv.set j v h5⟩ ncap nshift := by
  have hm := inv.mirrored
  have hc : (Slots.mk nc nk nv).cap = ncap := inv.cap_eq
  have hsz := hm.size_eq
  have hc' : (Slots.mk (setCtrlN nc ncap j (tagOf (hashBits nshift k)) h1 h2 h3) (nk.set j k h4)
      (nv.set j v h5)).cap = ncap := by
    unfold Slots.cap; simp only [size_setCtrlN]; rw [hsz, Nat.add_sub_cancel]
  -- the new control bytes
  have hb : ∀ x < ncap, (setCtrlN nc ncap j (tagOf (hashBits nshift k)) h1 h2 h3)[x]! =
      if x = j then tagOf (hashBits nshift k) else nc[x]! := fun x hx => by
    have e := slotByte_setCtrlN hm hj (tagOf (hashBits nshift k)) (hi := h1) (hm := h2) (hc := h3) x
    rw [slotByte_def, slotByte_def, Nat.mod_eq_of_lt hx] at e
    exact e
  have hk : ∀ x, (nk.set j k h4)[x]? = if j = x then some k else nk[x]? := fun x =>
    Array.getElem?_set h4
  have hv : ∀ x, (nv.set j v h5)[x]? = if j = x then some v else nv[x]? := fun x =>
    Array.getElem?_set h5
  have hne : ∀ y < ncap, nc[y]! ≠ EMPTY →
      (setCtrlN nc ncap j (tagOf (hashBits nshift k)) h1 h2 h3)[y]! ≠ EMPTY := fun y hy hny => by
    rw [hb y hy]
    split
    · intro e; exact not_lt_EMPTY (e ▸ tagOf_lt _)
    · exact hny
  -- reaching in the new arrays
  have hreach' : ∀ p y, (Slots.mk nc nk nv).Reach p y →
      (Slots.mk (setCtrlN nc ncap j (tagOf (hashBits nshift k)) h1 h2 h3) (nk.set j k h4)
        (nv.set j v h5)).Reach p y := fun p y hr => by
    unfold Slots.Reach at hr ⊢
    rw [hc] at hr
    rw [hc']
    obtain ⟨k₁, hk₁, j₁, hj₁, heq, hpr⟩ := hr
    exact ⟨k₁, hk₁, j₁, hj₁, heq, fun k' hk' j' hj' =>
      hne _ (Nat.mod_lt _ h3) (hpr k' hk' j' hj')⟩
  -- full slots of the new arrays
  have hfull : ∀ x, x ≠ j →
      (Slots.mk (setCtrlN nc ncap j (tagOf (hashBits nshift k)) h1 h2 h3) (nk.set j k h4)
        (nv.set j v h5)).IsFull x → (Slots.mk nc nk nv).IsFull x := fun x hxj hx => by
    obtain ⟨hx1, hx2⟩ := hx
    rw [hc'] at hx1
    refine ⟨by rw [hc]; exact hx1, ?_⟩
    have := hb x hx1
    rw [ite_eq_right hxj] at this
    simp only at hx2
    rw [this] at hx2
    exact hx2
  have hkx : ∀ x, x ≠ j → (nk.set j k h4)[x]? = nk[x]? := fun x hxj => by
    rw [hk x, ite_eq_right (Ne.symm hxj)]
  have hkj : (nk.set j k h4)[j]? = some k := by rw [hk j, ite_eq_left rfl]
  -- the old slot `i`
  obtain ⟨-, hif, hik, -⟩ := entryAt_eq_some he
  have hfi : s.IsFull i := ⟨hi, hif⟩
  refine {
    le := hi
    mirrored := mirrored_setCtrlN hm hj _ (hi := h1) (hm := h2) (hc := h3)
    keys_size := by rw [Array.size_set]; exact inv.keys_size
    vals_size := by rw [Array.size_set]; exact inv.vals_size
    bytes := fun x hx => by
      rw [hb x hx]
      split
      · exact Or.inr (tagOf_lt _)
      · exact inv.bytes x hx
    tag := ?_
    probe := ?_
    distinct := ?_
    perm := ?_ }
  · intro x k₁ hx hkx₁
    by_cases hxj : x = j
    · subst hxj
      rw [hkj] at hkx₁
      cases hkx₁
      simp only
      rw [hb x hj, ite_eq_left rfl]
    · simp only at hkx₁ ⊢
      rw [hkx x hxj] at hkx₁
      have := inv.tag x k₁ (hfull x hxj hx) hkx₁
      simp only at this
      rw [hb x (by have := hx.1; rw [hc'] at this; exact this), ite_eq_right hxj, this]
  · intro x k₁ hx hkx₁
    by_cases hxj : x = j
    · subst hxj
      rw [hkj] at hkx₁
      cases hkx₁
      rw [hc']
      unfold Slots.Reach
      rw [hc']
      obtain ⟨k₁, hk₁, j₁, hj₁, heq, hpr⟩ := hreach
      exact ⟨k₁, hk₁, j₁, hj₁, heq, fun k' hk' j' hj' =>
        hne _ (Nat.mod_lt _ h3) (hpr k' hk' j' hj')⟩
    · simp only at hkx₁
      rw [hkx x hxj] at hkx₁
      have := inv.probe x k₁ (hfull x hxj hx) hkx₁
      rw [hc] at this
      rw [hc']
      exact hreach' _ _ this
  · intro _ _ x y k₁ k₂ hx hy hkx₁ hky₂ hbeq
    simp only at hkx₁ hky₂
    by_cases hxj : x = j
    · by_cases hyj : y = j
      · rw [hxj, hyj]
      · subst hxj
        rw [hkj] at hkx₁
        cases hkx₁
        rw [hkx y hyj] at hky₂
        obtain ⟨q, hq, hqf, hqk⟩ := inv.old_of_full (hfull y hyj hy) hky₂
        have := wf.distinct i q k k₂ hfi hqf hik hqk hbeq
        omega
    · by_cases hyj : y = j
      · subst hyj
        rw [hkj] at hky₂
        cases hky₂
        rw [hkx x hxj] at hkx₁
        obtain ⟨q, hq, hqf, hqk⟩ := inv.old_of_full (hfull x hxj hx) hkx₁
        have := wf.distinct q i k₁ k hqf hfi hqk hik hbeq
        omega
      · rw [hkx x hxj] at hkx₁
        rw [hkx y hyj] at hky₂
        exact inv.distinct x y k₁ k₂ (hfull x hxj hx) (hfull y hyj hy) hkx₁ hky₂ hbeq
  · -- the entries
    have hjc : j < (Slots.mk nc nk nv).ctrl.size := h1
    have hnone : (Slots.mk nc nk nv).entryAt j = none :=
      entryAt_none (fun h => absurd (le_of_isFree hfr) (by
        rw [UInt8.not_le]; exact h))
    have hsome : (Slots.mk (setCtrlN nc ncap j (tagOf (hashBits nshift k)) h1 h2 h3)
        (nk.set j k h4) (nv.set j v h5)).entryAt j = some ⟨k, v⟩ := by
      unfold Slots.entryAt
      simp only
      rw [getElem?_eq_getElem! (by rw [size_setCtrlN]; exact h1), hb j hj, ite_eq_left rfl]
      simp only [tagOf_lt, ite_true, hkj, hv j, Option.bind_some, Option.map_some]
    have hrest : ∀ x ∈ List.range ncap, x ≠ j →
        (Slots.mk (setCtrlN nc ncap j (tagOf (hashBits nshift k)) h1 h2 h3) (nk.set j k h4)
          (nv.set j v h5)).entryAt x = (Slots.mk nc nk nv).entryAt x := fun x hx hxj => by
      rw [List.mem_range] at hx
      apply entryAt_congr
      · simp only
        rw [getElem?_eq_getElem! (by rw [size_setCtrlN]; omega), getElem?_eq_getElem! (by omega),
          hb x hx, ite_eq_right hxj]
      · exact hkx x hxj
      · simp only; rw [hv x, ite_eq_right (Ne.symm hxj)]
    have hp := filterMap_perm_update hnone hsome List.nodup_range (List.mem_range.mpr hj) hrest
    unfold Slots.entries
    rw [hc']
    refine hp.trans ?_
    have hpi := inv.perm
    unfold Slots.entries at hpi
    rw [hc] at hpi
    rw [entriesBelow_succ, he]
    exact (hpi.cons _).trans (List.perm_append_singleton _ _).symm

/-- The fresh arrays satisfy the invariant before any move. -/
private theorem moveInv_init [BEq α] [Hashable α] (s : Slots α β) {lg : Nat} (h3 : 3 ≤ lg)
    (k0 : α) (v0 : β) (nshift : UInt64) :
    MoveInv s 0 ⟨emptyCtrl ((2 : Nat) ^ lg), Array.replicate ((2 : Nat) ^ lg + 1) k0,
      Array.replicate ((2 : Nat) ^ lg + 1) v0⟩ ((2 : Nat) ^ lg) nshift := by
  have hm := mirrored_emptyCtrl h3
  have hcap : (Slots.mk (emptyCtrl ((2 : Nat) ^ lg)) (Array.replicate ((2 : Nat) ^ lg + 1) k0)
      (Array.replicate ((2 : Nat) ^ lg + 1) v0)).cap = 2 ^ lg := by
    unfold Slots.cap; rw [size_emptyCtrl h3, Nat.add_sub_cancel]
  have nf : ∀ x, ¬(Slots.mk (emptyCtrl ((2 : Nat) ^ lg))
      (Array.replicate ((2 : Nat) ^ lg + 1) k0)
      (Array.replicate ((2 : Nat) ^ lg + 1) v0)).IsFull x := by
    rintro x ⟨hx, hf⟩
    rw [hcap] at hx
    exact not_lt_EMPTY (getElem!_emptyCtrl h3 (i := x) (by omega) ▸ hf)
  have he := (WF.empty (α := α) (β := β) k0 v0 h3).size_eq
  exact {
    le := Nat.zero_le _
    mirrored := hm
    keys_size := Array.size_replicate
    vals_size := Array.size_replicate
    bytes := fun x hx => Or.inl (getElem!_emptyCtrl h3 (by omega))
    tag := fun x _ hx => absurd hx (nf x)
    probe := fun x _ hx => absurd hx (nf x)
    distinct := by intro _ _ x _ _ _ hx; exact absurd hx (nf x)
    perm := by rw [List.eq_nil_of_length_eq_zero he.symm]; exact List.Perm.nil }

/-- The result of a move loop, as slots. -/
private def toSlots (r : ByteArray × Array α × Array β) : Slots α β := ⟨r.1, r.2.1, r.2.2⟩

/-- **The move loop on `Nat` indices keeps the invariant** to the last old slot. -/
private theorem moveLoopN_inv [BEq α] [Hashable α] {ctrl : ByteArray} {keys : Array α}
    {vals : Array β} {size gl : Nat} {mask : USize} {shift : UInt64}
    (wf : WF ⟨ctrl, keys, vals⟩ size gl mask shift) {ncap : Nat} {nshift : UInt64}
    (hsize : size ≤ capacityOf ncap) :
    ∀ (d i : Nat) {nc : ByteArray} {nk : Array α} {nv : Array β}
      {hO : MoveSrcN ctrl keys vals (ctrl.size - 8)} {hN : MoveDstN nc nk nv ncap}
      {hff : FreeBoundN ncap},
      i + d = ctrl.size - 8 → MoveInv ⟨ctrl, keys, vals⟩ i ⟨nc, nk, nv⟩ ncap nshift →
      MoveInv ⟨ctrl, keys, vals⟩ (ctrl.size - 8)
        (toSlots (moveLoopN ctrl keys vals (ctrl.size - 8) i nc nk nv ncap nshift hO hN hff))
        ncap nshift
  | 0, i, nc, nk, nv, hO, hN, hff, hid, inv => by
    obtain rfl : i = ctrl.size - 8 := by omega
    rw [moveLoopN, dite_eq_right (Nat.lt_irrefl _)]
    exact inv
  | d + 1, i, nc, nk, nv, hO, hN, hff, hid, inv => by
    have hlt : i < ctrl.size - 8 := by omega
    rw [moveLoopN, dite_eq_left hlt]
    have hik := hO.keys_lt hlt
    have hiv := hO.vals_lt hlt
    have hic := hO.ctrl_lt hlt
    by_cases hf : (ctrl[i]'hic &&& 0x80 == 0) = true
    · rw [ite_eq_left hf]
      dsimp only
      have hfull : ctrl[i] < 0x80 := by rw [and80_eq_zero] at hf; simpa using hf
      have he : (Slots.mk ctrl keys vals).entryAt i = some ⟨keys[i], vals[i]⟩ :=
        entryAt_some hic hfull hik hiv
      have h8 := inv.mirrored.le_cap
      have hlen : (Slots.mk nc nk nv).entries.length < (Slots.mk nc nk nv).cap := by
        rw [inv.perm.length_eq, inv.cap_eq]
        have := length_entriesBelow_le (Slots.mk ctrl keys vals) (i := i) (i' := ctrl.size - 8)
          (by omega)
        have hse : (entriesBelow (Slots.mk ctrl keys vals) (ctrl.size - 8)).length = size :=
          wf.size_eq.symm
        have := capacityOf_lt h8
        omega
      have hfree := exists_free inv.ctrlOK (by rw [inv.cap_eq, inv.keys_size]; omega)
        (by rw [inv.cap_eq, inv.vals_size]; omega) hlen
      rw [inv.cap_eq] at hfree
      obtain ⟨hr, hfr, hreach⟩ := findFreeN_spec inv.mirrored
        (fun x hx => inv.ctrlOK x (by rw [inv.cap_eq]; exact hx)) hfree
        (p₀ := homeN (hashBits nshift keys[i]) ncap) (ncap / 8) 0
        (pos := homeN (hashBits nshift keys[i]) ncap) (stride := 0) (hA := hN.ctrlN)
        (hp := Nat.mod_lt _ hN.pos) (by omega) (by rw [probePos_zero, homeN, Nat.mod_mod]) rfl
        (fun _ h => absurd h (Nat.not_lt_zero _))
      exact moveLoopN_inv wf hsize d (i + 1) (by omega) (inv.write wf hlt he hr hfr hreach)
    · rw [ite_eq_right hf]
      have hnf : ¬ctrl[i] < 0x80 := by rw [and80_eq_zero] at hf; simpa using hf
      exact moveLoopN_inv wf hsize d (i + 1) (by omega)
        (inv.skip hlt (entryAt_none (by rw [getElem!_pos ctrl i hic]; exact hnf)))

/-- **The rebuild's move** (either loop) ends with the invariant over all old slots. -/
private theorem rebuild_inv [BEq α] [Hashable α] {ctrl : ByteArray} {keys : Array α}
    {vals : Array β} {size gl : Nat} {mask : USize} {shift : UInt64}
    (wf : WF ⟨ctrl, keys, vals⟩ size gl mask shift) {lg : Nat} {k0 : α} {v0 : β}
    (h : RebuildPre ⟨ctrl, keys, vals⟩ size lg) {nc : ByteArray} {nk : Array α} {nv : Array β}
    (hm : (if hs : smallMask (((2 : Nat) ^ lg - 1).toUSize) = true then
        moveLoop ctrl keys vals mask 0 (ctrl.propagateMark (emptyCtrl ((2 : Nat) ^ lg)))
          (keys.propagateMark (Array.replicate ((2 : Nat) ^ lg + 1) k0))
          (vals.propagateMark (Array.replicate ((2 : Nat) ^ lg + 1) v0))
          (((2 : Nat) ^ lg - 1).toUSize) ((57 - lg).toUInt64) (wf.moveSrcU h hs)
          (moveDstU h.three_le hs) freeBound
      else
        moveLoopN ctrl keys vals (ctrl.size - 8) 0 (ctrl.propagateMark (emptyCtrl ((2 : Nat) ^ lg)))
          (keys.propagateMark (Array.replicate ((2 : Nat) ^ lg + 1) k0))
          (vals.propagateMark (Array.replicate ((2 : Nat) ^ lg + 1) v0)) ((2 : Nat) ^ lg)
          ((57 - lg).toUInt64) wf.moveSrcN (moveDstN h.three_le) freeBoundN) = (nc, nk, nv)) :
    MoveInv ⟨ctrl, keys, vals⟩ (ctrl.size - 8) ⟨nc, nk, nv⟩ ((2 : Nat) ^ lg)
      ((57 - lg).toUInt64) := by
  have h3 := h.three_le
  have key : moveLoopN ctrl keys vals (ctrl.size - 8) 0
      (ctrl.propagateMark (emptyCtrl ((2 : Nat) ^ lg)))
      (keys.propagateMark (Array.replicate ((2 : Nat) ^ lg + 1) k0))
      (vals.propagateMark (Array.replicate ((2 : Nat) ^ lg + 1) v0)) ((2 : Nat) ^ lg)
      ((57 - lg).toUInt64) wf.moveSrcN (moveDstN h.three_le) freeBoundN = (nc, nk, nv) := by
    by_cases hs : smallMask (((2 : Nat) ^ lg - 1).toUSize) = true
    · rw [dite_eq_left hs] at hm
      have hl := lg_le_of_smallMask hs
      obtain ⟨lg₀, ha⟩ := wf.alloc h.alloc
      have hsz0 := ha.mirrored.size_eq
      have hcl := h.cap_le
      unfold Slots.cap at hcl
      simp only at hsz0 hcl
      have h1 : 2 ^ lg ≤ 2 ^ 31 := Nat.pow_le_pow_right (by decide) hl
      have hl0 : lg₀ ≤ 31 :=
        (Nat.pow_le_pow_iff_right (show 1 < 2 by decide)).mp (show 2 ^ lg₀ ≤ 2 ^ 31 by omega)
      have hog : mask.toNat + 1 = ctrl.size - 8 := by
        rw [ha.mask_eq, toNat_mask_of_le hl0]
        have := Nat.two_pow_pos lg₀
        omega
      have e := moveLoop_eq_moveLoopN (i := 0) hog (geom_of_le h3 hl) (size_emptyCtrl h3)
        (Nat.zero_le _) (hO := wf.moveSrcU h hs) (hN := moveDstU h.three_le hs) (hff := freeBound)
        (hO' := wf.moveSrcN) (hN' := moveDstN h.three_le) (hff' := freeBoundN)
        (nc := ctrl.propagateMark (emptyCtrl ((2 : Nat) ^ lg)))
        (nk := keys.propagateMark (Array.replicate ((2 : Nat) ^ lg + 1) k0))
        (nv := vals.propagateMark (Array.replicate ((2 : Nat) ^ lg + 1) v0))
        (nshift := (57 - lg).toUInt64)
      rw [USize.toNat_zero] at e
      exact e.symm.trans hm
    · rw [dite_eq_right hs] at hm
      exact hm
  have := moveLoopN_inv wf h.size_le (ctrl.size - 8) 0
    (nc := ctrl.propagateMark (emptyCtrl ((2 : Nat) ^ lg)))
    (nk := keys.propagateMark (Array.replicate ((2 : Nat) ^ lg + 1) k0))
    (nv := vals.propagateMark (Array.replicate ((2 : Nat) ^ lg + 1) v0))
    (hO := wf.moveSrcN) (hN := moveDstN h.three_le) (hff := freeBoundN) (Nat.zero_add _)
    (moveInv_init _ h3 k0 v0 ((57 - lg).toUInt64))
  rw [key] at this
  exact this

section Move

variable [BEq α] [Hashable α] {ctrl : ByteArray} {keys : Array α} {vals : Array β}
  {size gl : Nat} {mask : USize} {shift : UInt64}

/-- **The rebuild builds a well-formed table**: `size` entries in `2 ^ lg` slots, no
tombstones, `growthLeft = capacity - size`. The hypothesis is the move of `Build.lean`'s
`rebuild`, word for word. -/
theorem WF.rebuild (wf : WF ⟨ctrl, keys, vals⟩ size gl mask shift) {lg : Nat} {k0 : α} {v0 : β}
    (h : RebuildPre ⟨ctrl, keys, vals⟩ size lg) {nc : ByteArray} {nk : Array α} {nv : Array β}
    (hm : (if hs : smallMask (((2 : Nat) ^ lg - 1).toUSize) = true then
        moveLoop ctrl keys vals mask 0 (ctrl.propagateMark (emptyCtrl ((2 : Nat) ^ lg)))
          (keys.propagateMark (Array.replicate ((2 : Nat) ^ lg + 1) k0))
          (vals.propagateMark (Array.replicate ((2 : Nat) ^ lg + 1) v0))
          (((2 : Nat) ^ lg - 1).toUSize) ((57 - lg).toUInt64) (wf.moveSrcU h hs)
          (moveDstU h.three_le hs) freeBound
      else
        moveLoopN ctrl keys vals (ctrl.size - 8) 0 (ctrl.propagateMark (emptyCtrl ((2 : Nat) ^ lg)))
          (keys.propagateMark (Array.replicate ((2 : Nat) ^ lg + 1) k0))
          (vals.propagateMark (Array.replicate ((2 : Nat) ^ lg + 1) v0)) ((2 : Nat) ^ lg)
          ((57 - lg).toUInt64) wf.moveSrcN (moveDstN h.three_le) freeBoundN) = (nc, nk, nv)) :
    WF ⟨nc, nk, nv⟩ size (capacityOf ((2 : Nat) ^ lg) - size) (((2 : Nat) ^ lg - 1).toUSize)
      ((57 - lg).toUInt64) := by
  have inv := rebuild_inv wf h hm
  have hc := inv.cap_eq
  exact {
    shape := Or.inr ⟨lg, h.three_le, inv.mirrored, inv.keys_size, inv.vals_size, rfl, rfl⟩
    ctrl := inv.ctrlOK
    tag := inv.tag
    size_eq := by rw [inv.perm.length_eq]; exact wf.size_eq
    room := by rw [inv.numDeleted, hc]; have := h.size_le; omega
    distinct := inv.distinct
    probe := inv.probe }

/-- **The rebuild keeps the entries**, up to order (no lawfulness: no key is compared). -/
theorem rebuild_perm_raw (wf : WF ⟨ctrl, keys, vals⟩ size gl mask shift) {lg : Nat} {k0 : α}
    {v0 : β} (h : RebuildPre ⟨ctrl, keys, vals⟩ size lg) {nc : ByteArray} {nk : Array α}
    {nv : Array β}
    (hm : (if hs : smallMask (((2 : Nat) ^ lg - 1).toUSize) = true then
        moveLoop ctrl keys vals mask 0 (ctrl.propagateMark (emptyCtrl ((2 : Nat) ^ lg)))
          (keys.propagateMark (Array.replicate ((2 : Nat) ^ lg + 1) k0))
          (vals.propagateMark (Array.replicate ((2 : Nat) ^ lg + 1) v0))
          (((2 : Nat) ^ lg - 1).toUSize) ((57 - lg).toUInt64) (wf.moveSrcU h hs)
          (moveDstU h.three_le hs) freeBound
      else
        moveLoopN ctrl keys vals (ctrl.size - 8) 0 (ctrl.propagateMark (emptyCtrl ((2 : Nat) ^ lg)))
          (keys.propagateMark (Array.replicate ((2 : Nat) ^ lg + 1) k0))
          (vals.propagateMark (Array.replicate ((2 : Nat) ^ lg + 1) v0)) ((2 : Nat) ^ lg)
          ((57 - lg).toUInt64) wf.moveSrcN (moveDstN h.three_le) freeBoundN) = (nc, nk, nv)) :
    (Slots.entries ⟨nc, nk, nv⟩).Perm (Slots.entries ⟨ctrl, keys, vals⟩) :=
  (rebuild_inv wf h hm).perm

/-- The rebuilt table has `2 ^ lg` slots. -/
theorem rebuild_cap_raw (wf : WF ⟨ctrl, keys, vals⟩ size gl mask shift) {lg : Nat} {k0 : α}
    {v0 : β} (h : RebuildPre ⟨ctrl, keys, vals⟩ size lg) {nc : ByteArray} {nk : Array α}
    {nv : Array β}
    (hm : (if hs : smallMask (((2 : Nat) ^ lg - 1).toUSize) = true then
        moveLoop ctrl keys vals mask 0 (ctrl.propagateMark (emptyCtrl ((2 : Nat) ^ lg)))
          (keys.propagateMark (Array.replicate ((2 : Nat) ^ lg + 1) k0))
          (vals.propagateMark (Array.replicate ((2 : Nat) ^ lg + 1) v0))
          (((2 : Nat) ^ lg - 1).toUSize) ((57 - lg).toUInt64) (wf.moveSrcU h hs)
          (moveDstU h.three_le hs) freeBound
      else
        moveLoopN ctrl keys vals (ctrl.size - 8) 0 (ctrl.propagateMark (emptyCtrl ((2 : Nat) ^ lg)))
          (keys.propagateMark (Array.replicate ((2 : Nat) ^ lg + 1) k0))
          (vals.propagateMark (Array.replicate ((2 : Nat) ^ lg + 1) v0)) ((2 : Nat) ^ lg)
          ((57 - lg).toUInt64) wf.moveSrcN (moveDstN h.three_le) freeBoundN) = (nc, nk, nv)) :
    (Slots.mk nc nk nv).cap = (2 : Nat) ^ lg :=
  (rebuild_inv wf h hm).cap_eq

end Move

end OAMap.Core.Swiss
