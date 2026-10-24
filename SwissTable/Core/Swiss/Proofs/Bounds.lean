module

public import SwissTable.Core.Swiss.Defs

/-!
# Swiss core proofs, part 1: bounds, termination, and what the code reads off the invariant

A proof file of the Swiss core (`SwissTable/Core/Swiss/Table.lean`, "Proof structure"): the facts
that the code files (`Loops.lean`, `Build.lean`, `Table.lean`) discharge their array bounds and
termination measures with, and the small facts that every later proof file uses.

* **Machine words** (all later files): `USize` additions that do not wrap (`toNat_add_of_lt`,
  `toNat_add_eight`, `toNat_add_one`), the slot mask `2 ^ lg - 1` (`toNat_mask_of_le`, and
  `smallMask_pow_iff`: its bit 31 is clear iff `lg ≤ 31`, the heart of the guard lemmas; on 32-bit
  platforms the mask of a table of `2 ^ 32` slots or more wraps to `2 ^ 32 - 1`, whose bit 31 is
  set), masked indices (`and_mask_lt`, ...), and the byte read `uget_eq_getElem'`.
* **Termination** (`Loops.lean`): the `Prod.Lex` measures of the loops (`lex_lane`, `lex_group`,
  `lex_fold`, ...), with the probe and traversal steps that do not wrap on machine words.
* **The loops' erased hypotheses** (`Loops.lean`): the bounds that `ArrU`, `LoopU`, `ArrN`,
  `MoveSrcU`, `FoldU`, ... give, and how they carry over from one iteration to the next.
* **Control arrays** (all later files): sizes and bytes after `setCtrlN` and `eraseCtrlN`
  (`getElem_setCtrlN`, `mirrored_setCtrlN`, `slotByte_setCtrlN`), the group word on `Nat` indices
  (`byte_ctrlWordN`, `byte_ctrlWordN_of_mirrored`, `ctrlWordN_congr`), and the machine-word forms
  against the `Nat` ones (`setCtrl_eq_setCtrlN`, `ctrlWord_eq_ctrlWordN`, `homeU_toNat`).
* **Slots** (all later files): the entry of a slot and its cells, in both directions
  (`entryAt_of_full`, `entryAt_of_isFull`, `entryAt_of_not_full`, `entryAt_eq_none`,
  `entryAt_eq_some`, `isFull_of_entryAt`), membership in the entries (`mem_entries`), and
  `filterMap_congr_mem` for the entries as a `filterMap` over the slots.
* **The invariant** (`Build.lean`, `Table.lean`, all later files): the shape facts (`WF.geom`,
  `WF.mirrored`, the cell bounds), the guards (`WF.smallMask_eq`: `smallMask ↔ smallShift`), the
  hypotheses of the loops from the invariant (`WF.loopU`, `WF.arrN`, `WF.foldU`, ...), the
  unallocated table (`WF.unalloc`; `firstGroup`: no tag matches in its only group, which has an
  EMPTY slot), the cells an insert writes (`WF.new_*`), the capacity arithmetic of `lgFor`, and the
  preconditions of a rebuild (`WF.rebuildPre_same`, `WF.rebuildPre_grow`).

The slot arithmetic comes from `Geom` and `Mirrored` of `Group.lean` (`Geom.toNat_and_mask`,
`Geom.toNat_add_and_mask`, `byte_ctrlWord_of_mirrored`, `slotByte_setCtrl`). Statements that unify
with code terms write `(2 : Nat) ^ lg`: with the bare numeral, the elaborator tries to evaluate
`2 ^ lg` before the default instance fixes its type, and times out.

`WF.new_alloc_gl`, `WF.new_alloc_old` and `WF.new_alloc_oldN` take a `NewSlot` (`_h`) that their
proofs do not need, because the inserts of `Table.lean` pass it: removing it there changes only
erased arguments, but it reorders the parameters of a join point in `Table.lean`'s generated C,
and the code is frozen.
-/

@[expose] public section

universe u v w

namespace SwissTable.Core.Swiss

variable {α : Type u} {β : Type v} {γ : Type w}

/-! ## Machine words below `2 ^ 32`, and the `2 ^ 31` guard -/

/-- An addition of `USize`s below `2 ^ 32` does not wrap. -/
theorem toNat_add_of_lt {a b : USize} (h : a.toNat + b.toNat < 2 ^ 32) :
    (a + b).toNat = a.toNat + b.toNat := by
  rw [USize.toNat_add]
  exact Nat.mod_eq_of_lt (Nat.lt_of_lt_of_le h USize.le_size)

private theorem toNat_eight_u : (8 : USize).toNat = 8 := by simp

private theorem toNat_one_u : (1 : USize).toNat = 1 := by simp

/-- The probe and traversal step `+ 8` does not wrap up to `2 ^ 31`. -/
theorem toNat_add_eight {a : USize} (h : a.toNat ≤ 2 ^ 31) :
    (a + 8).toNat = a.toNat + 8 := by
  rw [toNat_add_of_lt (by rw [toNat_eight_u]; omega), toNat_eight_u]

/-- `+ 1` does not wrap below `2 ^ 31`. -/
theorem toNat_add_one {a : USize} (h : a.toNat < 2 ^ 31) : (a + 1).toNat = a.toNat + 1 := by
  rw [toNat_add_of_lt (by rw [toNat_one_u]; omega), toNat_one_u]

theorem ne_zero_of_bne {m : UInt64} (h : (m != 0) = true) : m ≠ 0 := by simpa using h

theorem eq_zero_of_not_bne {m : UInt64} (h : ¬(m != 0) = true) : m = 0 := by simpa using h

private theorem eight_le_of_not_lt {a : USize} (h : ¬a < 8) : 8 ≤ a.toNat := by
  rw [USize.lt_iff_toNat_lt, toNat_eight_u] at h; omega

private theorem toNat_sub_eight {a : USize} (h : ¬a < 8) : (a - 8).toNat = a.toNat - 8 := by
  have := eight_le_of_not_lt h
  rw [USize.toNat_sub_of_le _ _ (by rw [USize.le_iff_toNat_le, toNat_eight_u]; exact this),
    toNat_eight_u]

private theorem toNat_add_lane {p : USize} {m : UInt64} (hm : IsMask m) (hp : p.toNat ≤ 2 ^ 31) :
    (p + lowestLane m).toNat = p.toNat + (lowestLane m).toNat := by
  have := lowestLane_lt hm
  exact toNat_add_of_lt (by omega)

private theorem toNat_toUSize_lt {n : Nat} (h : n < 2 ^ 32) : n.toUSize.toNat = n := by
  rw [Nat.toUSize_eq, USize.toNat_ofNat_of_lt_32 h]

private theorem two_pow_le_31 {lg : Nat} (h : lg ≤ 31) : 2 ^ lg ≤ 2 ^ 31 :=
  Nat.pow_le_pow_right (by decide) h

private theorem two_pow_ge_32 {lg : Nat} (h : ¬lg ≤ 31) : 2 ^ 32 ≤ 2 ^ lg :=
  Nat.pow_le_pow_right (by decide) (by omega)

private theorem and_two_pow_eq_zero_iff (x n : Nat) : x &&& 2 ^ n = 0 ↔ x.testBit n = false := by
  constructor
  · intro h
    have := congrArg (fun y => y.testBit n) h
    simp only [Nat.testBit_and, Nat.testBit_two_pow, Nat.zero_testBit, decide_true,
      Bool.and_true] at this
    exact this
  · intro h
    apply Nat.eq_of_testBit_eq
    intro i
    rw [Nat.testBit_and, Nat.testBit_two_pow, Nat.zero_testBit]
    by_cases hi : n = i
    · subst hi; simp [h]
    · simp [hi]

/-- **The heart of the guards**: the slot mask `2 ^ lg - 1` has bit 31 clear iff `lg ≤ 31` (on
32-bit platforms the mask of a table of `2 ^ 32` slots or more wraps to `2 ^ 32 - 1`, whose bit 31
is set). -/
theorem smallMask_pow_iff (lg : Nat) :
    smallMask ((2 : Nat) ^ lg - 1).toUSize = true ↔ lg ≤ 31 := by
  have hnb : 32 ≤ System.Platform.numBits := by
    rcases System.Platform.numBits_eq with h | h <;> omega
  have h31 : (0x80000000 : USize).toNat = 2 ^ 31 := by simp
  unfold smallMask
  rw [beq_iff_eq, ← USize.toNat_inj, USize.toNat_and, h31, USize.toNat_zero,
    and_two_pow_eq_zero_iff, Nat.toUSize_eq, USize.toNat_ofNat', Nat.testBit_mod_two_pow,
    Nat.testBit_two_pow_sub_one, decide_eq_true (show 31 < System.Platform.numBits by omega),
    Bool.true_and, decide_eq_false_iff_not]
  omega

private theorem smallShift_sub_iff (lg : Nat) : smallShift (57 - lg).toUInt64 = true ↔ lg ≤ 31 := by
  have h : (57 - lg).toUInt64.toNat = 57 - lg := by
    rw [Nat.toUInt64_eq, UInt64.toNat_ofNat']; exact Nat.mod_eq_of_lt (by omega)
  have h26 : (26 : UInt64).toNat = 26 := by simp
  unfold smallShift
  rw [decide_eq_true_iff, ge_iff_le, UInt64.le_iff_toNat_le, h, h26]
  omega

/-- `2 ^ lg - 1` as a slot mask, for `lg ≤ 31`. -/
theorem toNat_mask_of_le {lg : Nat} (h : lg ≤ 31) :
    ((2 : Nat) ^ lg - 1).toUSize.toNat = 2 ^ lg - 1 :=
  toNat_toUSize_lt (by have := two_pow_le_31 h; omega)

private theorem toNat_mask_le (lg : Nat) : ((2 : Nat) ^ lg - 1).toUSize.toNat ≤ 2 ^ lg - 1 := by
  rw [Nat.toUSize_eq, USize.toNat_ofNat']; exact Nat.mod_le _ _

/-- The bytes of the unallocated table's control array are EMPTY. -/
private theorem getElem_emptyGroup {c : ByteArray} (hc : c = emptyGroup) {j : Nat}
    (hj : j < c.size) : c[j] = 0xFF := by
  subst hc
  have h : ∀ j (h : j < 8),
      emptyGroup[j]'(by rw [show emptyGroup.size = 8 from rfl]; exact h) = 0xFF := by
    decide
  exact h j hj

/-- A machine-word byte read is the `Nat` one. -/
theorem uget_eq_getElem' (c : ByteArray) (i : USize) (h : i.toNat < c.size) :
    c.uget i h = c[i.toNat] := by
  cases c; rfl

private theorem getElem_set' (c : ByteArray) (i : Nat) (b : UInt8) (h : i < c.size) (k : Nat)
    (hk : k < (c.set i b h).size) :
    (c.set i b h)[k] = if i = k then b else c[k]'(by rw [size_set] at hk; exact hk) := by
  cases c
  simp [ByteArray.set, ByteArray.getElem_eq_getElem_data, Array.getElem_set]

/-- The second index `setCtrlN` writes: `i + cap` for the first 8 slots, `i` itself after. -/
private theorem mirrorIdxN_eq {i cap : Nat} (hic : i < cap) (h8 : 8 ≤ cap) :
    (i + cap - 8) % cap + 8 = if i < 8 then i + cap else i := by
  split
  · rw [Nat.mod_eq_of_lt (by omega)]; omega
  · rw [show i + cap - 8 = (i - 8) + cap by omega, Nat.add_mod_right, Nat.mod_eq_of_lt (by omega)]
    omega

/-! ## Machine-word arithmetic -/

theorem and_mask_le (x mask : USize) : (x &&& mask).toNat ≤ mask.toNat := by
  rw [USize.toNat_and]; exact Nat.and_le_right

theorem and_mask_lt {x mask : USize} {n : Nat} (h : mask.toNat < n) : (x &&& mask).toNat < n :=
  Nat.lt_of_le_of_lt (and_mask_le x mask) h

theorem and_mask_word {x mask : USize} {n : Nat} (h : mask.toNat + 8 ≤ n) :
    (x &&& mask).toNat + 8 ≤ n := by
  have := and_mask_le x mask; omega

theorem word_of_le {p mask : USize} {n : Nat} (h : mask.toNat + 8 ≤ n)
    (hp : p.toNat ≤ mask.toNat) : p.toNat + 8 ≤ n := by
  omega

theorem le_of_not_gt' {s mask : USize} (h : ¬s > mask) : s.toNat ≤ mask.toNat := by
  rw [GT.gt, USize.lt_iff_toNat_lt] at h; omega

theorem stride_zero {mask : USize} : (0 : USize).toNat ≤ mask.toNat := by
  simp

theorem keys_of_ne {P Q : Prop} {m : UInt64} (hk : P ∨ (m = 0 ∧ Q)) (h : (m != 0) = true) :
    P := by
  rcases hk with hk | ⟨rfl, -⟩
  · exact hk
  · simp at h

theorem keys_of_empty {P : Prop} {m e : UInt64} (hk : P ∨ (m = 0 ∧ e ≠ 0))
    (he : ¬(e != 0) = true) : P := by
  rcases hk with hk | ⟨-, hne⟩
  · exact hk
  · simp [hne] at he

/-- A cell index stays in bounds after a `uset`. -/
theorem lt_size_uset {xs : Array γ} {i : USize} {v : γ} {h : i.toNat < xs.size} {j : Nat}
    (hj : j < xs.size) : j < (xs.uset i v h).size := by
  rwa [Array.size_uset]

/-- A cell index stays in bounds after a `set`. -/
theorem lt_size_set {xs : Array γ} {i : Nat} {v : γ} {h : i < xs.size} {j : Nat}
    (hj : j < xs.size) : j < (xs.set i v h).size := by
  rwa [Array.size_set]

theorem lt_ctrl_of_cap {i cap n : Nat} (h : i < cap) (hc : cap = n - 8) : i < n := by
  omega

theorem clearLowest_lt_of {m : UInt64} (hm : IsMask m) (h : (m != 0) = true) :
    (clearLowest m).toNat < m.toNat :=
  clearLowest_lt hm (by simpa using h)

/-! ## Termination measures -/

theorem lex_lane {a : Nat} {m : UInt64} (hm : IsMask m) (h : (m != 0) = true) :
    Prod.Lex (fun a₁ a₂ => a₁ < a₂) (fun a₁ a₂ => a₁ < a₂) (a, (clearLowest m).toNat)
      (a, m.toNat) :=
  Prod.Lex.right _ (clearLowest_lt_of hm h)

/-- One probe step on machine words: on at most `2 ^ 31` slots `stride + 8` does not wrap. -/
theorem sub_group {mask stride : USize} (hsm : mask.toNat < 2 ^ 31)
    (hs : stride.toNat ≤ mask.toNat) :
    mask.toNat + 8 - (stride + 8).toNat < mask.toNat + 8 - stride.toNat := by
  have h8 := toNat_add_eight (a := stride) (by omega)
  omega

theorem lex_group {mask stride : USize} {b b' : Nat} (hsm : mask.toNat < 2 ^ 31)
    (hs : stride.toNat ≤ mask.toNat) :
    Prod.Lex (fun a₁ a₂ => a₁ < a₂) (fun a₁ a₂ => a₁ < a₂)
      (mask.toNat + 8 - (stride + 8).toNat, b') (mask.toNat + 8 - stride.toNat, b) :=
  Prod.Lex.left _ _ (sub_group hsm hs)

theorem sub_groupN {cap stride : Nat} (h : ¬cap ≤ stride + 8) :
    cap + 8 - (stride + 8) < cap + 8 - stride := by
  omega

theorem lex_groupN {cap stride : Nat} {b b' : Nat} (h : ¬cap ≤ stride + 8) :
    Prod.Lex (fun a₁ a₂ => a₁ < a₂) (fun a₁ a₂ => a₁ < a₂) (cap + 8 - (stride + 8), b')
      (cap + 8 - stride, b) :=
  Prod.Lex.left _ _ (sub_groupN h)

theorem move_dec {omask i : USize} (hsm : omask.toNat < 2 ^ 31) (hi : ¬i > omask) :
    omask.toNat + 1 - (i + 1).toNat < omask.toNat + 1 - i.toNat := by
  have hi' := le_of_not_gt' hi
  rw [toNat_add_of_lt (by rw [toNat_one_u]; omega), toNat_one_u]
  omega

theorem lex_fold {cap p : USize} {b b' : Nat} (hsm : cap.toNat ≤ 2 ^ 31) (hp : GroupAt cap p) :
    Prod.Lex (fun a₁ a₂ => a₁ < a₂) (fun a₁ a₂ => a₁ < a₂)
      (cap.toNat + 8 - (p + 8).toNat, b') (cap.toNat + 8 - p.toNat, b) := by
  have h1 := hp.1
  apply Prod.Lex.left
  rw [toNat_add_eight (by omega)]
  omega

theorem lex_foldN {cap p : Nat} {b b' : Nat} (h : p + 8 < cap) :
    Prod.Lex (fun a₁ a₂ => a₁ < a₂) (fun a₁ a₂ => a₁ < a₂) (cap + 8 - (p + 8), b')
      (cap + 8 - p, b) :=
  Prod.Lex.left _ _ (by omega)

theorem rev_dec {p : USize} (h : ¬p < 8) : (p - 8).toNat < p.toNat := by
  have := eight_le_of_not_lt h
  rw [toNat_sub_eight h]
  omega

/-! ## The loops' erased hypotheses -/

theorem CtrlN.mod_word {ctrl : ByteArray} {cap : Nat} (h : CtrlN ctrl cap) (x : Nat) :
    x % cap + 8 ≤ ctrl.size := by
  have := Nat.mod_lt x h.pos; have := h.word; omega

theorem CtrlN.word_of_lt {ctrl : ByteArray} {cap : Nat} (h : CtrlN ctrl cap) {p : Nat}
    (hp : p < cap) : p + 8 ≤ ctrl.size := by
  have := h.word; omega

theorem ArrN.mod_keys {ctrl : ByteArray} {keys : Array α} {cap : Nat} (h : ArrN ctrl keys cap)
    (x : Nat) : x % cap < keys.size := by
  have := Nat.mod_lt x h.pos; have := h.keys; omega

theorem MoveSrcU.ctrl_lt {oc : ByteArray} {ok : Array α} {ov : Array β} {omask : USize}
    (h : MoveSrcU oc ok ov omask) {i : USize} (hi : ¬i > omask) : i.toNat < oc.size := by
  have := le_of_not_gt' hi; have := h.ctrl; omega

theorem MoveSrcU.keys_lt {oc : ByteArray} {ok : Array α} {ov : Array β} {omask : USize}
    (h : MoveSrcU oc ok ov omask) {i : USize} (hi : ¬i > omask) : i.toNat < ok.size := by
  have := le_of_not_gt' hi; have := h.keys; omega

theorem MoveSrcU.vals_lt {oc : ByteArray} {ok : Array α} {ov : Array β} {omask : USize}
    (h : MoveSrcU oc ok ov omask) {i : USize} (hi : ¬i > omask) : i.toNat < ov.size := by
  have := le_of_not_gt' hi; have := h.vals; omega

theorem MoveDstU.ctrl_lt {nc : ByteArray} {nk : Array α} {nv : Array β} {nmask : USize}
    (h : MoveDstU nc nk nv nmask) {j : USize} (hj : j.toNat ≤ nmask.toNat + 1) :
    j.toNat < nc.size := by
  have := h.ctrl_size; omega

theorem MoveDstU.mirror {nc : ByteArray} {nk : Array α} {nv : Array β} {nmask : USize}
    (h : MoveDstU nc nk nv nmask) : nmask.toNat + 8 < nc.size := by
  have := h.ctrl_size; omega

theorem MoveDstU.keys_lt {nc : ByteArray} {nk : Array α} {nv : Array β} {nmask : USize}
    (h : MoveDstU nc nk nv nmask) {j : USize} (hj : j.toNat ≤ nmask.toNat + 1) :
    j.toNat < nk.size := by
  have := h.keys_size; omega

theorem MoveDstU.vals_lt {nc : ByteArray} {nk : Array α} {nv : Array β} {nmask : USize}
    (h : MoveDstU nc nk nv nmask) {j : USize} (hj : j.toNat ≤ nmask.toNat + 1) :
    j.toNat < nv.size := by
  have := h.vals_size; omega

theorem MoveDstU.write {nc nc' : ByteArray} {nk nk' : Array α} {nv nv' : Array β}
    {nmask : USize} (h : MoveDstU nc nk nv nmask) (hc : nc'.size = nc.size)
    (hk : nk'.size = nk.size) (hv : nv'.size = nv.size) : MoveDstU nc' nk' nv' nmask := by
  obtain ⟨⟨hw, hs⟩, h1, h2, h3⟩ := h
  exact ⟨⟨by omega, hs⟩, by omega, by omega, by omega⟩

theorem MoveSrcN.ctrl_lt {oc : ByteArray} {ok : Array α} {ov : Array β} {ocap : Nat}
    (h : MoveSrcN oc ok ov ocap) {i : Nat} (hi : i < ocap) : i < oc.size := by
  have := h.ctrl; omega

theorem MoveSrcN.keys_lt {oc : ByteArray} {ok : Array α} {ov : Array β} {ocap : Nat}
    (h : MoveSrcN oc ok ov ocap) {i : Nat} (hi : i < ocap) : i < ok.size := by
  have := h.keys; omega

theorem MoveSrcN.vals_lt {oc : ByteArray} {ok : Array α} {ov : Array β} {ocap : Nat}
    (h : MoveSrcN oc ok ov ocap) {i : Nat} (hi : i < ocap) : i < ov.size := by
  have := h.vals; omega

theorem MoveDstN.ctrlN {nc : ByteArray} {nk : Array α} {nv : Array β} {ncap : Nat}
    (h : MoveDstN nc nk nv ncap) : CtrlN nc ncap :=
  ⟨h.pos, by have := h.ctrl_size; omega⟩

theorem MoveDstN.word {nc : ByteArray} {nk : Array α} {nv : Array β} {ncap : Nat}
    (h : MoveDstN nc nk nv ncap) : ncap + 8 ≤ nc.size := by
  have := h.ctrl_size; omega

theorem MoveDstN.ctrl_lt {nc : ByteArray} {nk : Array α} {nv : Array β} {ncap : Nat}
    (h : MoveDstN nc nk nv ncap) {j : Nat} (hj : j ≤ ncap) : j < nc.size := by
  have := h.ctrl_size; omega

theorem MoveDstN.keys_lt {nc : ByteArray} {nk : Array α} {nv : Array β} {ncap : Nat}
    (h : MoveDstN nc nk nv ncap) {j : Nat} (hj : j ≤ ncap) : j < nk.size := by
  have := h.keys_size; omega

theorem MoveDstN.vals_lt {nc : ByteArray} {nk : Array α} {nv : Array β} {ncap : Nat}
    (h : MoveDstN nc nk nv ncap) {j : Nat} (hj : j ≤ ncap) : j < nv.size := by
  have := h.vals_size; omega

theorem MoveDstN.write {nc nc' : ByteArray} {nk nk' : Array α} {nv nv' : Array β} {ncap : Nat}
    (h : MoveDstN nc nk nv ncap) (hc : nc'.size = nc.size) (hk : nk'.size = nk.size)
    (hv : nv'.size = nv.size) : MoveDstN nc' nk' nv' ncap := by
  obtain ⟨h0, h1, h2, h3⟩ := h
  exact ⟨h0, by omega, by omega, by omega⟩

theorem FoldU.lane_keys {ctrl : ByteArray} {keys : Array α} {vals : Array β} {cap : USize}
    (h : FoldU ctrl keys vals cap) {p : USize} {fm : UInt64} (hp : GroupAt cap p)
    (hm : IsMask fm) : (p + lowestLane fm).toNat < keys.size := by
  have hl := lowestLane_lt hm
  have h1 := hp.1
  have := h.small
  have := h.keys
  rw [toNat_add_lane hm (by omega)]
  omega

theorem FoldU.lane_vals {ctrl : ByteArray} {keys : Array α} {vals : Array β} {cap : USize}
    (h : FoldU ctrl keys vals cap) {p : USize} {fm : UInt64} (hp : GroupAt cap p)
    (hm : IsMask fm) : (p + lowestLane fm).toNat < vals.size := by
  have hl := lowestLane_lt hm
  have h1 := hp.1
  have := h.small
  have := h.vals
  rw [toNat_add_lane hm (by omega)]
  omega

theorem FoldU.next_word {ctrl : ByteArray} {keys : Array α} {vals : Array β} {cap : USize}
    (h : FoldU ctrl keys vals cap) {p : USize} (hlt : p + 8 < cap) :
    (p + 8).toNat + 8 ≤ ctrl.size := by
  have := USize.lt_iff_toNat_lt.mp hlt
  have := h.word
  omega

theorem FoldU.next_group {ctrl : ByteArray} {keys : Array α} {vals : Array β} {cap : USize}
    (h : FoldU ctrl keys vals cap) {p : USize} (hp : GroupAt cap p) (hlt : p + 8 < cap) :
    GroupAt cap (p + 8) := by
  have h1 := hp.1
  have h2 := hp.2
  have := h.small
  have := h.eight
  have hlt' := USize.lt_iff_toNat_lt.mp hlt
  have h8 := toNat_add_eight (a := p) (by omega)
  exact ⟨by omega, by omega⟩

theorem FoldN.lane_keys {ctrl : ByteArray} {keys : Array α} {vals : Array β} {cap : Nat}
    (h : FoldN ctrl keys vals cap) {p : Nat} {fm : UInt64} (hp : GroupAtN cap p)
    (hm : IsMask fm) : p + (lowestLane64 fm).toNat < keys.size := by
  have := lowestLane64_lt hm; have := h.keys; have := hp.1; omega

theorem FoldN.lane_vals {ctrl : ByteArray} {keys : Array α} {vals : Array β} {cap : Nat}
    (h : FoldN ctrl keys vals cap) {p : Nat} {fm : UInt64} (hp : GroupAtN cap p)
    (hm : IsMask fm) : p + (lowestLane64 fm).toNat < vals.size := by
  have := lowestLane64_lt hm; have := h.vals; have := hp.1; omega

theorem FoldN.next_word {ctrl : ByteArray} {keys : Array α} {vals : Array β} {cap : Nat}
    (h : FoldN ctrl keys vals cap) {p : Nat} (hlt : p < cap) : p + 8 ≤ ctrl.size := by
  have := h.word; omega

theorem FoldN.next_group {ctrl : ByteArray} {keys : Array α} {vals : Array β} {cap : Nat}
    (h : FoldN ctrl keys vals cap) {p : Nat} (hp : GroupAtN cap p) (hlt : p + 8 < cap) :
    GroupAtN cap (p + 8) := by
  have := h.eight; have := hp.2; exact ⟨by omega, by omega⟩

theorem FoldN.ctrl_lt {ctrl : ByteArray} {keys : Array α} {vals : Array β} {cap : Nat}
    (h : FoldN ctrl keys vals cap) {i : Nat} (hi : i < cap) : i < ctrl.size := by
  have := h.word; omega

theorem FoldN.keys_lt {ctrl : ByteArray} {keys : Array α} {vals : Array β} {cap : Nat}
    (h : FoldN ctrl keys vals cap) {i : Nat} (hi : i < cap) : i < keys.size := by
  have := h.keys; omega

theorem FoldN.vals_lt {ctrl : ByteArray} {keys : Array α} {vals : Array β} {cap : Nat}
    (h : FoldN ctrl keys vals cap) {i : Nat} (hi : i < cap) : i < vals.size := by
  have := h.vals; omega

theorem RevGroupU.lane_keys {keys : Array α} {vals : Array β} {p : USize}
    (h : RevGroupU keys vals p) {fm : UInt64} (hm : IsMask fm) :
    (p + lowestLane fm).toNat < keys.size := by
  have hl := lowestLane_lt hm
  have := h.small
  have := h.keys
  rw [toNat_add_lane hm (by omega)]
  omega

theorem RevGroupU.lane_vals {keys : Array α} {vals : Array β} {p : USize}
    (h : RevGroupU keys vals p) {fm : UInt64} (hm : IsMask fm) :
    (p + lowestLane fm).toNat < vals.size := by
  have hl := lowestLane_lt hm
  have := h.small
  have := h.vals
  rw [toNat_add_lane hm (by omega)]
  omega

theorem RevAtU.word_sub {ctrl : ByteArray} {keys : Array α} {vals : Array β} {p : USize}
    (h : RevAtU ctrl keys vals p) (hp : ¬p < 8) : (p - 8).toNat + 8 ≤ ctrl.size := by
  have := eight_le_of_not_lt hp
  have := h.word
  rw [toNat_sub_eight hp]
  omega

theorem RevAtU.group {ctrl : ByteArray} {keys : Array α} {vals : Array β} {p : USize}
    (h : RevAtU ctrl keys vals p) (hp : ¬p < 8) : RevGroupU keys vals (p - 8) := by
  have := eight_le_of_not_lt hp
  have := h.keys
  have := h.vals
  have := h.small
  exact ⟨by rw [toNat_sub_eight hp]; omega, by rw [toNat_sub_eight hp]; omega,
    by rw [toNat_sub_eight hp]; omega⟩

theorem RevAtU.next {ctrl : ByteArray} {keys : Array α} {vals : Array β} {p : USize}
    (h : RevAtU ctrl keys vals p) (hp : ¬p < 8) : RevAtU ctrl keys vals (p - 8) := by
  have := eight_le_of_not_lt hp
  have := h.word
  have := h.keys
  have := h.vals
  have := h.small
  exact ⟨by rw [toNat_sub_eight hp]; omega, by rw [toNat_sub_eight hp]; omega,
    by rw [toNat_sub_eight hp]; omega, by rw [toNat_sub_eight hp]; omega⟩

theorem RevGroupN.lane_keys {keys : Array α} {vals : Array β} {p : Nat}
    (h : RevGroupN keys vals p) {fm : UInt64} (hm : IsMask fm) :
    p + (lowestLane64 fm).toNat < keys.size := by
  have := lowestLane64_lt hm; have := h.keys; omega

theorem RevGroupN.lane_vals {keys : Array α} {vals : Array β} {p : Nat}
    (h : RevGroupN keys vals p) {fm : UInt64} (hm : IsMask fm) :
    p + (lowestLane64 fm).toNat < vals.size := by
  have := lowestLane64_lt hm; have := h.vals; omega

theorem RevAtN.word_sub {ctrl : ByteArray} {keys : Array α} {vals : Array β} {p : Nat}
    (h : RevAtN ctrl keys vals p) (hp : ¬p < 8) : p - 8 + 8 ≤ ctrl.size := by
  have := h.word; omega

theorem RevAtN.group {ctrl : ByteArray} {keys : Array α} {vals : Array β} {p : Nat}
    (h : RevAtN ctrl keys vals p) (hp : ¬p < 8) : RevGroupN keys vals (p - 8) :=
  ⟨by have := h.keys; omega, by have := h.vals; omega⟩

theorem RevAtN.next {ctrl : ByteArray} {keys : Array α} {vals : Array β} {p : Nat}
    (h : RevAtN ctrl keys vals p) (hp : ¬p < 8) : RevAtN ctrl keys vals (p - 8) :=
  ⟨by have := h.word; omega, by have := h.keys; omega, by have := h.vals; omega⟩

theorem FMArr.ctrl_lt {ctrl : ByteArray} {keys : Array α} {vals : Array β} {cap : Nat}
    (h : FMArr ctrl keys vals cap) {i : Nat} (hi : i < cap) : i < ctrl.size := by
  have := h.word; omega

theorem FMArr.keys_lt {ctrl : ByteArray} {keys : Array α} {vals : Array β} {cap : Nat}
    (h : FMArr ctrl keys vals cap) {i : Nat} (hi : i < cap) : i < keys.size := by
  have := h.keys; omega

theorem FMArr.vals_lt {ctrl : ByteArray} {keys : Array α} {vals : Array β} {cap : Nat}
    (h : FMArr ctrl keys vals cap) {i : Nat} (hi : i < cap) : i < vals.size := by
  have := h.vals; omega

/-! ## Control arrays -/

theorem size_setCtrlN (c : ByteArray) (cap i : Nat) (b : UInt8) (hi : i < c.size)
    (hm : cap + 8 ≤ c.size) (hc : 0 < cap) : (setCtrlN c cap i b hi hm hc).size = c.size := by
  simp only [setCtrlN, size_set]

theorem size_eraseCtrlN (ctrl : ByteArray) (size gl cap i : Nat) (hi : i < cap)
    (hc : cap + 8 ≤ ctrl.size) : (eraseCtrlN ctrl size gl cap i hi hc).1.size = ctrl.size := by
  simp only [eraseCtrlN, size_setCtrlN]

theorem FMArr.erase {ctrl : ByteArray} {keys : Array α} {vals : Array β} {cap : Nat}
    (h : FMArr ctrl keys vals cap) {size gl i : Nat} {hi : i < cap} {c' : ByteArray} {g' : Nat}
    (he : eraseCtrlN ctrl size gl cap i hi h.word = (c', g')) {k' : Array α}
    (hk : k'.size = keys.size) : FMArr c' k' vals cap := by
  have hs := size_eraseCtrlN ctrl size gl cap i hi h.word
  rw [he] at hs
  exact ⟨by have := h.word; simp only at hs; omega, by have := h.keys; omega, h.vals⟩

/-- Byte `k` after `setCtrlN`: the two written indices, else the old byte. -/
theorem getElem_setCtrlN (c : ByteArray) (cap i : Nat) (b : UInt8) (hi : i < c.size)
    (hm : cap + 8 ≤ c.size) (hc : 0 < cap) (k : Nat) (hk : k < c.size) :
    (setCtrlN c cap i b hi hm hc)[k]'(by rw [size_setCtrlN]; exact hk) =
      if (i + cap - 8) % cap + 8 = k then b else if i = k then b else c[k] := by
  have := getElem_set' (c.set i b hi) ((i + cap - 8) % cap + 8) b
    (by rw [size_set]; have := Nat.mod_lt (i + cap - 8) hc; omega) k
    (by rw [size_set, size_set]; exact hk)
  rw [getElem_set' c i b hi] at this
  exact this

/-- `setCtrlN` keeps the mirror. -/
theorem mirrored_setCtrlN {c : ByteArray} {cap : Nat} (h : Mirrored c cap) {i : Nat}
    (hic : i < cap) (b : UInt8) {hi : i < c.size} {hm : cap + 8 ≤ c.size} {hc : 0 < cap} :
    Mirrored (setCtrlN c cap i b hi hm hc) cap := by
  have hs := h.size_eq
  have h8 := h.le_cap
  refine ⟨by rw [size_setCtrlN]; exact hs, h.pow_two, h8, fun j hj => ?_⟩
  rw [getElem_setCtrlN _ _ _ _ _ _ _ _ (by omega), getElem_setCtrlN _ _ _ _ _ _ _ _ (by omega),
    mirrorIdxN_eq hic h8, h.mirror j hj]
  repeat' split
  all_goals first | rfl | omega

/-- `setCtrlN` writes exactly slot `i`, as seen through `slotByte`. -/
theorem slotByte_setCtrlN {c : ByteArray} {cap : Nat} (h : Mirrored c cap) {i : Nat}
    (hic : i < cap) (b : UInt8) {hi : i < c.size} {hm : cap + 8 ≤ c.size} {hc : 0 < cap}
    (k : Nat) :
    slotByte (setCtrlN c cap i b hi hm hc) cap k = if k % cap = i then b else slotByte c cap k := by
  have hs := h.size_eq
  have h8 := h.le_cap
  have hkc : k % cap < cap := Nat.mod_lt _ (by omega)
  rw [← slotByte_mod, (mirrored_setCtrlN h hic b (hi := hi) (hm := hm) (hc := hc)).slotByte_eq hkc,
    getElem_setCtrlN _ _ _ _ _ _ _ _ (by omega), ← slotByte_mod c, h.slotByte_eq hkc,
    mirrorIdxN_eq hic h8]
  repeat' split
  all_goals first | rfl | omega

/-- The group word at equal indices. -/
theorem ctrlWordN_congr {c : ByteArray} {i j : Nat} (e : i = j) {h : i + 8 ≤ c.size}
    {h' : j + 8 ≤ c.size} : ctrlWordN c i h = ctrlWordN c j h' := by
  subst e; rfl

/-- Byte `j` of the group word on `Nat` indices. -/
theorem byte_ctrlWordN (c : ByteArray) (i : Nat) (h : i + 8 ≤ c.size) {j : Nat} (hj : j < 8) :
    byte (ctrlWordN c i h) j = c[i + j]'(by omega) := by
  unfold ctrlWordN
  rw [byte_or8 _ _ _ _ _ _ _ _ hj]
  rcases j with _ | _ | _ | _ | _ | _ | _ | _ | j <;> simp
  all_goals omega

/-- Under the mirror, byte `j` of the group word at slot `p` is the byte of slot
`(p + j) % cap`. -/
theorem byte_ctrlWordN_of_mirrored {c : ByteArray} {cap : Nat} (h : Mirrored c cap) {p : Nat}
    {hw : p + 8 ≤ c.size} {j : Nat} (hj : j < 8) :
    byte (ctrlWordN c p hw) j = slotByte c cap ((p + j) % cap) := by
  rw [byte_ctrlWordN c p hw hj, h.getElem_eq, slotByte_mod]

/-- The machine-word group read is the `Nat` one (when the index does not wrap). -/
theorem ctrlWord_eq_ctrlWordN {c : ByteArray} {i : USize} (hs : i.toNat < 2 ^ 31)
    {h : i.toNat + 8 ≤ c.size} {h' : i.toNat + 8 ≤ c.size} :
    ctrlWord c i h = ctrlWordN c i.toNat h' := by
  apply byte_ext
  intro j hj
  rw [byte_ctrlWord' c i h (by have := USize.le_size; omega) hj, byte_ctrlWordN c i.toNat h' hj]

/-- The machine-word control write is the `Nat` one. -/
theorem setCtrl_eq_setCtrlN {c : ByteArray} {cap : Nat} {mask i : USize} (hg : Geom cap mask)
    (hic : i.toNat < cap) {b : UInt8} {h1 : i.toNat < c.size}
    {h2 : mask.toNat + 8 < c.size} {h3 : i.toNat < c.size} {h4 : cap + 8 ≤ c.size}
    {h5 : 0 < cap} : setCtrl c mask i b h1 h2 = setCtrlN c cap i.toNat b h3 h4 h5 := by
  obtain ⟨n, hcap⟩ := hg.pow_two
  apply ByteArray.ext_getElem (by rw [size_setCtrl, size_setCtrlN])
  intro k hk hk'
  have hk0 : k < c.size := by rw [size_setCtrl] at hk; exact hk
  rw [getElem_setCtrl _ _ _ _ _ _ k hk0, getElem_setCtrlN _ _ _ _ _ _ _ k hk0,
    toNat_mirrorIdx hcap hg.le_cap hg.mask_add_one hg.lt_size hic, mirrorIdxN_eq hic hg.le_cap]

/-- The machine-word home slot is the `Nat` one. -/
theorem homeU_toNat {q : UInt64} {cap : Nat} {mask : USize} (hg : Geom cap mask) :
    (homeU q mask).toNat = homeN q cap := by
  obtain ⟨n, hcap⟩ := hg.pow_two
  unfold homeU homeN
  rw [hg.toNat_and_mask, UInt64.toNat_toUSize, ← USize.size_eq_two_pow,
    Nat.mod_mod_of_dvd _ (dvd_usize_size hcap hg.cap_le_size)]

/-- `getElem!` of a `ByteArray` in range is `getElem`. -/
theorem getElem!_eq_getElem {c : ByteArray} {i : Nat} (h : i < c.size) : c[i]! = c[i] := by
  exact getElem!_pos c i h

/-! ## Slots -/

theorem Slots.IsFull.cap_pos {s : Slots α β} {i : Nat} (hi : s.IsFull i) : 0 < s.cap := by
  have := hi.1; omega

theorem isFull_of {s : Slots α β} {i : Nat} (hi : i < s.cap) {h : i < s.ctrl.size}
    (hf : s.ctrl[i]'h < 0x80) : s.IsFull i :=
  ⟨hi, by rwa [getElem!_eq_getElem h]⟩

/-- A tag is a FULL byte. -/
theorem tagOf_lt (q : UInt64) : tagOf q < 0x80 := by
  unfold tagOf; exact toUInt8_and_7F_lt q

theorem EMPTY_not_lt : ¬EMPTY < 0x80 := by rw [EMPTY_eq]; decide

theorem DELETED_not_lt : ¬DELETED < 0x80 := by rw [DELETED_eq]; decide

/-! ## Slots: the entry of a slot -/

/-- The entry of a full slot with both cells. -/
theorem entryAt_of_full {s : Slots α β} {i : Nat} (hc : i < s.ctrl.size) (hf : s.ctrl[i] < 0x80)
    (hk : i < s.keys.size) (hv : i < s.vals.size) :
    s.entryAt i = some ⟨s.keys[i], s.vals[i]⟩ := by
  unfold Slots.entryAt
  rw [getElem?_pos s.ctrl i hc]
  simp [hf, hk, hv]

/-- The entry of a full slot with both cells, from `IsFull`. -/
theorem entryAt_of_isFull {s : Slots α β} {i : Nat} (hi : s.IsFull i) (hk : i < s.keys.size)
    (hv : i < s.vals.size) : s.entryAt i = some ⟨s.keys[i], s.vals[i]⟩ := by
  have hc : i < s.ctrl.size := by have := hi.1; unfold Slots.cap at this; omega
  have hf := hi.2
  rw [getElem!_pos s.ctrl i hc] at hf
  exact entryAt_of_full hc hf hk hv

/-- A slot whose control byte is not FULL has no entry. -/
theorem entryAt_of_not_full {s : Slots α β} {i : Nat} (hc : i < s.ctrl.size)
    (hf : ¬s.ctrl[i] < 0x80) : s.entryAt i = none := by
  unfold Slots.entryAt
  rw [getElem?_pos s.ctrl i hc]
  simp [hf]

/-- A slot whose control byte is not FULL has no entry (`getElem!` form: no bound needed). -/
theorem entryAt_eq_none {s : Slots α β} {i : Nat} (h : ¬s.ctrl[i]! < 0x80) :
    s.entryAt i = none := by
  unfold Slots.entryAt
  by_cases hi : i < s.ctrl.size
  · rw [getElem?_pos s.ctrl i hi]
    rw [getElem!_pos s.ctrl i hi] at h
    simp only [h, ite_false]
  · rw [getElem?_neg s.ctrl i hi]

/-- What an entry of a slot says about the slot's cells. -/
theorem entryAt_eq_some {s : Slots α β} {i : Nat} {e : (_ : α) × β}
    (h : s.entryAt i = some e) :
    i < s.ctrl.size ∧ s.ctrl[i]! < 0x80 ∧ s.keys[i]? = some e.1 ∧ s.vals[i]? = some e.2 := by
  unfold Slots.entryAt at h
  split at h
  · rename_i c hc
    rw [getElem?_eq_some_iff] at hc
    obtain ⟨hi, rfl⟩ := hc
    split at h
    · rename_i hlt
      cases hk : s.keys[i]? with
      | none => simp [hk] at h
      | some k =>
        cases hv : s.vals[i]? with
        | none => simp [hk, hv] at h
        | some v =>
          simp only [hk, hv, Option.bind_some, Option.map_some, Option.some.injEq] at h
          subst h
          exact ⟨hi, by rw [getElem!_pos s.ctrl i hi]; exact hlt, rfl, rfl⟩
    · exact absurd h (by simp)
  · exact absurd h (by simp)

/-- A slot below `cap` with an entry is full. -/
theorem isFull_of_entryAt {s : Slots α β} {i : Nat} {e : (_ : α) × β} (h : s.entryAt i = some e)
    (hi : i < s.cap) : s.IsFull i :=
  ⟨hi, (entryAt_eq_some h).2.1⟩

/-- The entries are the entries of the slots below `cap`. -/
theorem mem_entries {s : Slots α β} {e : (_ : α) × β} :
    e ∈ s.entries ↔ ∃ i, i < s.cap ∧ s.entryAt i = some e := by
  simp [Slots.entries, List.mem_filterMap, List.mem_range]

/-- `List.filterMap` with functions that agree on the list. -/
theorem filterMap_congr_mem {δ : Type _} {ε : Type _} {f g : δ → Option ε} {l : List δ}
    (h : ∀ x ∈ l, f x = g x) : l.filterMap f = l.filterMap g := by
  induction l with
  | nil => rfl
  | cons a l ih =>
    simp only [List.filterMap_cons, h a List.mem_cons_self,
      ih (fun x hx => h x (List.mem_cons_of_mem _ hx))]

/-! ## Private helpers: the two shapes -/

section Shape

variable {s : Slots α β} {mask : USize} {shift : UInt64} {lg : Nat}

private theorem Unalloc.cap_eq (h : Unalloc s mask shift) : s.cap = 0 := by
  unfold Slots.cap; rw [h.ctrl_eq]; rfl

private theorem Unalloc.ctrl_size (h : Unalloc s mask shift) : s.ctrl.size = 8 := by
  rw [h.ctrl_eq]; rfl

private theorem Alloc.cap_eq (h : Alloc s mask shift lg) : s.cap = 2 ^ lg := by
  unfold Slots.cap; rw [h.mirrored.size_eq]; exact Nat.add_sub_cancel _ _

private theorem Alloc.ctrl_size (h : Alloc s mask shift lg) : s.ctrl.size = 2 ^ lg + 8 :=
  h.mirrored.size_eq

private theorem Alloc.eight_le (h : Alloc s mask shift lg) : 8 ≤ 2 ^ lg :=
  h.mirrored.le_cap

private theorem Alloc.mask_le (h : Alloc s mask shift lg) : mask.toNat ≤ 2 ^ lg - 1 := by
  rw [h.mask_eq]; exact toNat_mask_le lg

private theorem Alloc.mask_toNat (h : Alloc s mask shift lg) (hlg : lg ≤ 31) :
    mask.toNat = 2 ^ lg - 1 := by
  rw [h.mask_eq]; exact toNat_mask_of_le hlg

private theorem Alloc.smallMask_iff (h : Alloc s mask shift lg) :
    smallMask mask = true ↔ lg ≤ 31 := by
  rw [h.mask_eq]; exact smallMask_pow_iff lg

private theorem Alloc.smallShift_iff (h : Alloc s mask shift lg) :
    smallShift shift = true ↔ lg ≤ 31 := by
  rw [h.shift_eq]; exact smallShift_sub_iff lg

private theorem smallMask_zero : smallMask 0 = true := by
  unfold smallMask; simp

private theorem smallShift_57 : smallShift 57 = true := by
  unfold smallShift; decide

end Shape

/-! ## The invariant: shape -/

section WF

variable [BEq α] [Hashable α] {s : Slots α β} {size gl : Nat} {mask : USize} {shift : UInt64}

/-- The unallocated table is well formed. -/
theorem WF.unalloc : WF (⟨emptyGroup, #[], #[]⟩ : Slots α β) 0 0 0 57 := by
  have hcap : (⟨emptyGroup, #[], #[]⟩ : Slots α β).cap = 0 := rfl
  refine ⟨Or.inl ⟨rfl, rfl, rfl, rfl, rfl⟩, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · intro i hi; rw [hcap] at hi; omega
  · intro i k hi; have := hi.1; rw [hcap] at this; omega
  · simp [Slots.entries, hcap]
  · simp [Slots.numDeleted, hcap, capacityOf]
  · intro _ _ i j k k' hi; have := hi.1; rw [hcap] at this; omega
  · intro _ _ i k hi; have := hi.1; rw [hcap] at this; omega

/-- An allocated table (`0 < cap`) has `(2 : Nat) ^ lg` slots. -/
theorem WF.alloc (wf : WF s size gl mask shift) (hc : 0 < s.cap) : ∃ lg, Alloc s mask shift lg := by
  rcases wf.shape with hu | h
  · rw [hu.cap_eq] at hc; omega
  · exact h

/-- A table with no slots is the unallocated one. -/
theorem WF.unalloc_of (wf : WF s size gl mask shift) (hc : s.cap = 0) : Unalloc s mask shift := by
  rcases wf.shape with hu | ⟨lg, ha⟩
  · exact hu
  · have := ha.cap_eq; have := ha.eight_le; omega

/-- An allocated table is mirrored. -/
theorem WF.mirrored (wf : WF s size gl mask shift) (hc : 0 < s.cap) : Mirrored s.ctrl s.cap := by
  obtain ⟨lg, ha⟩ := wf.alloc hc
  rw [ha.cap_eq]; exact ha.mirrored

/-- The geometry of an allocated table on the machine-word path. -/
theorem WF.geom (wf : WF s size gl mask shift) (hs : smallMask mask = true) (hc : 0 < s.cap) :
    Geom s.cap mask := by
  obtain ⟨lg, ha⟩ := wf.alloc hc
  have hlg := ha.smallMask_iff.mp hs
  have hm := ha.mask_toNat hlg
  have hp := two_pow_le_31 hlg
  have := ha.eight_le
  have := USize.le_size
  rw [ha.cap_eq]
  exact ⟨by omega, ⟨lg, rfl⟩, ha.eight_le, by omega⟩

theorem WF.ctrl_size_ge (wf : WF s size gl mask shift) : 8 ≤ s.ctrl.size := by
  rcases wf.shape with hu | ⟨lg, ha⟩
  · rw [hu.ctrl_size]; omega
  · rw [ha.ctrl_size]; have := Nat.two_pow_pos lg; omega

theorem WF.keys_size (wf : WF s size gl mask shift) (hc : 0 < s.cap) :
    s.keys.size = s.cap + 1 := by
  obtain ⟨lg, ha⟩ := wf.alloc hc
  rw [ha.keys_size, ha.cap_eq]

theorem WF.vals_size (wf : WF s size gl mask shift) (hc : 0 < s.cap) :
    s.vals.size = s.cap + 1 := by
  obtain ⟨lg, ha⟩ := wf.alloc hc
  rw [ha.vals_size, ha.cap_eq]

theorem WF.keys_size_eq_vals (wf : WF s size gl mask shift) : s.keys.size = s.vals.size := by
  rcases wf.shape with hu | ⟨lg, ha⟩
  · rw [hu.keys_size, hu.vals_size]
  · rw [ha.keys_size, ha.vals_size]

theorem WF.cap_word (wf : WF s size gl mask shift) : s.ctrl.size - 8 + 8 ≤ s.ctrl.size := by
  have := wf.ctrl_size_ge; omega

theorem WF.cap_le_ctrl (_wf : WF s size gl mask shift) : s.ctrl.size - 8 ≤ s.ctrl.size :=
  Nat.sub_le _ _

theorem WF.keys_lt (wf : WF s size gl mask shift) {i : Nat} (hi : i < s.cap) :
    i < s.keys.size := by
  have := wf.keys_size (by omega); omega

theorem WF.vals_lt (wf : WF s size gl mask shift) {i : Nat} (hi : i < s.cap) :
    i < s.vals.size := by
  have := wf.vals_size (by omega); omega

theorem WF.place_keysN (wf : WF s size gl mask shift) (hc : 0 < s.cap) :
    s.ctrl.size - 8 < s.keys.size := by
  have := wf.keys_size hc; unfold Slots.cap at this; omega

theorem WF.place_valsN (wf : WF s size gl mask shift) (hc : 0 < s.cap) :
    s.ctrl.size - 8 < s.vals.size := by
  have := wf.vals_size hc; unfold Slots.cap at this; omega

theorem WF.ctrl_of_vals (wf : WF s size gl mask shift) {i : Nat} (hi : i < s.vals.size) :
    i < s.ctrl.size := by
  rcases wf.shape with hu | ⟨lg, ha⟩
  · rw [hu.vals_size] at hi; omega
  · rw [ha.vals_size] at hi; rw [ha.ctrl_size]; omega

theorem WF.keys_of_vals (wf : WF s size gl mask shift) {i : Nat} (hi : i < s.vals.size) :
    i < s.keys.size := by
  rw [wf.keys_size_eq_vals]; exact hi

theorem WF.full_ctrl (_wf : WF s size gl mask shift) {i : Nat} (hi : s.IsFull i) :
    i < s.ctrl.size := by
  have := hi.1; unfold Slots.cap at this; omega

theorem WF.full_word (_wf : WF s size gl mask shift) {i : USize} (hi : s.IsFull i.toNat) :
    i.toNat + 8 ≤ s.ctrl.size := by
  have := hi.1; unfold Slots.cap at this; omega

theorem WF.mirror_lt (wf : WF s size gl mask shift) (hc : 0 < s.cap) :
    mask.toNat + 8 < s.ctrl.size := by
  obtain ⟨lg, ha⟩ := wf.alloc hc
  have := ha.mask_le
  have := ha.eight_le
  rw [ha.ctrl_size]
  omega

theorem WF.cap_pos_of_gl (wf : WF s size gl mask shift) (h : 0 < gl) : 0 < s.cap := by
  refine Nat.pos_of_ne_zero fun hc => ?_
  have := wf.room
  rw [hc] at this
  simp [capacityOf] at this
  omega

/-- The placeholder cell, at `mask + 1` on machine words. -/
theorem WF.place_keys (wf : WF s size gl mask shift) (hs : smallMask mask = true)
    (hc : 0 < s.cap) : (mask + 1).toNat < s.keys.size := by
  obtain ⟨lg, ha⟩ := wf.alloc hc
  have hlg := ha.smallMask_iff.mp hs
  have hm := ha.mask_toNat hlg
  have hp := two_pow_le_31 hlg
  have := ha.eight_le
  rw [toNat_add_of_lt (by rw [hm, toNat_one_u]; omega), hm, toNat_one_u, ha.keys_size]
  omega

theorem WF.place_vals (wf : WF s size gl mask shift) (hs : smallMask mask = true)
    (hc : 0 < s.cap) : (mask + 1).toNat < s.vals.size := by
  obtain ⟨lg, ha⟩ := wf.alloc hc
  have hlg := ha.smallMask_iff.mp hs
  have hm := ha.mask_toNat hlg
  have hp := two_pow_le_31 hlg
  have := ha.eight_le
  rw [toNat_add_of_lt (by rw [hm, toNat_one_u]; omega), hm, toNat_one_u, ha.vals_size]
  omega

theorem WF.word0 (wf : WF s size gl mask shift) : (0 : USize).toNat + 8 ≤ s.ctrl.size := by
  have := wf.ctrl_size_ge; simpa using this

theorem WF.word0N (wf : WF s size gl mask shift) : 0 + 8 ≤ s.ctrl.size := by
  have := wf.ctrl_size_ge; omega

/-! ## The invariant: guards and the loops' hypotheses -/

/-- **The two guard forms agree** on every table: `shift = 57 - lg` and `mask = 2 ^ lg - 1`
(`57` and `0` unallocated), and both tests say `lg ≤ 31`. -/
theorem WF.smallMask_eq (wf : WF s size gl mask shift) : smallMask mask = smallShift shift := by
  rcases wf.shape with hu | ⟨lg, ha⟩
  · rw [hu.mask_eq, hu.shift_eq, smallMask_zero, smallShift_57]
  · exact Bool.eq_iff_iff.mpr (ha.smallMask_iff.trans ha.smallShift_iff.symm)

theorem WF.smallMask_of_smallShift (wf : WF s size gl mask shift) (hs : smallShift shift = true) :
    smallMask mask = true := by
  rw [wf.smallMask_eq]; exact hs

/-- On the machine-word path (`smallMask`), at most `2 ^ 31` slots. -/
theorem WF.cap_le_of_smallMask (wf : WF s size gl mask shift) (hs : smallMask mask = true) :
    s.cap ≤ 2 ^ 31 := by
  rcases wf.shape with hu | ⟨lg, ha⟩
  · rw [hu.cap_eq]; omega
  · rw [ha.cap_eq]; exact two_pow_le_31 (ha.smallMask_iff.mp hs)

/-- Off the machine-word path, the table is allocated and has more than `2 ^ 31` slots. -/
theorem WF.cap_gt_of_not_smallMask (wf : WF s size gl mask shift)
    (hs : ¬smallMask mask = true) : 2 ^ 31 < s.cap := by
  rcases wf.shape with hu | ⟨lg, ha⟩
  · rw [hu.mask_eq] at hs; exact absurd smallMask_zero hs
  · rw [ha.cap_eq]
    have := two_pow_ge_32 (fun h => hs (ha.smallMask_iff.mpr h))
    omega

theorem WF.loopU' (wf : WF s size gl mask shift) (hs : smallMask mask = true) :
    LoopU s.ctrl s.keys mask := by
  rcases wf.shape with hu | ⟨lg, ha⟩
  · have hm : mask.toNat = 0 := by rw [hu.mask_eq]; rfl
    refine ⟨⟨?_, ?_⟩, Or.inr ⟨hu.ctrl_eq, hu.mask_eq⟩⟩
    · rw [hm, hu.ctrl_size]; omega
    · rw [hm]; omega
  · have hlg := ha.smallMask_iff.mp hs
    have hm := ha.mask_toNat hlg
    have hp := two_pow_le_31 hlg
    have := ha.eight_le
    refine ⟨⟨?_, ?_⟩, Or.inl ?_⟩
    · rw [hm, ha.ctrl_size]; omega
    · rw [hm]; omega
    · rw [hm, ha.keys_size]; omega

theorem WF.loopU (wf : WF s size gl mask shift) (hs : smallShift shift = true) :
    LoopU s.ctrl s.keys mask :=
  wf.loopU' (wf.smallMask_of_smallShift hs)

theorem WF.ctrlN' (wf : WF s size gl mask shift) (hs : ¬smallMask mask = true) :
    CtrlN s.ctrl (s.ctrl.size - 8) := by
  have hc := wf.cap_gt_of_not_smallMask hs
  have := wf.ctrl_size_ge
  unfold Slots.cap at hc
  exact ⟨by omega, by omega⟩

theorem WF.arrN' (wf : WF s size gl mask shift) (hs : ¬smallMask mask = true) :
    ArrN s.ctrl s.keys (s.ctrl.size - 8) := by
  have hc := wf.cap_gt_of_not_smallMask hs
  exact ⟨wf.ctrlN' hs, wf.place_keysN (by omega)⟩

theorem WF.arrN (wf : WF s size gl mask shift) (hs : ¬smallShift shift = true) :
    ArrN s.ctrl s.keys (s.ctrl.size - 8) :=
  wf.arrN' (by rw [wf.smallMask_eq]; exact hs)

private theorem WF.cap_le_keys (wf : WF s size gl mask shift) : s.cap ≤ s.keys.size := by
  rcases wf.shape with hu | ⟨lg, ha⟩
  · rw [hu.cap_eq]; omega
  · rw [ha.cap_eq, ha.keys_size]; omega

private theorem WF.cap_le_vals (wf : WF s size gl mask shift) : s.cap ≤ s.vals.size := by
  rcases wf.shape with hu | ⟨lg, ha⟩
  · rw [hu.cap_eq]; omega
  · rw [ha.cap_eq, ha.vals_size]; omega

private theorem WF.cap_mod_eight (wf : WF s size gl mask shift) : s.cap % 8 = 0 := by
  rcases wf.shape with hu | ⟨lg, ha⟩
  · rw [hu.cap_eq]
  · rw [ha.cap_eq]; exact Nat.mod_eq_zero_of_dvd (Nat.pow_dvd_pow 2 ha.three_le)

private theorem WF.eight_le_cap (wf : WF s size gl mask shift) (hc : 0 < s.cap) : 8 ≤ s.cap := by
  obtain ⟨lg, ha⟩ := wf.alloc hc
  rw [ha.cap_eq]; exact ha.eight_le

/-- The traversals' slot count `ctrl.usize - 8` is `cap` on the machine-word path. -/
private theorem WF.toNat_usize_sub (wf : WF s size gl mask shift) (hs : smallShift shift = true) :
    (s.ctrl.usize - 8).toNat = s.cap := by
  have hc := wf.cap_le_of_smallMask (wf.smallMask_of_smallShift hs)
  have h8 := wf.ctrl_size_ge
  unfold Slots.cap at hc ⊢
  have hu : s.ctrl.usize.toNat = s.ctrl.size := by
    rw [ByteArray.usize, toNat_toUSize_lt (by omega)]
  rw [USize.toNat_sub_of_le _ _ (by rw [USize.le_iff_toNat_le, hu, toNat_eight_u]; omega), hu,
    toNat_eight_u]

theorem WF.foldU (wf : WF s size gl mask shift) (hs : smallShift shift = true) :
    FoldU s.ctrl s.keys s.vals (s.ctrl.usize - 8) := by
  have hu := wf.toNat_usize_sub hs
  have hc := wf.cap_le_of_smallMask (wf.smallMask_of_smallShift hs)
  exact ⟨by rw [hu]; exact hc, by rw [hu]; exact wf.cap_word, by rw [hu]; exact wf.cap_le_keys,
    by rw [hu]; exact wf.cap_le_vals, by rw [hu]; exact wf.cap_mod_eight⟩

theorem WF.group0 (wf : WF s size gl mask shift) (hs : smallShift shift = true)
    (hc : 0 < s.ctrl.usize - 8) : GroupAt (s.ctrl.usize - 8) 0 := by
  have hu := wf.toNat_usize_sub hs
  have h0 := USize.lt_iff_toNat_lt.mp hc
  rw [USize.toNat_zero, hu] at h0
  have := wf.eight_le_cap h0
  unfold GroupAt
  rw [hu, USize.toNat_zero]
  omega

theorem WF.foldN (wf : WF s size gl mask shift) : FoldN s.ctrl s.keys s.vals (s.ctrl.size - 8) := by
  exact ⟨wf.cap_word, wf.cap_le_keys, wf.cap_le_vals, wf.cap_mod_eight⟩

theorem WF.group0N (wf : WF s size gl mask shift) (hs : ¬smallShift shift = true) :
    GroupAtN (s.ctrl.size - 8) 0 := by
  have hc := wf.cap_gt_of_not_smallMask (by rw [wf.smallMask_eq]; exact hs)
  unfold Slots.cap at hc
  exact ⟨by omega, by omega⟩

theorem WF.revU (wf : WF s size gl mask shift) (hs : smallShift shift = true) :
    RevAtU s.ctrl s.keys s.vals (s.ctrl.usize - 8) := by
  have hu := wf.toNat_usize_sub hs
  have hc := wf.cap_le_of_smallMask (wf.smallMask_of_smallShift hs)
  exact ⟨by rw [hu]; exact wf.cap_le_ctrl, by rw [hu]; exact wf.cap_le_keys,
    by rw [hu]; exact wf.cap_le_vals, by rw [hu]; exact hc⟩

theorem WF.revN (wf : WF s size gl mask shift) : RevAtN s.ctrl s.keys s.vals (s.ctrl.size - 8) := by
  exact ⟨wf.cap_le_ctrl, wf.cap_le_keys, wf.cap_le_vals⟩

theorem WF.moveSrcU (wf : WF s size gl mask shift) {lg : Nat} (h : RebuildPre s size lg)
    (hs : smallMask (((2 : Nat) ^ lg - 1).toUSize) = true) :
    MoveSrcU s.ctrl s.keys s.vals mask := by
  have hlg := (smallMask_pow_iff lg).mp hs
  obtain ⟨lg', ha⟩ := wf.alloc h.alloc
  have hle := h.cap_le
  rw [ha.cap_eq] at hle
  have hlg' : lg' ≤ 31 :=
    (Nat.pow_le_pow_iff_right (by decide)).mp (Nat.le_trans hle (two_pow_le_31 hlg))
  have hm := ha.mask_toNat hlg'
  have hp := two_pow_le_31 hlg'
  have := ha.eight_le
  refine ⟨?_, ?_, ?_, ?_⟩
  · rw [hm]; omega
  · rw [hm, ha.ctrl_size]; omega
  · rw [hm, ha.keys_size]; omega
  · rw [hm, ha.vals_size]; omega

theorem WF.moveSrcN (wf : WF s size gl mask shift) :
    MoveSrcN s.ctrl s.keys s.vals (s.ctrl.size - 8) := by
  exact ⟨wf.cap_le_ctrl, wf.cap_le_keys, wf.cap_le_vals⟩

-- The statement does not use the section's `[BEq α] [Hashable α]`.
set_option linter.unusedSectionVars false in
/-- **The first group of a probe** reads keys only in an allocated table: in the unallocated
one (`emptyGroup`) no lane carries a tag (a tag is below `0x80`) and every lane is EMPTY. -/
theorem firstGroup {ctrl : ByteArray} {keys : Array α} {mask : USize} (h : LoopU ctrl keys mask)
    (q : UInt64) :
    mask.toNat < keys.size ∨
      (matchTag (ctrlWord ctrl (homeU q mask) (and_mask_word h.arr.word)) (repTag (tagOf q)) = 0 ∧
        matchEmpty (ctrlWord ctrl (homeU q mask) (and_mask_word h.arr.word)) ≠ 0) := by
  rcases h.keys with hk | ⟨hc, _⟩
  · exact Or.inl hk
  · right
    have hb : ∀ j < 8,
        byte (ctrlWord ctrl (homeU q mask) (and_mask_word h.arr.word)) j = 0xFF := by
      intro j hj
      exact (byte_ctrlWord _ _ _ hj).trans (getElem_emptyGroup hc _)
    have ht := tagOf_lt q
    constructor
    · refine (isMask_eq_zero_iff (isMask_matchTag _ _)).mpr fun j hj => ?_
      rw [flag_matchTag _ _ hj, hb j hj, beq_eq_false_iff_ne]
      intro heq
      rw [← heq] at ht
      exact absurd ht (by decide)
    · intro h0
      have := (isMask_eq_zero_iff (isMask_matchEmpty _)).mp h0 0 (by decide)
      rw [flag_matchEmpty _ (by decide), hb 0 (by decide)] at this
      exact absurd this (by decide)

/-! ## The invariant: where inserts write -/

theorem WF.new_ctrl (wf : WF s size gl mask shift) {a : α} {q : UInt64} {i : Nat}
    (h : NewSlot s shift a q i) : i < s.ctrl.size := by
  rcases h.slot with hf | ⟨_, hi⟩
  · have := hf.lt; unfold Slots.cap at this; omega
  · have := wf.ctrl_size_ge; omega

theorem WF.new_alloc_gl (wf : WF s size gl mask shift) {a : α} {q : UInt64} {i : Nat}
    (_h : NewSlot s shift a q i) (hgl : ¬(gl == 0) = true) : 0 < s.cap :=
  wf.cap_pos_of_gl (by simp at hgl; omega)

theorem WF.new_alloc_old (wf : WF s size gl mask shift) {a : α} {q : UInt64} {i : USize}
    (_h : NewSlot s shift a q i.toNat) {hi : i.toNat < s.ctrl.size}
    (hold : ¬(s.ctrl.uget i hi == EMPTY) = true) : 0 < s.cap := by
  refine Nat.pos_of_ne_zero fun hc => hold ?_
  have hu := wf.unalloc_of hc
  rw [uget_eq_getElem', getElem_emptyGroup hu.ctrl_eq, EMPTY_eq]
  decide

theorem WF.new_alloc_oldN (wf : WF s size gl mask shift) {a : α} {q : UInt64} {i : Nat}
    (_h : NewSlot s shift a q i) {hi : i < s.ctrl.size}
    (hold : ¬(s.ctrl[i]'hi == EMPTY) = true) : 0 < s.cap := by
  refine Nat.pos_of_ne_zero fun hc => hold ?_
  have hu := wf.unalloc_of hc
  rw [getElem_emptyGroup hu.ctrl_eq, EMPTY_eq]
  decide

theorem WF.new_keys (wf : WF s size gl mask shift) {a : α} {q : UInt64} {i : Nat}
    (h : NewSlot s shift a q i) (hc : 0 < s.cap) : i < s.keys.size := by
  have := wf.keys_size hc
  rcases h.slot with hf | ⟨hc0, _⟩
  · have := hf.lt; omega
  · omega

theorem WF.new_vals (wf : WF s size gl mask shift) {a : α} {q : UInt64} {i : Nat}
    (h : NewSlot s shift a q i) (hc : 0 < s.cap) : i < s.vals.size := by
  have := wf.vals_size hc
  rcases h.slot with hf | ⟨hc0, _⟩
  · have := hf.lt; omega
  · omega

/-! ## Capacity arithmetic and the rebuild's preconditions -/

theorem three_le_lgFor (n : Nat) : 3 ≤ lgFor n := by
  unfold lgFor; omega

private theorem le_two_pow_clog2 (m : Nat) : m ≤ 2 ^ clog2 m := by
  unfold clog2
  split
  · rw [Nat.pow_zero]; omega
  · have := Nat.lt_log2_self (n := m - 1); omega

private theorem clog2_two_pow (k : Nat) : clog2 (2 ^ k) = k := by
  unfold clog2
  split
  · rename_i h
    rcases Nat.eq_zero_or_pos k with hk | hk
    · exact hk.symm
    · have := Nat.one_lt_two_pow (n := k) (by omega); omega
  · rename_i h
    have hk : k ≠ 0 := by rintro rfl; exact h (by simp)
    have hne : 2 ^ k - 1 ≠ 0 := by omega
    have e : 2 ^ k = 2 * 2 ^ (k - 1) := by
      rw [← Nat.pow_succ']; congr 1; omega
    have h1 : (2 ^ k - 1).log2 < k := (Nat.log2_lt hne).mpr (by omega)
    have h2 : k - 1 ≤ (2 ^ k - 1).log2 :=
      (Nat.le_log2 hne).mpr (by have := Nat.two_pow_pos (k - 1); omega)
    omega

/-- A table of `2 ^ lgFor n` slots holds `n` entries. -/
theorem le_capacityOf_lgFor (n : Nat) : n ≤ capacityOf (2 ^ lgFor n) := by
  unfold capacityOf lgFor
  have h := le_two_pow_clog2 ((n + 6) / 7)
  rw [Nat.pow_add, show (2 : Nat) ^ 3 = 8 from rfl, Nat.mul_div_cancel_left _ (by decide : 0 < 8)]
  omega

/-- `lgFor` of the capacity of `(2 : Nat) ^ lg` slots is `lg` (`lg ≥ 3`). -/
theorem lgFor_capacityOf {lg : Nat} (h : 3 ≤ lg) : lgFor (capacityOf ((2 : Nat) ^ lg)) = lg := by
  unfold lgFor capacityOf
  have e : (2 : Nat) ^ lg = 8 * 2 ^ (lg - 3) := by
    rw [show (8 : Nat) = 2 ^ 3 from rfl, ← Nat.pow_add]; congr 1; omega
  rw [e, Nat.mul_div_cancel_left _ (by decide : 0 < 8),
    show (2 ^ (lg - 3) * 7 + 6) / 7 = 2 ^ (lg - 3) by omega, clog2_two_pow]
  omega

theorem WF.rebuildPre_same (wf : WF s size gl mask shift) (hz : ¬(s.keys.size == 0) = true)
    (hh : size + 1 ≤ capacityOf (s.ctrl.size - 8) / 2) :
    RebuildPre s size (lgFor (capacityOf (s.ctrl.size - 8))) := by
  have hc : 0 < s.cap := by
    refine Nat.pos_of_ne_zero fun h0 => hz ?_
    rw [(wf.unalloc_of h0).keys_size]; rfl
  obtain ⟨lg, ha⟩ := wf.alloc hc
  have hcap : s.ctrl.size - 8 = 2 ^ lg := ha.cap_eq
  have hh' : size + 1 ≤ capacityOf (2 ^ lg) / 2 := hcap ▸ hh
  rw [hcap, lgFor_capacityOf ha.three_le]
  exact ⟨hc, ha.three_le, by rw [ha.cap_eq]; exact Nat.le_refl _, by omega⟩

theorem WF.rebuildPre_grow (wf : WF s size gl mask shift) (hz : ¬(s.keys.size == 0) = true) :
    RebuildPre s size (lgFor (max (size + 1) (capacityOf (s.ctrl.size - 8) + 1))) := by
  have hc : 0 < s.cap := by
    refine Nat.pos_of_ne_zero fun h0 => hz ?_
    rw [(wf.unalloc_of h0).keys_size]; rfl
  have hM := le_capacityOf_lgFor (max (size + 1) (capacityOf (s.ctrl.size - 8) + 1))
  have h1 := Nat.le_max_left (size + 1) (capacityOf (s.ctrl.size - 8) + 1)
  have h2 := Nat.le_max_right (size + 1) (capacityOf (s.ctrl.size - 8) + 1)
  refine ⟨hc, three_le_lgFor _, ?_, by omega⟩
  show s.ctrl.size - 8 ≤ _
  unfold capacityOf at hM h2 ⊢
  omega

end WF

end SwissTable.Core.Swiss
