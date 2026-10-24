module

public import OAMap.Core.Swiss.Defs

/-!
# Swiss core proofs, part 1: bounds, termination, and what the code reads off the invariant

A proof file of the SwissTable core (`OAMap/Core/Swiss/Table.lean`, "Proof structure"). Its
owner edits only this file: the proofs, and any private helper lemmas. The statements are fixed:
the code files and the later proof files use them. Some proofs are already done (the one-line
ones); the `sorry`s are what is left.

Contents, and who uses them:

* **Machine-word arithmetic and termination** (`Loops.lean`): masked indices (`and_mask_lt`,
  ...), the probe step and the traversal steps without wrapping below `2 ^ 31`, the `Prod.Lex`
  measures of the loops (`lex_lane`, `lex_group`, `lex_fold`, ...).
* **The loops' erased hypotheses** (`Loops.lean`): the bounds that `ArrU`, `LoopU`, `ArrN`,
  `MoveSrcU`, `FoldU`, ... give, and how they carry over from one iteration to the next.
  `firstGroup`: in the unallocated table no tag matches and the first group has an EMPTY slot.
* **Control arrays** (all later files): sizes and bytes after `setCtrlN` and `eraseCtrlN`, and the
  machine-word forms against the `Nat` ones (`setCtrl_eq_setCtrlN`, `ctrlWord_eq_ctrlWordN`,
  `homeU_toNat`).
* **The invariant** (`Build.lean`, `Table.lean`, all later files): the shape facts (`WF.geom`,
  `WF.mirrored`, the cell bounds), the guards (`WF.smallMask_eq`: `smallMask ↔ smallShift`), the
  hypotheses of the loops from the invariant (`WF.loopU`, `WF.arrN`, `WF.foldU`, ...), the
  unallocated table (`WF.unalloc`), the capacity arithmetic of `lgFor`, and the preconditions of a
  rebuild (`WF.rebuildPre_same`, `WF.rebuildPre_grow`).

Proof hints: `Geom` and `Mirrored` of `Group.lean` carry the slot arithmetic
(`Geom.toNat_and_mask`, `Geom.toNat_add_and_mask`, `byte_ctrlWord_of_mirrored`,
`slotByte_setCtrl`); `smallMask ((2 ^ lg - 1).toUSize) = true ↔ lg ≤ 31` is the heart of the guard
lemmas (see `Shape.fast_of_mask_lt` of the earlier linear-probing map for the wrap argument);
`lowestLane_lt`/`lowestLane64_lt` bound the lanes; `clearLowest_lt` is the lane measure. Write
`(2 : Nat) ^ lg` in statements that unify with code terms: with the bare numeral, the elaborator
tries to evaluate `2 ^ lg` before the default instance fixes its type, and times out.
-/

@[expose] public section

universe u v w

namespace OAMap.Core.Swiss

variable {α : Type u} {β : Type v} {γ : Type w}

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

/-- One probe step on machine words: below `2 ^ 31` slots `stride + 8` does not wrap. -/
theorem sub_group {mask stride : USize} (hsm : mask.toNat < 2 ^ 31)
    (hs : stride.toNat ≤ mask.toNat) (h : ¬stride + 8 > mask) :
    mask.toNat + 8 - (stride + 8).toNat < mask.toNat + 8 - stride.toNat := by
  sorry

theorem lex_group {mask stride : USize} {b b' : Nat} (hsm : mask.toNat < 2 ^ 31)
    (hs : stride.toNat ≤ mask.toNat) (h : ¬stride + 8 > mask) :
    Prod.Lex (fun a₁ a₂ => a₁ < a₂) (fun a₁ a₂ => a₁ < a₂)
      (mask.toNat + 8 - (stride + 8).toNat, b') (mask.toNat + 8 - stride.toNat, b) :=
  Prod.Lex.left _ _ (sub_group hsm hs h)

theorem sub_groupN {cap stride : Nat} (h : ¬cap ≤ stride + 8) :
    cap + 8 - (stride + 8) < cap + 8 - stride := by
  omega

theorem lex_groupN {cap stride : Nat} {b b' : Nat} (h : ¬cap ≤ stride + 8) :
    Prod.Lex (fun a₁ a₂ => a₁ < a₂) (fun a₁ a₂ => a₁ < a₂) (cap + 8 - (stride + 8), b')
      (cap + 8 - stride, b) :=
  Prod.Lex.left _ _ (sub_groupN h)

theorem move_dec {omask i : USize} (hsm : omask.toNat < 2 ^ 31) (hi : ¬i > omask) :
    omask.toNat + 1 - (i + 1).toNat < omask.toNat + 1 - i.toNat := by
  sorry

theorem lex_fold {cap p : USize} {b b' : Nat} (hsm : cap.toNat ≤ 2 ^ 31) (hp : GroupAt cap p)
    (h : p + 8 < cap) :
    Prod.Lex (fun a₁ a₂ => a₁ < a₂) (fun a₁ a₂ => a₁ < a₂)
      (cap.toNat + 8 - (p + 8).toNat, b') (cap.toNat + 8 - p.toNat, b) := by
  sorry

theorem lex_foldN {cap p : Nat} {b b' : Nat} (h : p + 8 < cap) :
    Prod.Lex (fun a₁ a₂ => a₁ < a₂) (fun a₁ a₂ => a₁ < a₂) (cap + 8 - (p + 8), b')
      (cap + 8 - p, b) :=
  Prod.Lex.left _ _ (by omega)

theorem rev_dec {p : USize} (h : ¬p < 8) : (p - 8).toNat < p.toNat := by
  sorry

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
  sorry

theorem FoldU.lane_vals {ctrl : ByteArray} {keys : Array α} {vals : Array β} {cap : USize}
    (h : FoldU ctrl keys vals cap) {p : USize} {fm : UInt64} (hp : GroupAt cap p)
    (hm : IsMask fm) : (p + lowestLane fm).toNat < vals.size := by
  sorry

theorem FoldU.next_word {ctrl : ByteArray} {keys : Array α} {vals : Array β} {cap : USize}
    (h : FoldU ctrl keys vals cap) {p : USize} (hp : GroupAt cap p) (hlt : p + 8 < cap) :
    (p + 8).toNat + 8 ≤ ctrl.size := by
  sorry

theorem FoldU.next_group {ctrl : ByteArray} {keys : Array α} {vals : Array β} {cap : USize}
    (h : FoldU ctrl keys vals cap) {p : USize} (hp : GroupAt cap p) (hlt : p + 8 < cap) :
    GroupAt cap (p + 8) := by
  sorry

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
  sorry

theorem RevGroupU.lane_vals {keys : Array α} {vals : Array β} {p : USize}
    (h : RevGroupU keys vals p) {fm : UInt64} (hm : IsMask fm) :
    (p + lowestLane fm).toNat < vals.size := by
  sorry

theorem RevAtU.word_sub {ctrl : ByteArray} {keys : Array α} {vals : Array β} {p : USize}
    (h : RevAtU ctrl keys vals p) (hp : ¬p < 8) : (p - 8).toNat + 8 ≤ ctrl.size := by
  sorry

theorem RevAtU.group {ctrl : ByteArray} {keys : Array α} {vals : Array β} {p : USize}
    (h : RevAtU ctrl keys vals p) (hp : ¬p < 8) : RevGroupU keys vals (p - 8) := by
  sorry

theorem RevAtU.next {ctrl : ByteArray} {keys : Array α} {vals : Array β} {p : USize}
    (h : RevAtU ctrl keys vals p) (hp : ¬p < 8) : RevAtU ctrl keys vals (p - 8) := by
  sorry

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

/-- `setCtrlN` keeps the mirror. -/
theorem mirrored_setCtrlN {c : ByteArray} {cap : Nat} (h : Mirrored c cap) {i : Nat}
    (hic : i < cap) (b : UInt8) {hi : i < c.size} {hm : cap + 8 ≤ c.size} {hc : 0 < cap} :
    Mirrored (setCtrlN c cap i b hi hm hc) cap := by
  sorry

/-- `setCtrlN` writes exactly slot `i`, as seen through `slotByte`. -/
theorem slotByte_setCtrlN {c : ByteArray} {cap : Nat} (h : Mirrored c cap) {i : Nat}
    (hic : i < cap) (b : UInt8) {hi : i < c.size} {hm : cap + 8 ≤ c.size} {hc : 0 < cap}
    (k : Nat) :
    slotByte (setCtrlN c cap i b hi hm hc) cap k = if k % cap = i then b else slotByte c cap k := by
  sorry

/-- Byte `j` of the group word on `Nat` indices. -/
theorem byte_ctrlWordN (c : ByteArray) (i : Nat) (h : i + 8 ≤ c.size) {j : Nat} (hj : j < 8) :
    byte (ctrlWordN c i h) j = c[i + j]'(by omega) := by
  sorry

/-- Under the mirror, byte `j` of the group word at slot `p` is the byte of slot
`(p + j) % cap`. -/
theorem byte_ctrlWordN_of_mirrored {c : ByteArray} {cap : Nat} (h : Mirrored c cap) {p : Nat}
    (hp : p < cap) {hw : p + 8 ≤ c.size} {j : Nat} (hj : j < 8) :
    byte (ctrlWordN c p hw) j = slotByte c cap ((p + j) % cap) := by
  sorry

/-- The machine-word group read is the `Nat` one (when the index does not wrap). -/
theorem ctrlWord_eq_ctrlWordN {c : ByteArray} {i : USize} (hs : i.toNat < 2 ^ 31)
    {h : i.toNat + 8 ≤ c.size} {h' : i.toNat + 8 ≤ c.size} :
    ctrlWord c i h = ctrlWordN c i.toNat h' := by
  sorry

/-- The machine-word control write is the `Nat` one. -/
theorem setCtrl_eq_setCtrlN {c : ByteArray} {cap : Nat} {mask i : USize} (hg : Geom cap mask)
    (hsz : c.size = cap + 8) (hic : i.toNat < cap) {b : UInt8} {h1 : i.toNat < c.size}
    {h2 : mask.toNat + 8 < c.size} {h3 : i.toNat < c.size} {h4 : cap + 8 ≤ c.size}
    {h5 : 0 < cap} : setCtrl c mask i b h1 h2 = setCtrlN c cap i.toNat b h3 h4 h5 := by
  sorry

/-- The machine-word home slot is the `Nat` one. -/
theorem homeU_toNat {q : UInt64} {cap : Nat} {mask : USize} (hg : Geom cap mask) :
    (homeU q mask).toNat = homeN q cap := by
  sorry

/-- `getElem!` of a `ByteArray` in range is `getElem`. -/
theorem getElem!_eq_getElem {c : ByteArray} {i : Nat} (h : i < c.size) : c[i]! = c[i] := by
  sorry

/-! ## Slots -/

theorem Slots.IsFull.cap_pos {s : Slots α β} {i : Nat} (hi : s.IsFull i) : 0 < s.cap := by
  have := hi.1; omega

theorem isFull_of {s : Slots α β} {i : Nat} (hi : i < s.cap) {h : i < s.ctrl.size}
    (hf : s.ctrl[i]'h < 0x80) : s.IsFull i :=
  ⟨hi, by rwa [getElem!_eq_getElem h]⟩

/-- A tag is a FULL byte. -/
theorem tagOf_lt (q : UInt64) : tagOf q < 0x80 := by
  unfold tagOf; exact toUInt8_and_7F_lt q

/-! ## The invariant: shape -/

section WF

variable [BEq α] [Hashable α] {s : Slots α β} {size gl : Nat} {mask : USize} {shift : UInt64}

/-- The unallocated table is well formed. -/
theorem WF.unalloc : WF (⟨emptyGroup, #[], #[]⟩ : Slots α β) 0 0 0 57 := by
  sorry

/-- An allocated table (`0 < cap`) has `(2 : Nat) ^ lg` slots. -/
theorem WF.alloc (wf : WF s size gl mask shift) (hc : 0 < s.cap) : ∃ lg, Alloc s mask shift lg := by
  sorry

/-- A table with no slots is the unallocated one. -/
theorem WF.unalloc_of (wf : WF s size gl mask shift) (hc : s.cap = 0) : Unalloc s mask shift := by
  sorry

/-- An allocated table is mirrored. -/
theorem WF.mirrored (wf : WF s size gl mask shift) (hc : 0 < s.cap) : Mirrored s.ctrl s.cap := by
  sorry

/-- The geometry of an allocated table on the machine-word path. -/
theorem WF.geom (wf : WF s size gl mask shift) (hs : smallMask mask = true) (hc : 0 < s.cap) :
    Geom s.cap mask := by
  sorry

theorem WF.ctrl_size_ge (wf : WF s size gl mask shift) : 8 ≤ s.ctrl.size := by
  sorry

theorem WF.keys_size (wf : WF s size gl mask shift) (hc : 0 < s.cap) :
    s.keys.size = s.cap + 1 := by
  sorry

theorem WF.vals_size (wf : WF s size gl mask shift) (hc : 0 < s.cap) :
    s.vals.size = s.cap + 1 := by
  sorry

theorem WF.keys_size_eq_vals (wf : WF s size gl mask shift) : s.keys.size = s.vals.size := by
  sorry

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
  sorry

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
  sorry

theorem WF.cap_pos_of_gl (wf : WF s size gl mask shift) (h : 0 < gl) : 0 < s.cap := by
  sorry

/-- The placeholder cell, at `mask + 1` on machine words. -/
theorem WF.place_keys (wf : WF s size gl mask shift) (hs : smallMask mask = true)
    (hc : 0 < s.cap) : (mask + 1).toNat < s.keys.size := by
  sorry

theorem WF.place_vals (wf : WF s size gl mask shift) (hs : smallMask mask = true)
    (hc : 0 < s.cap) : (mask + 1).toNat < s.vals.size := by
  sorry

theorem WF.word0 (wf : WF s size gl mask shift) : (0 : USize).toNat + 8 ≤ s.ctrl.size := by
  have := wf.ctrl_size_ge; simpa using this

theorem WF.word0N (wf : WF s size gl mask shift) : 0 + 8 ≤ s.ctrl.size := by
  have := wf.ctrl_size_ge; omega

/-! ## The invariant: guards and the loops' hypotheses -/

/-- **The two guard forms agree** on every table: `shift = 57 - lg` and `mask = 2 ^ lg - 1`
(`57` and `0` unallocated), and both tests say `lg ≤ 31`. -/
theorem WF.smallMask_eq (wf : WF s size gl mask shift) : smallMask mask = smallShift shift := by
  sorry

theorem WF.smallMask_of_smallShift (wf : WF s size gl mask shift) (hs : smallShift shift = true) :
    smallMask mask = true := by
  rw [wf.smallMask_eq]; exact hs

/-- On the machine-word path (`smallMask`), at most `2 ^ 31` slots. -/
theorem WF.cap_le_of_smallMask (wf : WF s size gl mask shift) (hs : smallMask mask = true) :
    s.cap ≤ 2 ^ 31 := by
  sorry

/-- Off the machine-word path, the table is allocated and has more than `2 ^ 31` slots. -/
theorem WF.cap_gt_of_not_smallMask (wf : WF s size gl mask shift)
    (hs : ¬smallMask mask = true) : 2 ^ 31 < s.cap := by
  sorry

theorem WF.loopU' (wf : WF s size gl mask shift) (hs : smallMask mask = true) :
    LoopU s.ctrl s.keys mask := by
  sorry

theorem WF.loopU (wf : WF s size gl mask shift) (hs : smallShift shift = true) :
    LoopU s.ctrl s.keys mask :=
  wf.loopU' (wf.smallMask_of_smallShift hs)

theorem WF.ctrlN' (wf : WF s size gl mask shift) (hs : ¬smallMask mask = true) :
    CtrlN s.ctrl (s.ctrl.size - 8) := by
  sorry

theorem WF.arrN' (wf : WF s size gl mask shift) (hs : ¬smallMask mask = true) :
    ArrN s.ctrl s.keys (s.ctrl.size - 8) := by
  sorry

theorem WF.arrN (wf : WF s size gl mask shift) (hs : ¬smallShift shift = true) :
    ArrN s.ctrl s.keys (s.ctrl.size - 8) :=
  wf.arrN' (by rw [wf.smallMask_eq]; exact hs)

theorem WF.foldU (wf : WF s size gl mask shift) (hs : smallShift shift = true) :
    FoldU s.ctrl s.keys s.vals (s.ctrl.usize - 8) := by
  sorry

theorem WF.group0 (wf : WF s size gl mask shift) (hs : smallShift shift = true)
    (hc : 0 < s.ctrl.usize - 8) : GroupAt (s.ctrl.usize - 8) 0 := by
  sorry

theorem WF.foldN (wf : WF s size gl mask shift) : FoldN s.ctrl s.keys s.vals (s.ctrl.size - 8) := by
  sorry

theorem WF.group0N (wf : WF s size gl mask shift) (hs : ¬smallShift shift = true) :
    GroupAtN (s.ctrl.size - 8) 0 := by
  sorry

theorem WF.revU (wf : WF s size gl mask shift) (hs : smallShift shift = true) :
    RevAtU s.ctrl s.keys s.vals (s.ctrl.usize - 8) := by
  sorry

theorem WF.revN (wf : WF s size gl mask shift) : RevAtN s.ctrl s.keys s.vals (s.ctrl.size - 8) := by
  sorry

theorem WF.moveSrcU (wf : WF s size gl mask shift) {lg : Nat} (h : RebuildPre s size lg)
    (hs : smallMask (((2 : Nat) ^ lg - 1).toUSize) = true) :
    MoveSrcU s.ctrl s.keys s.vals mask := by
  sorry

theorem WF.moveSrcN (wf : WF s size gl mask shift) :
    MoveSrcN s.ctrl s.keys s.vals (s.ctrl.size - 8) := by
  sorry

/-- **The first group of a probe** reads keys only in an allocated table: in the unallocated
one (`emptyGroup`) no lane carries a tag (a tag is below `0x80`) and every lane is EMPTY. -/
theorem firstGroup {ctrl : ByteArray} {keys : Array α} {mask : USize} (h : LoopU ctrl keys mask)
    (q : UInt64) :
    mask.toNat < keys.size ∨
      (matchTag (ctrlWord ctrl (homeU q mask) (and_mask_word h.arr.word)) (repTag (tagOf q)) = 0 ∧
        matchEmpty (ctrlWord ctrl (homeU q mask) (and_mask_word h.arr.word)) ≠ 0) := by
  sorry

/-! ## The invariant: where inserts write -/

theorem WF.new_ctrl (wf : WF s size gl mask shift) {a : α} {q : UInt64} {i : Nat}
    (h : NewSlot s shift a q i) : i < s.ctrl.size := by
  sorry

theorem WF.new_alloc_gl (wf : WF s size gl mask shift) {a : α} {q : UInt64} {i : Nat}
    (_h : NewSlot s shift a q i) (hgl : ¬(gl == 0) = true) : 0 < s.cap :=
  wf.cap_pos_of_gl (by simp at hgl; omega)

theorem WF.new_alloc_old (wf : WF s size gl mask shift) {a : α} {q : UInt64} {i : USize}
    (h : NewSlot s shift a q i.toNat) {hi : i.toNat < s.ctrl.size}
    (hold : ¬(s.ctrl.uget i hi == EMPTY) = true) : 0 < s.cap := by
  sorry

theorem WF.new_alloc_oldN (wf : WF s size gl mask shift) {a : α} {q : UInt64} {i : Nat}
    (h : NewSlot s shift a q i) {hi : i < s.ctrl.size}
    (hold : ¬(s.ctrl[i]'hi == EMPTY) = true) : 0 < s.cap := by
  sorry

theorem WF.new_keys (wf : WF s size gl mask shift) {a : α} {q : UInt64} {i : Nat}
    (h : NewSlot s shift a q i) (hc : 0 < s.cap) : i < s.keys.size := by
  sorry

theorem WF.new_vals (wf : WF s size gl mask shift) {a : α} {q : UInt64} {i : Nat}
    (h : NewSlot s shift a q i) (hc : 0 < s.cap) : i < s.vals.size := by
  sorry

/-! ## Capacity arithmetic and the rebuild's preconditions -/

theorem three_le_lgFor (n : Nat) : 3 ≤ lgFor n := by
  unfold lgFor; omega

/-- A table of `2 ^ lgFor n` slots holds `n` entries. -/
theorem le_capacityOf_lgFor (n : Nat) : n ≤ capacityOf (2 ^ lgFor n) := by
  sorry

/-- `lgFor` of the capacity of `(2 : Nat) ^ lg` slots is `lg` (`lg ≥ 3`). -/
theorem lgFor_capacityOf {lg : Nat} (h : 3 ≤ lg) : lgFor (capacityOf ((2 : Nat) ^ lg)) = lg := by
  sorry

theorem WF.rebuildPre_same (wf : WF s size gl mask shift) (hz : ¬(s.keys.size == 0) = true)
    (hh : size + 1 ≤ capacityOf (s.ctrl.size - 8) / 2) :
    RebuildPre s size (lgFor (capacityOf (s.ctrl.size - 8))) := by
  sorry

theorem WF.rebuildPre_grow (wf : WF s size gl mask shift) (hz : ¬(s.keys.size == 0) = true)
    (hh : ¬size + 1 ≤ capacityOf (s.ctrl.size - 8) / 2) :
    RebuildPre s size (lgFor (max (size + 1) (capacityOf (s.ctrl.size - 8) + 1))) := by
  sorry

end WF

end OAMap.Core.Swiss
