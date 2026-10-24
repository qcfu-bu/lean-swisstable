module

public import SwissTable.Core.Swiss.Table
public import Std.Data.Internal.List.Associative

/-!
# Swiss core proofs, part 8: filter, filterMap, map and the traversals (contract 17–22)

A proof file of the Swiss core (`SwissTable/Core/Swiss/Table.lean`, "Proof structure"): the
contract lemmas 17–22 (`docs/ARCHITECTURE.md` §3.3). All six are **U**: no lawfulness, only the
invariant's unconditional part (`WF.shape`, `WF.size_eq`).

* **The traversals** (`foldM`, `foldRev`, `forIn`) go a group at a time over the `matchFull` mask
  of each group, lowest lane first (`foldRev`: highest lane first, last group first); the groups
  at `0, 8, …, cap - 8` never wrap, so byte `j` of the group at `p` is slot `p + j`
  (`byte_ctrlWord'`, `byte_ctrlWordN`) and a lane's flag says the slot is full
  (`flag_matchFull`); `lowestLane_spec` and `flag_clearLowest` walk the lanes in order. So each
  loop folds over `entryAt` of the slots in (reverse) order: `(List.range cap).filterMap entryAt`
  is the model. The unallocated table has no group to visit (`cap = 0`).
  In the proofs, `laneEntries s p fm` is the list of entries of the lanes of `fm` in the group at
  `p`, and `restEntries` is that list followed by the full slots of the later groups: what a
  forward loop at `(p, fm)` has still to visit. Each `Nat` loop is shown by functional induction
  to fold over `restEntries` (`foldMLoopN_spec`, `forInLoopN_spec`; `foldRevGroupN_spec` and
  `foldRevLoopN_spec` for the reverse fold), and each machine-word loop equals its `Nat` loop
  (`foldMLoop_eq_gen`, `forInLoop_eq_gen`, `foldRevGroup_eq_gen`, `foldRevLoop_eq_gen`; from the
  first group, `foldMLoop_eq_foldMLoopN`).
* **filter** erases the rejected entries in slot order (`filterLoop_entries`): pointwise, an
  erasure removes exactly its slot (`eraseAtN_entryAt`, from `entryAt_eraseN` of
  `Proofs/Write.lean`).
* **filterMap** is `filterMap_entries_raw` of `Proofs/Bulk.lean`, or the unallocated table when
  `firstSome` finds nothing (`firstSome_none`: every entry is rejected).
* **map** rewrites the value of each full slot (`Array.getElem_mapFinIdx`, slot by slot), or is
  the unallocated table when `firstFull` finds no full slot (`firstFull_none`).
-/

@[expose] public section

universe u v w w'

open Std.Internal.List

namespace SwissTable.Core

namespace Swiss

variable {α : Type u} {β : Type v} {γ : Type w}

/-! ## The entries, slot by slot -/

/-- With no full slot, there is no entry. -/
private theorem entries_eq_nil_of {s : Slots α β}
    (h : ∀ j, j < s.cap → ∀ hc : j < s.ctrl.size, ¬s.ctrl[j] < 0x80) : s.entries = [] := by
  apply List.eq_nil_iff_forall_not_mem.mpr
  intro e he
  obtain ⟨j, hj, hje⟩ := mem_entries.mp he
  obtain ⟨hc, hf, -, -⟩ := entryAt_eq_some hje
  exact h j hj hc (by rwa [getElem!_eq_getElem hc] at hf)

/-- The unallocated table has no entry. -/
private theorem emptyImpl_entries [BEq α] [Hashable α] (c : Nat) :
    (emptyImpl c : Table α β).slots.entries = [] := by
  rfl

/-! ## The lanes of a group -/

/-- The entries of the lanes of `fm` in the group at slot `p`, lowest lane first. -/
private def laneEntries (s : Slots α β) (p : Nat) (fm : UInt64) : List ((_ : α) × β) :=
  (List.range 8).filterMap fun j => if flag fm j then s.entryAt (p + j) else none

/-- Every lane of `fm` is a full slot of the group at `p`. -/
private def SubFull (ctrl : ByteArray) (p : Nat) (fm : UInt64) : Prop :=
  ∀ j < 8, flag fm j = true → ∀ h : p + j < ctrl.size, ctrl[p + j] < 0x80

/-- The lanes of `fm` are exactly the full slots of the group at `p`. -/
private def FullMask (ctrl : ByteArray) (p : Nat) (fm : UInt64) : Prop :=
  ∀ j < 8, ∀ h : p + j < ctrl.size, flag fm j = decide (ctrl[p + j] < 0x80)

private theorem FullMask.sub {ctrl : ByteArray} {p : Nat} {fm : UInt64} (h : FullMask ctrl p fm) :
    SubFull ctrl p fm := by
  intro j hj hf hc
  rw [h j hj hc] at hf
  exact of_decide_eq_true hf

private theorem SubFull.clearLowest {ctrl : ByteArray} {p : Nat} {fm : UInt64}
    (h : SubFull ctrl p fm) (hm : IsMask fm) (h0 : fm ≠ 0) : SubFull ctrl p (clearLowest fm) := by
  intro j hj hf hc
  rw [flag_clearLowest hm h0, Bool.and_eq_true] at hf
  exact h j hj hf.1 hc

private theorem fullMask_ctrlWordN (ctrl : ByteArray) (p : Nat) (h : p + 8 ≤ ctrl.size) :
    FullMask ctrl p (matchFull (ctrlWordN ctrl p h)) := by
  intro j hj hc
  rw [flag_matchFull _ hj, byte_ctrlWordN ctrl p h hj]

private theorem fullMask_ctrlWord (ctrl : ByteArray) (p : USize) (h : p.toNat + 8 ≤ ctrl.size)
    (hw : p.toNat + 8 ≤ USize.size) : FullMask ctrl p.toNat (matchFull (ctrlWord ctrl p h)) := by
  intro j hj hc
  rw [flag_matchFull _ hj, byte_ctrlWord' ctrl p h hw hj]

private theorem laneEntries_zero (s : Slots α β) (p : Nat) : laneEntries s p 0 = [] := by
  unfold laneEntries
  simp [flag_zero]

/-- The lowest lane first: the lanes of `fm` are its lowest lane, then those of
`clearLowest fm`. -/
private theorem laneEntries_step (s : Slots α β) (p : Nat) {fm : UInt64} (hm : IsMask fm)
    (h0 : fm ≠ 0) :
    laneEntries s p fm =
      (s.entryAt (p + (lowestLane fm).toNat)).toList ++ laneEntries s p (clearLowest fm) := by
  obtain ⟨hl8, hlf, hlb⟩ := lowestLane_spec hm h0
  generalize hl : (lowestLane fm).toNat = l at hl8 hlf hlb
  have hc := flag_clearLowest hm h0
  rw [hl] at hc
  have hr : List.range 8 = List.range' 0 l ++ (l :: List.range' (l + 1) (7 - l)) := by
    have e : (8 : Nat) = l + ((7 - l) + 1) := by omega
    rw [List.range_eq_range', e, ← List.range'_append, List.range'_succ]
    simp
  unfold laneEntries
  rw [hr, List.filterMap_append, List.filterMap_append, List.filterMap_cons, List.filterMap_cons]
  have e1 : (List.range' 0 l).filterMap
      (fun j => if flag fm j then s.entryAt (p + j) else none) = [] := by
    rw [List.filterMap_eq_nil_iff]
    intro a ha
    rw [List.mem_range'_1] at ha
    simp [hlb a (by omega)]
  have e2 : (List.range' 0 l).filterMap
      (fun j => if flag (clearLowest fm) j then s.entryAt (p + j) else none) = [] := by
    rw [List.filterMap_eq_nil_iff]
    intro a ha
    rw [List.mem_range'_1] at ha
    simp [hc, hlb a (by omega)]
  have e3 : (List.range' (l + 1) (7 - l)).filterMap
      (fun j => if flag (clearLowest fm) j then s.entryAt (p + j) else none) =
      (List.range' (l + 1) (7 - l)).filterMap
      (fun j => if flag fm j then s.entryAt (p + j) else none) := by
    apply filterMap_congr_mem
    intro a ha
    rw [List.mem_range'_1] at ha
    have : (a != l) = true := by simp; omega
    simp [hc, this]
  rw [e1, e2, e3]
  simp only [hlf, hc, bne_self_eq_false, Bool.and_false, ite_true, Bool.false_eq_true, ite_false,
    List.nil_append]
  cases s.entryAt (p + l) <;> simp

/-- The lowest lane of a mask of full lanes. -/
private theorem laneEntries_lane (s : Slots α β) (p : Nat) {fm : UInt64} (hm : IsMask fm)
    (h0 : fm ≠ 0) (hs : SubFull s.ctrl p fm) (hc : p + 8 ≤ s.ctrl.size) (hk : p + 8 ≤ s.keys.size)
    (hv : p + 8 ≤ s.vals.size) :
    laneEntries s p fm =
      ⟨s.keys[p + (lowestLane64 fm).toNat]'(by have := lowestLane64_lt hm; omega),
        s.vals[p + (lowestLane64 fm).toNat]'(by have := lowestLane64_lt hm; omega)⟩ ::
        laneEntries s p (clearLowest fm) := by
  obtain ⟨hl8, hlf, -⟩ := lowestLane_spec hm h0
  rw [laneEntries_step s p hm h0]
  have e := toNat_lowestLane_of_isMask hm
  rw [e] at hl8 hlf ⊢
  rw [entryAt_of_full (s := s) (by omega) (hs _ hl8 hlf (by omega))]
  rfl

/-- The lanes of the full mask of a group are its full slots. -/
private theorem laneEntries_full (s : Slots α β) {p : Nat} {fm : UInt64}
    (hw : p + 8 ≤ s.ctrl.size) (h : FullMask s.ctrl p fm) :
    laneEntries s p fm = (List.range' p 8).filterMap s.entryAt := by
  unfold laneEntries
  rw [List.range'_eq_map_range, List.filterMap_map]
  apply filterMap_congr_mem
  intro j hj
  rw [List.mem_range] at hj
  simp only [Function.comp]
  rw [h j hj (by omega)]
  by_cases hf : s.ctrl[p + j] < 0x80
  · simp [hf]
  · simp [hf, entryAt_of_not_full (s := s) (by omega) hf]

/-- What a traversal from the lanes `fm` of the group at `p` still visits: those lanes, then
every full slot of the later groups. -/
private def restEntries (s : Slots α β) (cap p : Nat) (fm : UInt64) : List ((_ : α) × β) :=
  laneEntries s p fm ++ (List.range' (p + 8) (cap - (p + 8))).filterMap s.entryAt

private theorem restEntries_lane (s : Slots α β) (cap p : Nat) {fm : UInt64} (hm : IsMask fm)
    (h0 : fm ≠ 0) (hs : SubFull s.ctrl p fm) (hc : p + 8 ≤ s.ctrl.size) (hk : p + 8 ≤ s.keys.size)
    (hv : p + 8 ≤ s.vals.size) :
    restEntries s cap p fm =
      ⟨s.keys[p + (lowestLane64 fm).toNat]'(by have := lowestLane64_lt hm; omega),
        s.vals[p + (lowestLane64 fm).toNat]'(by have := lowestLane64_lt hm; omega)⟩ ::
        restEntries s cap p (clearLowest fm) := by
  unfold restEntries
  rw [laneEntries_lane s p hm h0 hs hc hk hv, List.cons_append]

private theorem restEntries_next (s : Slots α β) {cap p : Nat} {fm : UInt64} (h16 : p + 16 ≤ cap)
    (hw : p + 16 ≤ s.ctrl.size) (h : FullMask s.ctrl (p + 8) fm) :
    restEntries s cap p 0 = restEntries s cap (p + 8) fm := by
  unfold restEntries
  rw [laneEntries_zero, List.nil_append, laneEntries_full s (by omega) h, ← List.filterMap_append]
  congr 1
  have e : cap - (p + 8) = 8 + (cap - (p + 8 + 8)) := by omega
  rw [e, ← List.range'_append]

private theorem restEntries_end (s : Slots α β) {cap p : Nat} (hlt : ¬p + 8 < cap) :
    restEntries s cap p 0 = [] := by
  unfold restEntries
  rw [laneEntries_zero, List.nil_append, show cap - (p + 8) = 0 by omega]
  rfl

private theorem restEntries_init (s : Slots α β) {cap : Nat} {fm : UInt64} (h8 : 8 ≤ cap)
    (hw : 8 ≤ s.ctrl.size) (h : FullMask s.ctrl 0 fm) :
    restEntries s cap 0 fm = (List.range cap).filterMap s.entryAt := by
  unfold restEntries
  rw [laneEntries_full s (by omega) h, ← List.filterMap_append]
  congr 1
  have e : cap = 8 + (cap - (0 + 8)) := by omega
  rw [List.range_eq_range']
  conv => rhs; rw [e]
  rw [← List.range'_append]

/-! ## The traversals on `Nat` indices fold over the entries -/

/-- The next group of a traversal of `cap` slots (a multiple of 8). -/
private theorem next16 {cap p : Nat} (hp : GroupAtN cap p) (h8 : cap % 8 = 0) (hlt : p + 8 < cap) :
    p + 16 ≤ cap := by
  have := hp.2; omega

private theorem foldMLoopN_spec {ε : Type w} {m : Type w → Type w'} [Monad m]
    (f : ε → α → β → m ε) (ctrl : ByteArray) (keys : Array α) (vals : Array β) (cap : Nat)
    (hF : FoldN ctrl keys vals cap) (p : Nat) (fm : UInt64) (acc : ε) (hp : GroupAtN cap p)
    (hm : IsMask fm) (hs : SubFull ctrl p fm) :
    foldMLoopN f ctrl keys vals cap p fm acc hF hp hm =
      (restEntries ⟨ctrl, keys, vals⟩ cap p fm).foldlM (fun d e => f d e.1 e.2) acc := by
  revert hs
  induction p, fm, acc, hp, hm using foldMLoopN.induct ctrl keys vals cap hF with
  | case1 p fm acc hp hm h ih =>
    intro hs
    have h0 := ne_zero_of_bne h
    rw [foldMLoopN, dite_eq_left h,
      restEntries_lane ⟨ctrl, keys, vals⟩ cap p hm h0 hs
        (by dsimp only; have := hF.word; have := hp.1; omega)
        (by dsimp only; have := hF.keys; have := hp.1; omega)
        (by dsimp only; have := hF.vals; have := hp.1; omega),
      List.foldlM_cons]
    dsimp only
    congr 1
    funext acc'
    exact ih acc' (hs.clearLowest hm h0)
  | case2 p fm acc hp hm h _ hlt ih =>
    intro _
    have hlt : p + 8 < cap := hlt
    have := eq_zero_of_not_bne h
    subst this
    rw [foldMLoopN, dite_eq_right h]
    dsimp only
    rw [dite_eq_left hlt, ih ((fullMask_ctrlWordN ctrl (p + 8) _).sub),
      restEntries_next ⟨ctrl, keys, vals⟩ (next16 hp hF.eight hlt)
        (by dsimp only; have := hF.word; have := next16 hp hF.eight hlt; omega)
        (fullMask_ctrlWordN ctrl (p + 8) _)]
  | case3 p fm acc hp hm h _ hlt =>
    intro _
    have hlt : ¬p + 8 < cap := hlt
    have := eq_zero_of_not_bne h
    subst this
    rw [foldMLoopN, dite_eq_right h]
    dsimp only
    rw [dite_eq_right hlt, restEntries_end _ hlt]
    rfl

private theorem forInLoopN_spec {ε : Type w} {m : Type w → Type w'} [Monad m]
    (f : α → β → ε → m (ForInStep ε)) (ctrl : ByteArray) (keys : Array α) (vals : Array β)
    (cap : Nat) (hF : FoldN ctrl keys vals cap) (p : Nat) (fm : UInt64) (acc : ε)
    (hp : GroupAtN cap p) (hm : IsMask fm) (hs : SubFull ctrl p fm) :
    forInLoopN f ctrl keys vals cap p fm acc hF hp hm =
      ForIn.forIn (restEntries ⟨ctrl, keys, vals⟩ cap p fm) acc (fun e d => f e.1 e.2 d) := by
  revert hs
  induction p, fm, acc, hp, hm using forInLoopN.induct ctrl keys vals cap hF with
  | case1 p fm acc hp hm h ih =>
    intro hs
    have h0 := ne_zero_of_bne h
    rw [forInLoopN, dite_eq_left h,
      restEntries_lane ⟨ctrl, keys, vals⟩ cap p hm h0 hs
        (by dsimp only; have := hF.word; have := hp.1; omega)
        (by dsimp only; have := hF.keys; have := hp.1; omega)
        (by dsimp only; have := hF.vals; have := hp.1; omega),
      List.forIn_cons]
    dsimp only
    congr 1
    funext r
    cases r with
    | done b => rfl
    | yield b => exact ih b (hs.clearLowest hm h0)
  | case2 p fm acc hp hm h _ hlt ih =>
    intro _
    have hlt : p + 8 < cap := hlt
    have := eq_zero_of_not_bne h
    subst this
    rw [forInLoopN, dite_eq_right h]
    dsimp only
    rw [dite_eq_left hlt, ih ((fullMask_ctrlWordN ctrl (p + 8) _).sub),
      restEntries_next ⟨ctrl, keys, vals⟩ (next16 hp hF.eight hlt)
        (by dsimp only; have := hF.word; have := next16 hp hF.eight hlt; omega)
        (fullMask_ctrlWordN ctrl (p + 8) _)]
  | case3 p fm acc hp hm h _ hlt =>
    intro _
    have hlt : ¬p + 8 < cap := hlt
    have := eq_zero_of_not_bne h
    subst this
    rw [forInLoopN, dite_eq_right h]
    dsimp only
    rw [dite_eq_right hlt, restEntries_end _ hlt, List.forIn_nil]

private theorem foldRevGroupN_spec {ε : Type w} (f : ε → α → β → ε) (ctrl : ByteArray)
    (keys : Array α) (vals : Array β) (p : Nat) (acc : ε) (hp : RevGroupN keys vals p)
    (hw : p + 8 ≤ ctrl.size) (fm : UInt64) (hm : IsMask fm) (hs : SubFull ctrl p fm) :
    foldRevGroupN f keys vals p fm acc hp hm =
      (laneEntries ⟨ctrl, keys, vals⟩ p fm).foldr (fun e d => f d e.1 e.2) acc := by
  revert hs
  induction fm, hm using foldRevGroupN.induct p with
  | case1 fm hm h ih =>
    intro hs
    have h0 := ne_zero_of_bne h
    rw [foldRevGroupN, dite_eq_left h,
      laneEntries_lane ⟨ctrl, keys, vals⟩ p hm h0 hs hw hp.keys hp.vals, List.foldr_cons,
      ih (hs.clearLowest hm h0)]
  | case2 fm hm h =>
    intro _
    have := eq_zero_of_not_bne h
    subst this
    rw [foldRevGroupN, dite_eq_right h, laneEntries_zero]
    rfl

private theorem foldRevLoopN_spec {ε : Type w} (f : ε → α → β → ε) (ctrl : ByteArray)
    (keys : Array α) (vals : Array β) (p : Nat) (acc : ε) (hp : RevAtN ctrl keys vals p)
    (h8 : p % 8 = 0) :
    foldRevLoopN f ctrl keys vals p acc hp =
      ((List.range p).filterMap (Slots.entryAt ⟨ctrl, keys, vals⟩)).foldr
        (fun e d => f d e.1 e.2) acc := by
  revert h8
  induction p, acc, hp using foldRevLoopN.induct f ctrl keys vals with
  | case1 p acc hp h =>
    intro h8
    have : p = 0 := by omega
    subst this
    rw [foldRevLoopN, dite_eq_left h]
    rfl
  | case2 p acc hp h p' acc' ih =>
    intro h8
    rw [foldRevLoopN, dite_eq_right h]
    dsimp only
    rw [ih (by omega)]
    simp only [p', acc']
    rw [foldRevGroupN_spec f ctrl keys vals (p - 8) acc _ (by have := hp.word; omega)
      _ _ (fullMask_ctrlWordN ctrl (p - 8) _).sub,
      laneEntries_full ⟨ctrl, keys, vals⟩ (by dsimp only; have := hp.word; omega)
        (fullMask_ctrlWordN ctrl (p - 8) _),
      ← List.foldr_append, ← List.filterMap_append]
    congr 2
    have e : p = (p - 8) + 8 := by omega
    rw [List.range_eq_range', List.range_eq_range']
    conv => rhs; rw [e]
    rw [← List.range'_append]
    simp

/-! ## The machine-word traversals are the `Nat` ones -/

private theorem toNat_add_lowestLane {p : USize} {fm : UInt64} (hm : IsMask fm)
    (h : p.toNat ≤ 2 ^ 31) : (p + lowestLane fm).toNat = p.toNat + (lowestLane64 fm).toNat := by
  have := lowestLane_lt hm
  rw [toNat_add_of_lt (by omega), toNat_lowestLane_of_isMask hm]

private theorem FoldU.toN {ctrl : ByteArray} {keys : Array α} {vals : Array β} {cap : USize}
    (h : FoldU ctrl keys vals cap) : FoldN ctrl keys vals cap.toNat :=
  ⟨h.word, h.keys, h.vals, h.eight⟩

/-- `foldMLoop_eq_foldMLoopN`, with the `Nat` position and mask given by equations. -/
private theorem foldMLoop_eq_gen {ε : Type w} {m : Type w → Type w'} [Monad m]
    (f : ε → α → β → m ε) (ctrl : ByteArray) (keys : Array α) (vals : Array β) (cap : USize)
    (hF : FoldU ctrl keys vals cap) (p : USize) (fm : UInt64) (acc : ε) (hp : GroupAt cap p)
    (hm : IsMask fm) :
    ∀ (n : Nat) (fm' : UInt64), n = p.toNat → fm' = fm →
      ∀ (hF' : FoldN ctrl keys vals cap.toNat) (hp' : GroupAtN cap.toNat n) (hm' : IsMask fm'),
        foldMLoop f ctrl keys vals cap p fm acc hF hp hm =
          foldMLoopN f ctrl keys vals cap.toNat n fm' acc hF' hp' hm' := by
  induction p, fm, acc, hp, hm using foldMLoop.induct ctrl keys vals cap hF with
  | case1 p fm acc hp hm h ih =>
    intro n fm' hn hfm hF' hp' hm'
    subst hn hfm
    rw [foldMLoop, dite_eq_left h, foldMLoopN, dite_eq_left h]
    dsimp only
    have hi := toNat_add_lowestLane (p := p) hm (by have := hp.1; have := hF.small; omega)
    simp only [Array.uget, hi]
    congr 1
    funext acc'
    exact ih acc' _ _ rfl rfl _ _ _
  | case2 p fm acc hp hm h _ hlt ih =>
    intro n fm' hn hfm hF' hp' hm'
    subst hn hfm
    have hlt : p + 8 < cap := hlt
    have hsm := hF.small
    have hp1 := hp.1
    have h8 := toNat_add_eight (a := p) (by omega)
    have hlt' : p.toNat + 8 < cap.toNat := by rw [← h8]; exact USize.lt_iff_toNat_lt.mp hlt
    rw [foldMLoop, dite_eq_right h, foldMLoopN, dite_eq_right h]
    dsimp only
    rw [dite_eq_left hlt, dite_eq_left hlt']
    have hw : ctrlWord ctrl (p + 8) (hF.next_word hlt) =
        ctrlWordN ctrl (p.toNat + 8) (hF'.next_word hlt') :=
      (ctrlWord_eq_ctrlWordN (h' := by rw [h8]; exact hF'.next_word hlt') (by omega)).trans
        (ctrlWordN_congr h8)
    exact ih _ _ h8.symm (by rw [hw]) _ _ _
  | case3 p fm acc hp hm h _ hlt =>
    intro n fm' hn hfm hF' hp' hm'
    subst hn hfm
    have hlt : ¬p + 8 < cap := hlt
    have hsm := hF.small
    have hp1 := hp.1
    have h8 := toNat_add_eight (a := p) (by omega)
    have hlt' : ¬p.toNat + 8 < cap.toNat := by
      rw [← h8]; exact fun h => hlt (USize.lt_iff_toNat_lt.mpr h)
    rw [foldMLoop, dite_eq_right h, foldMLoopN, dite_eq_right h]
    dsimp only
    rw [dite_eq_right hlt, dite_eq_right hlt']

/-- `forInLoop` is `forInLoopN`, with the `Nat` position and mask given by equations. -/
private theorem forInLoop_eq_gen {ε : Type w} {m : Type w → Type w'} [Monad m]
    (f : α → β → ε → m (ForInStep ε)) (ctrl : ByteArray) (keys : Array α) (vals : Array β)
    (cap : USize) (hF : FoldU ctrl keys vals cap) (p : USize) (fm : UInt64) (acc : ε)
    (hp : GroupAt cap p) (hm : IsMask fm) :
    ∀ (n : Nat) (fm' : UInt64), n = p.toNat → fm' = fm →
      ∀ (hF' : FoldN ctrl keys vals cap.toNat) (hp' : GroupAtN cap.toNat n) (hm' : IsMask fm'),
        forInLoop f ctrl keys vals cap p fm acc hF hp hm =
          forInLoopN f ctrl keys vals cap.toNat n fm' acc hF' hp' hm' := by
  induction p, fm, acc, hp, hm using forInLoop.induct ctrl keys vals cap hF with
  | case1 p fm acc hp hm h ih =>
    intro n fm' hn hfm hF' hp' hm'
    subst hn hfm
    rw [forInLoop, dite_eq_left h, forInLoopN, dite_eq_left h]
    dsimp only
    have hi := toNat_add_lowestLane (p := p) hm (by have := hp.1; have := hF.small; omega)
    simp only [Array.uget, hi]
    congr 1
    funext r
    cases r with
    | done b => rfl
    | yield b => exact ih b _ _ rfl rfl _ _ _
  | case2 p fm acc hp hm h _ hlt ih =>
    intro n fm' hn hfm hF' hp' hm'
    subst hn hfm
    have hlt : p + 8 < cap := hlt
    have hsm := hF.small
    have hp1 := hp.1
    have h8 := toNat_add_eight (a := p) (by omega)
    have hlt' : p.toNat + 8 < cap.toNat := by rw [← h8]; exact USize.lt_iff_toNat_lt.mp hlt
    rw [forInLoop, dite_eq_right h, forInLoopN, dite_eq_right h]
    dsimp only
    rw [dite_eq_left hlt, dite_eq_left hlt']
    have hw : ctrlWord ctrl (p + 8) (hF.next_word hlt) =
        ctrlWordN ctrl (p.toNat + 8) (hF'.next_word hlt') :=
      (ctrlWord_eq_ctrlWordN (h' := by rw [h8]; exact hF'.next_word hlt') (by omega)).trans
        (ctrlWordN_congr h8)
    exact ih _ _ h8.symm (by rw [hw]) _ _ _
  | case3 p fm acc hp hm h _ hlt =>
    intro n fm' hn hfm hF' hp' hm'
    subst hn hfm
    have hlt : ¬p + 8 < cap := hlt
    have hsm := hF.small
    have hp1 := hp.1
    have h8 := toNat_add_eight (a := p) (by omega)
    have hlt' : ¬p.toNat + 8 < cap.toNat := by
      rw [← h8]; exact fun h => hlt (USize.lt_iff_toNat_lt.mpr h)
    rw [forInLoop, dite_eq_right h, forInLoopN, dite_eq_right h]
    dsimp only
    rw [dite_eq_right hlt, dite_eq_right hlt']

/-- `foldRevGroup` is `foldRevGroupN`. -/
private theorem foldRevGroup_eq_gen {ε : Type w} (f : ε → α → β → ε) (keys : Array α)
    (vals : Array β) (p : USize) (acc : ε) (hp : RevGroupU keys vals p) (fm : UInt64)
    (hm : IsMask fm) :
    ∀ (n : Nat) (fm' : UInt64), n = p.toNat → fm' = fm →
      ∀ (hp' : RevGroupN keys vals n) (hm' : IsMask fm'),
        foldRevGroup f keys vals p fm acc hp hm = foldRevGroupN f keys vals n fm' acc hp' hm' := by
  induction fm, hm using foldRevGroup.induct p with
  | case1 fm hm h ih =>
    intro n fm' hn hfm hp' hm'
    subst hn hfm
    rw [foldRevGroup, dite_eq_left h, foldRevGroupN, dite_eq_left h]
    dsimp only
    have hi := toNat_add_lowestLane (p := p) hm hp.small
    simp only [Array.uget, hi]
    rw [ih _ _ rfl rfl hp' _]
  | case2 fm hm h =>
    intro n fm' hn hfm hp' hm'
    subst hn hfm
    rw [foldRevGroup, dite_eq_right h, foldRevGroupN, dite_eq_right h]

/-- `foldRevLoop` is `foldRevLoopN`. -/
private theorem foldRevLoop_eq_gen {ε : Type w} (f : ε → α → β → ε) (ctrl : ByteArray)
    (keys : Array α) (vals : Array β) (p : USize) (acc : ε) (hp : RevAtU ctrl keys vals p) :
    ∀ (n : Nat), n = p.toNat → ∀ (hp' : RevAtN ctrl keys vals n),
      foldRevLoop f ctrl keys vals p acc hp = foldRevLoopN f ctrl keys vals n acc hp' := by
  induction p, acc, hp using foldRevLoop.induct f ctrl keys vals with
  | case1 p acc hp h =>
    intro n hn hp'
    subst hn
    have h' : p.toNat < 8 := by have := USize.lt_iff_toNat_lt.mp h; simpa using this
    rw [foldRevLoop, dite_eq_left h, foldRevLoopN, dite_eq_left h']
  | case2 p acc hp h p' acc' ih =>
    intro n hn hp'
    subst hn
    have h' : ¬p.toNat < 8 := by
      intro hlt; exact h (USize.lt_iff_toNat_lt.mpr (by simpa using hlt))
    have hsm := hp.small
    have hsub : (p - 8).toNat = p.toNat - 8 := by
      rw [USize.toNat_sub_of_le _ _ (USize.le_iff_toNat_le.mpr (by simp; omega))]
      simp
    rw [foldRevLoop, dite_eq_right h, foldRevLoopN, dite_eq_right h']
    dsimp only
    rw [ih (p.toNat - 8) hsub.symm (hp'.next h')]
    simp only [p', acc']
    congr 1
    have hw : ctrlWord ctrl (p - 8) (hp.word_sub h) =
        ctrlWordN ctrl (p.toNat - 8) (hp'.word_sub h') :=
      (ctrlWord_eq_ctrlWordN (h' := by rw [hsub]; exact hp'.word_sub h') (by omega)).trans
        (ctrlWordN_congr hsub)
    exact foldRevGroup_eq_gen f keys vals (p - 8) acc _ _ _ _ _ hsub.symm (by rw [hw]) _ _

/-- The control array of an unallocated or small table: its machine-word size minus 8 is
its number of slots. -/
private theorem usize_sub_eight_toNat {c : ByteArray} (h8 : 8 ≤ c.size) (hs : c.size < 2 ^ 32) :
    (c.usize - 8).toNat = c.size - 8 := by
  have hu : c.usize.toNat = c.size := by
    simp only [ByteArray.usize, Nat.toUSize_eq, USize.toNat_ofNat']
    exact Nat.mod_eq_of_lt (Nat.lt_of_lt_of_le hs USize.le_size)
  have h8' : (8 : USize).toNat ≤ c.usize.toNat := by rw [hu]; simp; omega
  rw [USize.toNat_sub_of_le _ _ (USize.le_iff_toNat_le.mpr h8'), hu]
  simp

section Helpers

variable [BEq α] [Hashable α]

/-- The entry of a slot of a table, when it is full. -/
private theorem tentryAt_full (t : Table α β) {i : Nat} (hi : i < t.slots.cap)
    (hf : t.ctrl[i]'(by simp [Slots.cap, Table.slots] at hi; omega) < 0x80) :
    t.slots.entryAt i = some ⟨t.slotKeys[i]'(t.wf.keys_lt hi), t.slotVals[i]'(t.wf.vals_lt hi)⟩ :=
  entryAt_of_full (s := t.slots) _ hf _ _

/-- On the machine-word path, the table has fewer than `2 ^ 32` control bytes. -/
private theorem ctrl_size_lt (t : Table α β) (hs : smallShift t.shift = true) :
    t.ctrl.size < 2 ^ 32 := by
  have hle := t.wf.cap_le_of_smallMask (t.wf.smallMask_of_smallShift hs)
  have h8 : 8 ≤ t.ctrl.size := t.wf.ctrl_size_ge
  simp only [Slots.cap] at hle h8
  omega

/-- A traversal from the full lanes of the first group of an allocated table visits its
entries. -/
private theorem restEntries_table (t : Table α β) {cap : Nat} (hcap : cap = t.ctrl.size - 8)
    (h8 : 8 ≤ cap) {fm : UInt64} (h : FullMask t.ctrl 0 fm) :
    restEntries ⟨t.ctrl, t.slotKeys, t.slotVals⟩ cap 0 fm = t.slots.entries := by
  rw [restEntries_init _ h8 (by dsimp only; omega) h]
  subst hcap
  rfl

/-- A table with no slots has no entries. -/
private theorem entries_of_cap_zero (t : Table α β) (h : t.ctrl.size - 8 = 0) :
    t.slots.entries = [] := by
  unfold Slots.entries
  rw [show t.slots.cap = 0 from h]
  rfl

/-- An erasure on `Nat` indices removes exactly its slot. -/
private theorem eraseAtN_entryAt (t : Table α β) (i : Nat) (hi : t.slots.IsFull i) {j : Nat}
    (hj : j < t.slots.cap) :
    (eraseAtN t i hi).slots.entryAt j = if j = i then none else t.slots.entryAt j := by
  obtain ⟨ctrl, keys, vals, size, gl, mask, shift, req, wf⟩ := t
  unfold eraseAtN
  simp only [Table.slots]
  apply entryAt_eraseN (Prod.eta _).symm hj

/-- `filterLoop` from slot `i`: the slots below `i` are untouched, the others
filtered. -/
private theorem filterLoop_entries (f : α → β → Bool) (cap i : Nat) (t : Table α β)
    (hc : cap = t.ctrl.size - 8) (hi : i ≤ cap) :
    (filterLoop f cap i t hc).slots.entries =
      (List.range cap).filterMap fun j =>
        if j < i then t.slots.entryAt j else (t.slots.entryAt j).filter fun e => f e.1 e.2 := by
  revert hi
  induction i, t, hc using filterLoop.induct f cap with
  | case1 i t hc h hf hk ih =>
    intro hi
    rw [filterLoop, dite_eq_left h, dite_eq_left hf, ite_eq_left hk, ih (by omega)]
    apply filterMap_congr_mem
    intro j hj
    by_cases hji : j < i
    · simp [hji, Nat.lt_succ_of_lt hji]
    · by_cases hji' : j = i
      · subst hji'
        rw [ite_eq_left (Nat.lt_succ_self j), ite_eq_right (Nat.lt_irrefl j),
          tentryAt_full t (by simp [Slots.cap, Table.slots]; omega) hf,
          Option.filter_some_pos (p := fun e : (_ : α) × β => f e.1 e.2) hk]
      · simp only [hji, ite_false]
        rw [ite_eq_right (by omega)]
  | case2 i t hc h hf hk ih =>
    intro hi
    rw [filterLoop, dite_eq_left h, dite_eq_left hf, ite_eq_right hk, ih (by omega)]
    apply filterMap_congr_mem
    intro j hj
    have hj' : j < t.slots.cap := by simp at hj; simp [Slots.cap, Table.slots]; omega
    rw [eraseAtN_entryAt t i _ hj']
    by_cases hji : j < i
    · simp [hji, Nat.lt_succ_of_lt hji]; omega
    · by_cases hji' : j = i
      · subst hji'
        rw [ite_eq_left (Nat.lt_succ_self j), ite_eq_right (Nat.lt_irrefl j), ite_eq_left rfl,
          tentryAt_full t (by simp [Slots.cap, Table.slots]; omega) hf,
          Option.filter_some_neg (p := fun e : (_ : α) × β => f e.1 e.2) (by simpa using hk)]
      · simp only [hji, ite_false, hji']
        rw [ite_eq_right (by omega)]
  | case3 i t hc h hf ih =>
    intro hi
    rw [filterLoop, dite_eq_left h, dite_eq_right hf, ih (by omega)]
    apply filterMap_congr_mem
    intro j hj
    by_cases hji : j < i
    · simp [hji, Nat.lt_succ_of_lt hji]
    · by_cases hji' : j = i
      · subst hji'
        rw [entryAt_of_not_full (s := t.slots) _ hf]
        simp
      · simp only [hji, ite_false]
        rw [ite_eq_right (by omega)]
  | case4 i t hc h =>
    intro hi
    rw [filterLoop, dite_eq_right h]
    have : i = cap := by omega
    subst this
    unfold Slots.entries
    simp only [Slots.cap, Table.slots] at hc ⊢
    rw [← hc]
    apply filterMap_congr_mem
    intro j hj
    simp at hj
    simp [hj]

omit [BEq α] [Hashable α] in
/-- The machine-word fold is the one on `Nat` indices. -/
private theorem foldMLoop_eq_foldMLoopN {ε : Type w} {m : Type w → Type w'} [Monad m]
    (f : ε → α → β → m ε) {ctrl : ByteArray} {keys : Array α} {vals : Array β} {cap p : USize}
    {fm : UInt64} {acc : ε} {hF : FoldU ctrl keys vals cap} {hp : GroupAt cap p}
    {hm : IsMask fm} {hF' : FoldN ctrl keys vals cap.toNat} {hp' : GroupAtN cap.toNat p.toNat} :
    foldMLoop f ctrl keys vals cap p fm acc hF hp hm =
      foldMLoopN f ctrl keys vals cap.toNat p.toNat fm acc hF' hp' hm :=
  foldMLoop_eq_gen f ctrl keys vals cap hF p fm acc hp hm _ _ rfl rfl hF' hp' hm

end Helpers

end Swiss

namespace Table

open Swiss

variable {α : Type u} {β : Type v} {γ : Type w} {_ : BEq α} {_ : Hashable α}

theorem toListModel_filter (t : Table α β) (f : α → β → Bool) :
    (t.filter f).toListModel.Perm (t.toListModel.filter fun p => f p.1 p.2) := by
  rw [filter_def, toListModel_def, toListModel_def, filterImpl,
    filterLoop_entries f _ 0 t rfl (Nat.zero_le _)]
  simp only [Nat.not_lt_zero, ite_false]
  unfold Slots.entries
  rw [List.filter_filterMap]
  exact List.Perm.refl _

theorem toListModel_filterMap (t : Table α β) (f : α → β → Option γ) :
    (t.filterMap f).toListModel.Perm
      (t.toListModel.filterMap fun p => (f p.1 p.2).map (⟨p.1, ·⟩)) := by
  rw [filterMap_def, toListModel_def, toListModel_def]
  obtain ⟨ctrl, keys, vals, size, gl, mask, shift, req, wf⟩ := t
  unfold filterMapImpl
  dsimp only
  split
  · rename_i hs
    rw [emptyImpl_entries]
    simp only [Table.slots]
    apply List.Perm.of_eq
    symm
    rw [List.filterMap_eq_nil_iff]
    intro e he
    obtain ⟨j, hj, hje⟩ := mem_entries.mp he
    obtain ⟨-, hf, hk, hv⟩ := entryAt_eq_some hje
    dsimp only at hj hf hk hv ⊢
    have := firstSome_none hs j (Nat.zero_le _) (by simpa [Slots.cap] using hj) hf _ _ hk hv
    simp [this]
  · rename_i i0 c0 hs
    apply List.Perm.of_eq
    simp only [Table.slots]
    apply filterMap_entries_raw wf hs rfl

theorem toListModel_map (t : Table α β) (f : α → β → γ) :
    (t.map f).toListModel.Perm (t.toListModel.map fun p => ⟨p.1, f p.1 p.2⟩) := by
  rw [map_def, toListModel_def, toListModel_def]
  obtain ⟨ctrl, keys, vals, size, gl, mask, shift, req, wf⟩ := t
  unfold mapImpl
  dsimp only
  split
  · rename_i hs
    rw [emptyImpl_entries]
    simp only [Table.slots]
    have hn : Slots.entries ⟨ctrl, keys, vals⟩ = [] := by
      apply entries_eq_nil_of
      intro j hj hc hf
      dsimp only at hj hc hf
      exact firstFull_none hs j (Nat.zero_le _) (by simpa [Slots.cap] using hj)
        (by rw [getElem!_eq_getElem hc]; exact hf)
    rw [hn]
    exact List.Perm.refl _
  · rename_i i0 hs
    apply List.Perm.of_eq
    simp only [Table.slots]
    unfold Slots.entries
    rw [List.map_filterMap]
    apply filterMap_congr_mem
    intro j hj
    rw [List.mem_range] at hj
    have hjc : j < ctrl.size := by simp only [Slots.cap] at hj; omega
    have hjk : j < keys.size := wf.keys_lt hj
    have hjv : j < vals.size := wf.vals_lt hj
    by_cases hf : ctrl[j] < 0x80
    · rw [entryAt_of_full hjc hf hjk (by simp only [Array.size_mapFinIdx]; exact hjv),
        entryAt_of_full hjc hf hjk hjv]
      simp only [Option.map_some, Array.getElem_mapFinIdx]
      by_cases hji : j = i0
      · subst hji; simp
      · simp only [Slots.cap] at hj
        simp [hj, hji, hf]
    · rw [entryAt_of_not_full hjc hf, entryAt_of_not_full hjc hf]
      rfl

theorem foldM_eq_foldlM_toListModel {ε : Type w} {m : Type w → Type w'} [Monad m]
    [LawfulMonad m] (t : Table α β) (f : ε → α → β → m ε) (init : ε) :
    t.foldM f init = t.toListModel.foldlM (fun d e => f d e.1 e.2) init := by
  rw [foldM_def, toListModel_def]
  have h8 : 8 ≤ t.ctrl.size := t.wf.ctrl_size_ge
  unfold foldMImpl
  split
  · rename_i hs
    have hu := usize_sub_eight_toNat h8 (ctrl_size_lt t hs)
    dsimp only
    split
    · rename_i hc
      have hfm := fullMask_ctrlWord t.ctrl 0 t.wf.word0 (by simp; have := USize.le_size; omega)
      have hg : GroupAtN (t.ctrl.usize - 8).toNat (0 : USize).toNat := t.wf.group0 hs hc
      rw [foldMLoop_eq_foldMLoopN (hF' := (t.wf.foldU hs).toN) (hp' := hg)]
      dsimp only
      rw [foldMLoopN_spec _ _ _ _ _ _ _ _ _ _ _ hfm.sub]
      rw [USize.toNat_zero] at hfm hg ⊢
      rw [restEntries_table t hu (by have := hg.1; omega) hfm]
    · rename_i hc
      have h0 : t.ctrl.size - 8 = 0 := by
        rw [← hu]
        have : ¬(0 : USize).toNat < (t.ctrl.usize - 8).toNat :=
          fun h => hc (USize.lt_iff_toNat_lt.mpr h)
        rw [USize.toNat_zero] at this
        omega
      rw [entries_of_cap_zero t h0]
      rfl
  · rename_i hs
    have hg : GroupAtN (t.ctrl.size - 8) 0 := t.wf.group0N hs
    rw [foldMLoopN_spec _ _ _ _ _ _ _ _ _ _ _ (fullMask_ctrlWordN t.ctrl 0 _).sub,
      restEntries_table t rfl (by have := hg.1; omega) (fullMask_ctrlWordN t.ctrl 0 _)]

theorem foldRev_eq_foldr_toListModel {ε : Type w} (t : Table α β) (f : ε → α → β → ε)
    (init : ε) : t.foldRev f init = t.toListModel.foldr (fun e d => f d e.1 e.2) init := by
  rw [foldRev_def, toListModel_def]
  have h8 : 8 ≤ t.ctrl.size := t.wf.ctrl_size_ge
  unfold foldRevImpl
  split
  · rename_i hs
    have hu := usize_sub_eight_toNat h8 (ctrl_size_lt t hs)
    rw [foldRevLoop_eq_gen f _ _ _ _ init _ _ hu.symm t.wf.revN,
      foldRevLoopN_spec _ _ _ _ _ _ _ t.wf.foldN.eight]
    rfl
  · rw [foldRevLoopN_spec _ _ _ _ _ _ _ t.wf.foldN.eight]
    rfl

theorem forIn_eq_forIn_toListModel {ε : Type w} {m : Type w → Type w'} [Monad m]
    [LawfulMonad m] (t : Table α β) (f : α → β → ε → m (ForInStep ε)) (init : ε) :
    t.forIn f init = ForIn.forIn t.toListModel init (fun e d => f e.1 e.2 d) := by
  rw [forIn_def, toListModel_def]
  have h8 : 8 ≤ t.ctrl.size := t.wf.ctrl_size_ge
  unfold forInImpl
  split
  · rename_i hs
    have hu := usize_sub_eight_toNat h8 (ctrl_size_lt t hs)
    dsimp only
    split
    · rename_i hc
      have hfm := fullMask_ctrlWord t.ctrl 0 t.wf.word0 (by simp; have := USize.le_size; omega)
      have hg : GroupAtN (t.ctrl.usize - 8).toNat (0 : USize).toNat := t.wf.group0 hs hc
      rw [forInLoop_eq_gen f _ _ _ _ (t.wf.foldU hs) _ _ _ _ _ _ _ rfl rfl (t.wf.foldU hs).toN hg
        (isMask_matchFull _)]
      dsimp only
      rw [forInLoopN_spec _ _ _ _ _ _ _ _ _ _ _ hfm.sub]
      rw [USize.toNat_zero] at hfm hg ⊢
      rw [restEntries_table t hu (by have := hg.1; omega) hfm]
    · rename_i hc
      have h0 : t.ctrl.size - 8 = 0 := by
        rw [← hu]
        have : ¬(0 : USize).toNat < (t.ctrl.usize - 8).toNat :=
          fun h => hc (USize.lt_iff_toNat_lt.mpr h)
        rw [USize.toNat_zero] at this
        omega
      rw [entries_of_cap_zero t h0]
      rfl
  · rename_i hs
    have hg : GroupAtN (t.ctrl.size - 8) 0 := t.wf.group0N hs
    rw [forInLoopN_spec _ _ _ _ _ _ _ _ _ _ _ (fullMask_ctrlWordN t.ctrl 0 _).sub,
      restEntries_table t rfl (by have := hg.1; omega) (fullMask_ctrlWordN t.ctrl 0 _)]

end Table

end SwissTable.Core
