module

public import SwissTable.Core.Swiss.Build
public import SwissTable.Core.Swiss.Proofs.Probe
public import Std.Data.Internal.List.Associative

/-!
# Swiss core proofs, part 4: single-slot writes, and the rebuilt table

A proof file of the Swiss core (`SwissTable/Core/Swiss/Table.lean`, "Proof structure").

* **The invariant after each write of `Table.lean`** (stated on the code's terms, machine-word and
  `Nat` forms): a value (`WF.replaceVals`), the key of a hit (`WF.keyN`, `WF.keyU`: `==` keys have
  the same hash and tag under lawfulness, and `TagInv` holds because the hit's byte is the tag of
  `a`), a new key at the slot of a `NewSlot` (`WF.newU_empty`, `WF.newU_del`, `WF.newN_empty`,
  `WF.newN_del`, `WF.freshU`, `WF.freshN`: `TagInv` by the tag written, `ProbeInv` by
  `FreeSlot.reach`, `Distinct` by `NewSlot.absent`, the counts by the EMPTY/DELETED accounting),
  and an erasure (`WF.eraseU`, `WF.eraseN`: writing EMPTY keeps `ProbeInv` because every group
  containing the slot already has an EMPTY slot, `exists_empty_of_needsTombstone_eq_false`;
  DELETED keeps it trivially; tombstone rule B only lowers `growthLeft`).
* **The entries after each write** (`Nat` forms; the machine-word forms reduce to them through
  `setCtrl_eq_setCtrlN`, `ctrlWord_eq_ctrlWordN` and `Array.uset_eq_set`): pointwise
  (`entryAt_kvN`, `entryAt_eraseN`), and as the list operations of the contract
  (`entries_newN_perm`, `WF.entries_kvN_replace`, `WF.entries_eraseN_eraseKey`).
* **The rebuilt table** (`Table.lean`'s `reserveInsert`, `Proofs/Update.lean`): its entries
  (`rebuild_perm`, `emptyTable_entries`, `reserveTable_perm`) and its room for the new key
  (`freshPre_reserve`).

The invariant is proved once per kind of write, on `Nat` indices: `WF.newGen` (a key and its tag
at a free slot) and `WF.eraseGen` (EMPTY or DELETED at a full slot, given the erase rule's window
fact); the stated forms instantiate them. `numDeleted` is a `countP` over the slots, so a write at
slot `i` changes it by the change at `i` only (`numDeleted_write`), and a probe still reaches a slot
after a write that leaves every group without an EMPTY slot without one (`reach_transfer`). The
entries after a write are a `filterMap` over the slots that changes at slot `i` only
(`filterMap_perm_cons`, `filterMap_replaceEntry`, `filterMap_eraseKey`).
-/

@[expose] public section

universe u v w

namespace SwissTable.Core.Swiss

open Std.Internal.List

variable {α : Type u} {β : Type v} {γ : Type w}

/-! ## Helpers: lists -/

/-- Two `filterMap`s that agree on `l` off `i`, where the first keeps `x` at `i` and the second
drops `i`, differ by `x` on a list that holds `i` once. -/
private theorem filterMap_perm_cons {γ δ : Type _} {f g : γ → Option δ} {i : γ} {x : δ}
    (hf : f i = some x) (hg : g i = none) :
    ∀ {l : List γ}, l.Nodup → i ∈ l → (∀ j ∈ l, j ≠ i → f j = g j) →
      (l.filterMap f).Perm (x :: l.filterMap g)
  | [], _, hm, _ => absurd hm List.not_mem_nil
  | j :: l, hnd, hm, hoff => by
    rw [List.nodup_cons] at hnd
    by_cases hji : j = i
    · subst hji
      rw [List.filterMap_cons, List.filterMap_cons, hf, hg,
        filterMap_congr_mem fun y hy => hoff y (List.mem_cons_of_mem _ hy)
          (fun h => hnd.1 (h ▸ hy))]
    · have ih := filterMap_perm_cons hf hg hnd.2
        ((List.mem_cons.mp hm).resolve_left (Ne.symm hji))
        (fun y hy hyi => hoff y (List.mem_cons_of_mem _ hy) hyi)
      rw [List.filterMap_cons, List.filterMap_cons, hoff j List.mem_cons_self hji]
      cases g j with
      | none => exact ih
      | some y => exact (ih.cons y).trans (List.Perm.swap x y _)

/-- `filterMap`s that differ at slot `i` only, where `i` holds the only key `== a`: replacing that
entry is `replaceEntry`. -/
private theorem filterMap_replaceEntry [BEq α] {f g : Nat → Option ((_ : α) × β)} {i : Nat}
    {a : α} {b : β} {e₀ : (_ : α) × β} (hf : f i = some ⟨a, b⟩) (hg : g i = some e₀)
    (he₀ : (e₀.1 == a) = true) :
    ∀ {l : List Nat}, l.Nodup → (∀ j ∈ l, j ≠ i → f j = g j) →
      (∀ j ∈ l, j ≠ i → ∀ e, g j = some e → (e.1 == a) = false) →
      l.filterMap f = replaceEntry a b (l.filterMap g)
  | [], _, _, _ => by rw [List.filterMap_nil, List.filterMap_nil, replaceEntry_nil]
  | j :: l, hnd, hoff, hne => by
    rw [List.nodup_cons] at hnd
    by_cases hji : j = i
    · subst hji
      obtain ⟨k₀, v₀⟩ := e₀
      rw [List.filterMap_cons, List.filterMap_cons, hf, hg, replaceEntry_cons_of_true he₀,
        filterMap_congr_mem fun y hy => hoff y (List.mem_cons_of_mem _ hy)
          (fun h => hnd.1 (h ▸ hy))]
    · have ih := filterMap_replaceEntry hf hg he₀ hnd.2
        (fun y hy hyi => hoff y (List.mem_cons_of_mem _ hy) hyi)
        (fun y hy hyi => hne y (List.mem_cons_of_mem _ hy) hyi)
      rw [List.filterMap_cons, List.filterMap_cons, hoff j List.mem_cons_self hji]
      cases hgj : g j with
      | none => exact ih
      | some y =>
        obtain ⟨k, v⟩ := y
        simp only
        rw [replaceEntry_cons_of_false (hne j List.mem_cons_self hji _ hgj), ih]

/-- `filterMap`s that differ at slot `i` only, where `i` holds the only key `== a` and the first
drops it: `eraseKey`. -/
private theorem filterMap_eraseKey [BEq α] {f g : Nat → Option ((_ : α) × β)} {i : Nat}
    {a : α} {e₀ : (_ : α) × β} (hf : f i = none) (hg : g i = some e₀)
    (he₀ : (e₀.1 == a) = true) :
    ∀ {l : List Nat}, l.Nodup → (∀ j ∈ l, j ≠ i → f j = g j) →
      (∀ j ∈ l, j ≠ i → ∀ e, g j = some e → (e.1 == a) = false) →
      l.filterMap f = eraseKey a (l.filterMap g)
  | [], _, _, _ => by rw [List.filterMap_nil, List.filterMap_nil, eraseKey_nil]
  | j :: l, hnd, hoff, hne => by
    rw [List.nodup_cons] at hnd
    by_cases hji : j = i
    · subst hji
      obtain ⟨k₀, v₀⟩ := e₀
      rw [List.filterMap_cons, List.filterMap_cons, hf, hg, eraseKey_cons_of_beq he₀,
        filterMap_congr_mem fun y hy => hoff y (List.mem_cons_of_mem _ hy)
          (fun h => hnd.1 (h ▸ hy))]
    · have ih := filterMap_eraseKey hf hg he₀ hnd.2
        (fun y hy hyi => hoff y (List.mem_cons_of_mem _ hy) hyi)
        (fun y hy hyi => hne y (List.mem_cons_of_mem _ hy) hyi)
      rw [List.filterMap_cons, List.filterMap_cons, hoff j List.mem_cons_self hji]
      cases hgj : g j with
      | none => exact ih
      | some y =>
        obtain ⟨k, v⟩ := y
        simp only
        rw [eraseKey_cons_of_false (hne j List.mem_cons_self hji _ hgj), ih]

/-- A count over the slots after a change at slot `i` only. -/
private theorem countP_range_update {i : Nat} {p p' : Nat → Bool} :
    ∀ {n : Nat}, i < n → (∀ j < n, j ≠ i → p' j = p j) →
      (List.range n).countP p' + (if p i then 1 else 0) =
        (List.range n).countP p + (if p' i then 1 else 0)
  | 0, hi, _ => absurd hi (Nat.not_lt_zero _)
  | n + 1, hi, h => by
    rw [List.range_succ, List.countP_append, List.countP_append, List.countP_singleton,
      List.countP_singleton]
    by_cases hin : i = n
    · subst hin
      rw [List.countP_congr (q := p) (fun j hj => by
        rw [h j (by have := List.mem_range.mp hj; omega)
          (by have := List.mem_range.mp hj; omega)])]
      omega
    · have ih := countP_range_update (n := n) (by omega) (fun j hj hji => h j (by omega) hji)
      rw [h n (by omega) (Ne.symm hin)]
      omega

/-! ## Helpers: control bytes and cells -/

private theorem ne_EMPTY_of_lt {b : UInt8} (h : b < 0x80) : b ≠ EMPTY := by
  rintro rfl; exact EMPTY_not_lt h

private theorem ne_DELETED_of_lt {b : UInt8} (h : b < 0x80) : b ≠ DELETED := by
  rintro rfl; exact DELETED_not_lt h

private theorem getElem_bset (c : ByteArray) (i : Nat) (b : UInt8) (h : i < c.size) (j : Nat)
    (hj : j < c.size) :
    (c.set i b h)[j]'(by rw [size_set]; exact hj) = if i = j then b else c[j] := by
  cases c; simp [ByteArray.set, ByteArray.getElem_eq_getElem_data, Array.getElem_set]

/-- The mirror write of `setCtrlN` lands on no slot but `i`. -/
private theorem mirror_ne {cap i j : Nat} (hic : i < cap) (hj : j < cap) (hji : j ≠ i) :
    (i + cap - 8) % cap + 8 ≠ j := by
  intro h
  by_cases h8 : 8 ≤ i
  · have : (i + cap - 8) % cap = i - 8 := by
      rw [show i + cap - 8 = (i - 8) + cap by omega, Nat.add_mod_right,
        Nat.mod_eq_of_lt (by omega)]
    omega
  · by_cases h8' : 8 ≤ i + cap
    · have : (i + cap - 8) % cap = i + cap - 8 := Nat.mod_eq_of_lt (by omega)
      omega
    · have : i + cap - 8 = 0 := by omega
      rw [this, Nat.zero_mod] at h
      omega

private theorem getElem_setCtrlN_lt {c : ByteArray} {cap i : Nat} {b : UInt8} {hi : i < c.size}
    {hm : cap + 8 ≤ c.size} {hc : 0 < cap} (hic : i < cap) {j : Nat} (hj : j < cap) :
    (setCtrlN c cap i b hi hm hc)[j]'(by rw [size_setCtrlN]; omega) =
      if j = i then b else c[j]'(by omega) := by
  have hjs : j < c.size := by omega
  unfold setCtrlN
  rw [getElem_bset _ _ _ _ _ (by rw [size_set]; exact hjs), getElem_bset _ _ _ _ _ hjs]
  by_cases hji : j = i
  · subst hji; simp
  · rw [ite_eq_right (mirror_ne hic hj hji), ite_eq_right (Ne.symm hji), ite_eq_right hji]

private theorem getElem!_setCtrlN {c : ByteArray} {cap i : Nat} {b : UInt8} {hi : i < c.size}
    {hm : cap + 8 ≤ c.size} {hc : 0 < cap} (hic : i < cap) {j : Nat} (hj : j < cap) :
    (setCtrlN c cap i b hi hm hc)[j]! = if j = i then b else c[j]! := by
  have hjs : j < c.size := by omega
  rw [getElem!_pos (setCtrlN c cap i b hi hm hc) j (by rw [size_setCtrlN]; exact hjs),
    getElem!_pos c j hjs, getElem_setCtrlN_lt hic hj]

private theorem getElem?_setCtrlN {c : ByteArray} {cap i : Nat} {b : UInt8} {hi : i < c.size}
    {hm : cap + 8 ≤ c.size} {hc : 0 < cap} (hic : i < cap) {j : Nat} (hj : j < cap) :
    (setCtrlN c cap i b hi hm hc)[j]? = if j = i then some b else c[j]? := by
  have hjs : j < c.size := by omega
  rw [getElem?_pos (setCtrlN c cap i b hi hm hc) j (by rw [size_setCtrlN]; exact hjs),
    getElem?_pos c j hjs, getElem_setCtrlN_lt hic hj]
  split <;> rfl

private theorem getElem?_aset {xs : Array γ} {i : Nat} {v : γ} {h : i < xs.size} (j : Nat) :
    (xs.set i v h)[j]? = if j = i then some v else xs[j]? := by
  rw [Array.getElem?_set]
  by_cases hji : j = i
  · subst hji; simp
  · rw [ite_eq_right (Ne.symm hji), ite_eq_right hji]

/-! ## Helpers: entries after a write -/

/-- The entry of slot `j` after a write of byte `t`, key `a` and value `b` at slot `i`. -/
private theorem entryAt_write {ctrl : ByteArray} {keys : Array α} {vals : Array β} {i : Nat}
    (hi : i < ctrl.size - 8) (t : UInt8) (a : α) (b : β) {h1 : i < ctrl.size}
    {h2 : ctrl.size - 8 + 8 ≤ ctrl.size} {h3 : 0 < ctrl.size - 8} {h4 : i < keys.size}
    {h5 : i < vals.size} {j : Nat} (hj : j < ctrl.size - 8) :
    (Slots.mk (setCtrlN ctrl (ctrl.size - 8) i t h1 h2 h3) (keys.set i a h4)
      (vals.set i b h5)).entryAt j =
      if j = i then (if t < 0x80 then some ⟨a, b⟩ else none)
      else Slots.entryAt ⟨ctrl, keys, vals⟩ j := by
  unfold Slots.entryAt
  simp only
  rw [getElem?_setCtrlN hi hj, getElem?_aset, getElem?_aset]
  by_cases hji : j = i
  · subst hji
    simp only [ite_true]
    split <;> rfl
  · simp only [hji, ite_false]

/-- The cap after a write. -/
private theorem cap_write {ctrl : ByteArray} {keys : Array α} {vals : Array β} {i : Nat}
    {t : UInt8} {a : α} {b : β} {h1 : i < ctrl.size}
    {h2 : ctrl.size - 8 + 8 ≤ ctrl.size} {h3 : 0 < ctrl.size - 8} {h4 : i < keys.size}
    {h5 : i < vals.size} :
    (Slots.mk (setCtrlN ctrl (ctrl.size - 8) i t h1 h2 h3) (keys.set i a h4)
      (vals.set i b h5)).cap = ctrl.size - 8 := by
  unfold Slots.cap; simp only [size_setCtrlN]

/-- A new entry at a slot without one: the entries gain it, up to order. -/
private theorem entries_write_perm {ctrl : ByteArray} {keys : Array α} {vals : Array β} {i : Nat}
    (hi : i < ctrl.size - 8) (hfree : ¬ctrl[i]! < 0x80) {t : UInt8} (ht : t < 0x80) (a : α)
    (b : β) {h1 : i < ctrl.size} {h2 : ctrl.size - 8 + 8 ≤ ctrl.size} {h3 : 0 < ctrl.size - 8}
    {h4 : i < keys.size} {h5 : i < vals.size} :
    (Slots.mk (setCtrlN ctrl (ctrl.size - 8) i t h1 h2 h3) (keys.set i a h4)
      (vals.set i b h5)).entries.Perm (⟨a, b⟩ :: Slots.entries ⟨ctrl, keys, vals⟩) := by
  unfold Slots.entries
  rw [cap_write]
  refine filterMap_perm_cons (i := i) ?_ (entryAt_eq_none (s := ⟨ctrl, keys, vals⟩) hfree)
    List.nodup_range (List.mem_range.mpr hi) (fun j hj hji => ?_)
  · rw [entryAt_write hi t a b hi, ite_eq_left rfl, ite_eq_left ht]
  · rw [entryAt_write hi t a b (List.mem_range.mp hj), ite_eq_right hji]

/-- An erasure (EMPTY or DELETED written over a full slot): the entries lose it. -/
private theorem entries_erase_perm {ctrl : ByteArray} {keys : Array α} {vals : Array β} {i : Nat}
    (hfull : Slots.IsFull ⟨ctrl, keys, vals⟩ i) {t : UInt8} (ht : ¬t < 0x80) (a : α) (b : β)
    {h1 : i < ctrl.size} {h2 : ctrl.size - 8 + 8 ≤ ctrl.size} {h3 : 0 < ctrl.size - 8}
    {h4 : i < keys.size} {h5 : i < vals.size} :
    (Slots.entries ⟨ctrl, keys, vals⟩).Perm (⟨keys[i], vals[i]⟩ ::
      (Slots.mk (setCtrlN ctrl (ctrl.size - 8) i t h1 h2 h3) (keys.set i a h4)
        (vals.set i b h5)).entries) := by
  have hi : i < ctrl.size - 8 := hfull.1
  unfold Slots.entries
  rw [cap_write]
  refine filterMap_perm_cons (i := i) (entryAt_of_isFull hfull h4 h5) ?_
    List.nodup_range (List.mem_range.mpr hi) (fun j hj hji => ?_)
  · rw [entryAt_write hi t a b hi, ite_eq_left rfl, ite_eq_right ht]
  · rw [entryAt_write hi t a b (List.mem_range.mp hj), ite_eq_right hji]

/-- `eraseCtrlN` writes the byte of the erase rule at slot `i`. -/
private theorem eraseCtrlN_spec {ctrl : ByteArray} {sz g cap i : Nat} {hic : i < cap}
    {hc : cap + 8 ≤ ctrl.size} {c' : ByteArray} {gl' : Nat}
    (he : eraseCtrlN ctrl sz g cap i hic hc = (c', gl')) :
    ∃ del : Bool,
      del = needsTombstone (matchEmpty (ctrlWordN ctrl i (by omega)))
        (matchEmpty (ctrlWordN ctrl ((i + cap - 8) % cap)
          (by have := Nat.mod_lt (i + cap - 8) (show 0 < cap by omega); omega))) ∧
      c' = setCtrlN ctrl cap i (if del then DELETED else EMPTY) (by omega) hc (by omega) ∧
      gl' = if del then (if sz - 1 + g + capacityOf cap / 4 < capacityOf cap then 0 else g)
        else g + 1 := by
  unfold eraseCtrlN at he
  simp only [Prod.mk.injEq] at he
  exact ⟨_, rfl, he.1.symm, he.2.symm⟩

/-! ## Helpers: the invariant after a write -/

section WriteGen

variable {ctrl : ByteArray} {keys : Array α} {vals : Array β} {i : Nat} {t : UInt8} {a : α}
  {b : β} {h1 : i < ctrl.size} {h2 : ctrl.size - 8 + 8 ≤ ctrl.size} {h3 : 0 < ctrl.size - 8}
  {h4 : i < keys.size} {h5 : i < vals.size}

/-- A write at a slot keeps the shape of an allocated table. -/
private theorem alloc_write {mask : USize} {shift : UInt64} {lg : Nat}
    (hal : Alloc (⟨ctrl, keys, vals⟩ : Slots α β) mask shift lg) (hi : i < ctrl.size - 8) :
    Alloc (Slots.mk (setCtrlN ctrl (ctrl.size - 8) i t h1 h2 h3) (keys.set i a h4)
      (vals.set i b h5)) mask shift lg := by
  have hm : Mirrored ctrl (2 ^ lg) := hal.mirrored
  have he : ctrl.size - 8 = 2 ^ lg := by have := hm.size_eq; omega
  have hm' : Mirrored ctrl (ctrl.size - 8) := he ▸ hm
  have key : ∀ c', Mirrored c' (ctrl.size - 8) → Mirrored c' (2 ^ lg) := fun c' h => he ▸ h
  exact ⟨hal.three_le, key _ (mirrored_setCtrlN hm' hi t (hi := h1) (hm := h2) (hc := h3)),
    by rw [Array.size_set]; exact hal.keys_size, by rw [Array.size_set]; exact hal.vals_size,
    hal.mask_eq, hal.shift_eq⟩

/-- A slot other than the one written is full exactly when it was. -/
private theorem isFull_write_ne (hi : i < ctrl.size - 8) {j : Nat} (hji : j ≠ i) :
    (Slots.mk (setCtrlN ctrl (ctrl.size - 8) i t h1 h2 h3) (keys.set i a h4)
      (vals.set i b h5)).IsFull j ↔ Slots.IsFull ⟨ctrl, keys, vals⟩ j := by
  unfold Slots.IsFull
  rw [cap_write]
  simp only
  constructor
  · rintro ⟨hj, hf⟩
    rw [getElem!_setCtrlN hi hj, ite_eq_right hji] at hf
    exact ⟨hj, hf⟩
  · rintro ⟨hj, hf⟩
    refine ⟨hj, ?_⟩
    rw [getElem!_setCtrlN hi hj, ite_eq_right hji]
    exact hf

/-- The tombstones after a write change by the change at slot `i`. -/
private theorem numDeleted_write (hi : i < ctrl.size - 8) :
    (Slots.mk (setCtrlN ctrl (ctrl.size - 8) i t h1 h2 h3) (keys.set i a h4)
      (vals.set i b h5)).numDeleted + (if ctrl[i]! == DELETED then 1 else 0) =
      Slots.numDeleted ⟨ctrl, keys, vals⟩ + (if t == DELETED then 1 else 0) := by
  unfold Slots.numDeleted
  rw [cap_write]
  have H := countP_range_update (n := ctrl.size - 8) (i := i)
    (p := fun j => ctrl[j]! == DELETED)
    (p' := fun j => (setCtrlN ctrl (ctrl.size - 8) i t h1 h2 h3)[j]! == DELETED) hi
    (fun j hj hji => by simp only [getElem!_setCtrlN hi hj, ite_eq_right hji])
  rw [getElem!_setCtrlN hi hi, ite_eq_left rfl] at H
  exact H

end WriteGen

/-- A probe reach survives a change of the control bytes that keeps every group without an EMPTY
slot without one. -/
private theorem reach_transfer {s : Slots α β} {s' : Slots α γ} (hcap : s'.cap = s.cap)
    (H : ∀ p : Nat, (∀ l < 8, s.ctrl[(p + l) % s.cap]! ≠ EMPTY) →
      ∀ l < 8, s'.ctrl[(p + l) % s.cap]! ≠ EMPTY)
    {p₀ j : Nat} (h : s.Reach p₀ j) : s'.Reach p₀ j := by
  obtain ⟨k, hk, l, hl, heq, hall⟩ := h
  unfold Slots.Reach
  rw [hcap]
  exact ⟨k, hk, l, hl, heq, fun k' hk' => H _ (hall k' hk')⟩

/-- A change of the control bytes that writes EMPTY nowhere keeps every group without an EMPTY
slot without one. -/
private theorem groups_of_pointwise {s : Slots α β} {s' : Slots α γ} (hc : 0 < s.cap)
    (h : ∀ x < s.cap, s.ctrl[x]! ≠ EMPTY → s'.ctrl[x]! ≠ EMPTY) :
    ∀ p : Nat, (∀ l < 8, s.ctrl[(p + l) % s.cap]! ≠ EMPTY) →
      ∀ l < 8, s'.ctrl[(p + l) % s.cap]! ≠ EMPTY :=
  fun _ hp l hl => h _ (Nat.mod_lt _ hc) (hp l hl)

/-- Two tables with the same slots and entries at the same slots have equally many entries. -/
private theorem length_entries_congr {s : Slots α β} {s' : Slots α γ} (hcap : s'.cap = s.cap)
    (h : ∀ j < s.cap, (s'.entryAt j).isSome = (s.entryAt j).isSome) :
    s'.entries.length = s.entries.length := by
  unfold Slots.entries
  rw [hcap, List.length_filterMap_eq_countP, List.length_filterMap_eq_countP]
  exact List.countP_congr (fun j hj => by rw [h j (List.mem_range.mp hj)])

section WFGen

variable [BEq α] [Hashable α] {ctrl : ByteArray} {keys : Array α} {vals : Array β}
  {size gl : Nat} {mask : USize} {shift : UInt64}

/-- **A new key at a `NewSlot`**, on `Nat` indices: `gl'` is `gl` less one when the slot was
EMPTY. -/
private theorem WF.newGen (wf : WF ⟨ctrl, keys, vals⟩ size gl mask shift) {a : α} {b : β}
    {q : UInt64} {i : Nat} (h : NewSlot ⟨ctrl, keys, vals⟩ shift a q i) {gl' : Nat}
    (hgl : gl' + (if ctrl[i]! = EMPTY then 1 else 0) = gl) {h1 : i < ctrl.size}
    {h2 : ctrl.size - 8 + 8 ≤ ctrl.size} {h3 : 0 < ctrl.size - 8} {h4 : i < keys.size}
    {h5 : i < vals.size} :
    WF ⟨setCtrlN ctrl (ctrl.size - 8) i (tagOf q) h1 h2 h3, keys.set i a h4, vals.set i b h5⟩
      (size + 1) gl' mask shift := by
  have hfs : Slots.FreeSlot ⟨ctrl, keys, vals⟩ (homeN q (ctrl.size - 8)) i := by
    rcases h.slot with hf | ⟨hc0, -⟩
    · exact hf
    · exact absurd hc0 (Nat.ne_of_gt h3)
  have hi : i < ctrl.size - 8 := hfs.lt
  have ht := tagOf_lt q
  have hfree : ctrl[i]! = EMPTY ∨ ctrl[i]! = DELETED := hfs.free
  have hnf : ¬ctrl[i]! < 0x80 := by
    rcases hfree with h | h <;> rw [h]
    · exact EMPTY_not_lt
    · exact DELETED_not_lt
  have hb : ∀ j < ctrl.size - 8, (setCtrlN ctrl (ctrl.size - 8) i (tagOf q) h1 h2 h3)[j]! =
      if j = i then tagOf q else ctrl[j]! := fun j hj => getElem!_setCtrlN hi hj
  obtain ⟨lg, hal⟩ := wf.alloc h3
  refine ⟨Or.inr ⟨lg, alloc_write hal hi⟩, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · -- control bytes
    intro j hj
    rw [cap_write] at hj
    simp only
    rw [hb j hj]
    split
    · exact isCtrl_of_lt ht
    · exact wf.ctrl j hj
  · -- tags
    intro j k hj hk
    simp only at hk ⊢
    rw [getElem?_aset] at hk
    have hjc : j < ctrl.size - 8 := by have := hj.1; rwa [cap_write] at this
    rw [hb j hjc]
    by_cases hji : j = i
    · rw [ite_eq_left hji] at hk ⊢
      obtain rfl := Option.some.inj hk
      rw [h.hash_eq]
    · rw [ite_eq_right hji] at hk ⊢
      exact wf.tag j k ((isFull_write_ne hi hji).mp hj) hk
  · -- size
    rw [(entries_write_perm hi hnf ht a b).length_eq, List.length_cons, ← wf.size_eq]
  · -- room
    have hnd := numDeleted_write (t := tagOf q) (a := a) (b := b) (h1 := h1) (h2 := h2) (h3 := h3)
      (h4 := h4) (h5 := h5) hi
    have hroom : gl + size + Slots.numDeleted ⟨ctrl, keys, vals⟩ ≤ capacityOf (ctrl.size - 8) :=
      wf.room
    rw [cap_write]
    have htd : (tagOf q == DELETED) = false := beq_false_of_ne (ne_DELETED_of_lt ht)
    rw [htd] at hnd
    have hed : (EMPTY == DELETED) = false := beq_false_of_ne (Ne.symm DELETED_ne_EMPTY)
    rcases hfree with he | he
    · rw [he, hed] at hnd
      rw [he] at hgl
      simp only [ite_true] at hgl
      simp only [Bool.false_eq_true, ite_false] at hnd
      omega
    · rw [he, beq_self_eq_true] at hnd
      rw [he, ite_eq_right DELETED_ne_EMPTY] at hgl
      simp only [Bool.false_eq_true, ite_true, ite_false] at hnd
      omega
  · -- distinct keys
    intro _ _ j j' k k' hj hj' hk hk' hkk
    simp only at hk hk'
    rw [getElem?_aset] at hk hk'
    by_cases hji : j = i <;> by_cases hji' : j' = i
    · rw [hji, hji']
    · rw [ite_eq_left hji] at hk
      obtain rfl := Option.some.inj hk
      rw [ite_eq_right hji'] at hk'
      have := h.absent j' k' ((isFull_write_ne hi hji').mp hj') hk'
      rw [BEq.comm, this] at hkk
      exact absurd hkk Bool.false_ne_true
    · rw [ite_eq_left hji'] at hk'
      obtain rfl := Option.some.inj hk'
      rw [ite_eq_right hji] at hk
      have := h.absent j k ((isFull_write_ne hi hji).mp hj) hk
      rw [this] at hkk
      exact absurd hkk Bool.false_ne_true
    · rw [ite_eq_right hji] at hk
      rw [ite_eq_right hji'] at hk'
      exact wf.distinct j j' k k' ((isFull_write_ne hi hji).mp hj)
        ((isFull_write_ne hi hji').mp hj') hk hk' hkk
  · -- probe
    intro _ _ j k hj hk
    simp only at hk
    rw [getElem?_aset] at hk
    rw [cap_write]
    have H := groups_of_pointwise (s := ⟨ctrl, keys, vals⟩)
      (s' := Slots.mk (setCtrlN ctrl (ctrl.size - 8) i (tagOf q) h1 h2 h3) (keys.set i a h4)
        (vals.set i b h5)) h3 (fun x hx hne => by
          simp only
          rw [hb x hx]
          split
          · exact ne_EMPTY_of_lt ht
          · exact hne)
    by_cases hji : j = i
    · rw [ite_eq_left hji] at hk
      obtain rfl := Option.some.inj hk
      subst hji
      rw [← h.hash_eq]
      exact reach_transfer cap_write H hfs.reach
    · rw [ite_eq_right hji] at hk
      exact reach_transfer cap_write H (wf.probe j k ((isFull_write_ne hi hji).mp hj) hk)

/-- **The erasure of a full slot**, on `Nat` indices, by a rule that writes EMPTY only when
every 8-slot window containing the slot has another EMPTY slot. -/
private theorem WF.eraseGen (wf : WF ⟨ctrl, keys, vals⟩ size gl mask shift) {i : Nat}
    (hfull : Slots.IsFull ⟨ctrl, keys, vals⟩ i) (del : Bool)
    (hrule : del = false → ∀ p l₀, l₀ < 8 → (p + l₀) % (ctrl.size - 8) = i →
      ∃ l < 8, ctrl[(p + l) % (ctrl.size - 8)]! = EMPTY)
    {gl' : Nat} (hgl : if del = true then gl' ≤ gl else gl' = gl + 1)
    {k0 : α} {v0 : β} {h1 : i < ctrl.size} {h2 : ctrl.size - 8 + 8 ≤ ctrl.size}
    {h3 : 0 < ctrl.size - 8} {h4 : i < keys.size} {h5 : i < vals.size} :
    WF ⟨setCtrlN ctrl (ctrl.size - 8) i (if del then DELETED else EMPTY) h1 h2 h3,
      keys.set i k0 h4, vals.set i v0 h5⟩ (size - 1) gl' mask shift := by
  have hi : i < ctrl.size - 8 := hfull.1
  have hold : ctrl[i]! < 0x80 := hfull.2
  have htnf : ¬(if del then DELETED else EMPTY) < 0x80 := by
    split
    · exact DELETED_not_lt
    · exact EMPTY_not_lt
  have hb : ∀ j < ctrl.size - 8,
      (setCtrlN ctrl (ctrl.size - 8) i (if del then DELETED else EMPTY) h1 h2 h3)[j]! =
        if j = i then (if del then DELETED else EMPTY) else ctrl[j]! :=
    fun j hj => getElem!_setCtrlN hi hj
  obtain ⟨lg, hal⟩ := wf.alloc h3
  have hfull' : ∀ j, (Slots.mk (setCtrlN ctrl (ctrl.size - 8) i (if del then DELETED else EMPTY)
      h1 h2 h3) (keys.set i k0 h4) (vals.set i v0 h5)).IsFull j →
        j ≠ i ∧ Slots.IsFull ⟨ctrl, keys, vals⟩ j := by
    intro j hj
    have hji : j ≠ i := by
      rintro rfl
      have := hj.2
      simp only at this
      rw [hb j hi, ite_eq_left rfl] at this
      exact htnf this
    exact ⟨hji, (isFull_write_ne hi hji).mp hj⟩
  have hkey : ∀ j, j ≠ i → (keys.set i k0 h4)[j]? = keys[j]? := fun j hji => by
    rw [getElem?_aset, ite_eq_right hji]
  have hperm := entries_erase_perm hfull htnf k0 v0 (h1 := h1) (h2 := h2) (h3 := h3) (h4 := h4)
    (h5 := h5)
  have hlen := hperm.length_eq
  rw [List.length_cons] at hlen
  have hsz := wf.size_eq
  refine ⟨Or.inr ⟨lg, alloc_write hal hi⟩, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · -- control bytes
    intro j hj
    rw [cap_write] at hj
    simp only
    rw [hb j hj]
    split
    · split
      · exact isCtrl_DELETED
      · exact isCtrl_EMPTY
    · exact wf.ctrl j hj
  · -- tags
    intro j k hj hk
    obtain ⟨hji, hj'⟩ := hfull' j hj
    simp only at hk ⊢
    rw [hkey j hji] at hk
    rw [hb j hj'.1, ite_eq_right hji]
    exact wf.tag j k hj' hk
  · -- size
    omega
  · -- room
    have hnd := numDeleted_write (t := if del then DELETED else EMPTY) (a := k0) (b := v0)
      (h1 := h1) (h2 := h2) (h3 := h3) (h4 := h4) (h5 := h5) hi
    have hroom : gl + size + Slots.numDeleted ⟨ctrl, keys, vals⟩ ≤ capacityOf (ctrl.size - 8) :=
      wf.room
    rw [cap_write]
    have hod : (ctrl[i]! == DELETED) = false := beq_false_of_ne (ne_DELETED_of_lt hold)
    rw [hod] at hnd
    have hed : (EMPTY == DELETED) = false := beq_false_of_ne (Ne.symm DELETED_ne_EMPTY)
    cases del
    · simp only [Bool.false_eq_true, ite_false, hed] at hnd hgl ⊢
      omega
    · simp only [ite_true, beq_self_eq_true, Bool.false_eq_true, ite_false] at hnd hgl ⊢
      omega
  · -- distinct keys
    intro _ _ j j' k k' hj hj' hk hk' hkk
    obtain ⟨hji, hjf⟩ := hfull' j hj
    obtain ⟨hji', hjf'⟩ := hfull' j' hj'
    simp only at hk hk'
    rw [hkey j hji] at hk
    rw [hkey j' hji'] at hk'
    exact wf.distinct j j' k k' hjf hjf' hk hk' hkk
  · -- probe
    intro _ _ j k hj hk
    obtain ⟨hji, hjf⟩ := hfull' j hj
    simp only at hk
    rw [hkey j hji] at hk
    rw [cap_write]
    have H : ∀ p : Nat, (∀ l < 8, ctrl[(p + l) % (ctrl.size - 8)]! ≠ EMPTY) →
        ∀ l < 8, (setCtrlN ctrl (ctrl.size - 8) i (if del then DELETED else EMPTY) h1 h2 h3)[
          (p + l) % (ctrl.size - 8)]! ≠ EMPTY := by
      intro p hp' l hl
      have hx : (p + l) % (ctrl.size - 8) < ctrl.size - 8 := Nat.mod_lt _ h3
      rw [hb _ hx]
      split
      · rename_i hxi
        cases del
        · obtain ⟨l', hl', he⟩ := hrule rfl p l hl hxi
          exact absurd he (hp' l' hl')
        · exact DELETED_ne_EMPTY
      · exact hp' l hl
    exact reach_transfer (s := ⟨ctrl, keys, vals⟩) (s' := Slots.mk (setCtrlN ctrl (ctrl.size - 8)
      i (if del then DELETED else EMPTY) h1 h2 h3) (keys.set i k0 h4) (vals.set i v0 h5))
      cap_write H (wf.probe j k hjf hk)

/-- **The erase rule on `Nat` indices**: when it writes EMPTY, every 8-slot window containing slot
`i` already has an EMPTY slot. -/
private theorem exists_empty_of_ruleN {c : ByteArray} {cap : Nat} (hm : Mirrored c cap)
    (hctrl : ∀ k < cap, IsCtrl c[k]!) {i : Nat} {hw1 : i + 8 ≤ c.size}
    {hw2 : (i + cap - 8) % cap + 8 ≤ c.size}
    (hrule : needsTombstone (matchEmpty (ctrlWordN c i hw1))
      (matchEmpty (ctrlWordN c ((i + cap - 8) % cap) hw2)) = false)
    {p l₀ : Nat} (hl₀ : l₀ < 8) (hp : (p + l₀) % cap = i) :
    ∃ l < 8, c[(p + l) % cap]! = EMPTY := by
  have h8 := hm.le_cap
  have hcp : 0 < cap := by omega
  have hsl : ∀ y, slotByte c cap y = c[y % cap]! := fun y => slotByte_def c cap y
  have hctrl' : ∀ y, IsCtrl (slotByte c cap y) := fun y => by
    rw [hsl]; exact hctrl _ (Nat.mod_lt _ hcp)
  have hfa : ∀ l < 8, flag (matchEmpty (ctrlWordN c i hw1)) l =
      (slotByte c cap ((i + l) % cap) == EMPTY) := by
    intro l hl
    have hb := byte_ctrlWordN_of_mirrored hm (hw := hw1) hl
    rw [flag_matchEmpty_ctrl _ hl (by rw [hb]; exact hctrl' _), hb]
  have hfb : ∀ l < 8, flag (matchEmpty (ctrlWordN c ((i + cap - 8) % cap) hw2)) l =
      (slotByte c cap (((i + cap - 8) % cap + l) % cap) == EMPTY) := by
    intro l hl
    have hb := byte_ctrlWordN_of_mirrored hm (hw := hw2) hl
    rw [flag_matchEmpty_ctrl _ hl (by rw [hb]; exact hctrl' _), hb]
  rcases window_of_needsTombstone_eq_false (isMask_matchEmpty _) (isMask_matchEmpty _) hrule l₀
    with ⟨l, hl, hle, hf⟩ | ⟨l, hl, hlt, hf⟩
  · refine ⟨l + l₀ - 8, by omega, ?_⟩
    rw [hfb l hl, beq_iff_eq, hsl] at hf
    have H : ((i + cap - 8) % cap + l) % cap % cap = (p + (l + l₀ - 8)) % cap := by
      rw [Nat.mod_mod, Nat.mod_add_mod, ← hp,
        show (p + l₀) % cap + cap - 8 + l = (p + l₀) % cap + (cap - 8 + l) by omega,
        Nat.mod_add_mod, show p + l₀ + (cap - 8 + l) = p + (l + l₀ - 8) + cap by omega,
        Nat.add_mod_right]
    rw [H] at hf
    exact hf
  · refine ⟨l + l₀, by omega, ?_⟩
    rw [hfa l hl, beq_iff_eq, hsl] at hf
    have H : (i + l) % cap % cap = (p + (l + l₀)) % cap := by
      rw [Nat.mod_mod, ← hp, Nat.mod_add_mod, show p + l₀ + l = p + (l + l₀) by omega]
    rw [H] at hf
    exact hf

end WFGen

section Writes

variable [BEq α] [Hashable α] {ctrl : ByteArray} {keys : Array α} {vals : Array β}
  {size gl : Nat} {mask : USize} {shift : UInt64}

/-! ## The invariant after a write -/

/-- The invariant reads the value array only through its size. -/
theorem WF.replaceVals (wf : WF ⟨ctrl, keys, vals⟩ size gl mask shift) {vals' : Array γ}
    (h : vals'.size = vals.size) : WF ⟨ctrl, keys, vals'⟩ size gl mask shift := by
  have hv : ∀ j, (vals'[j]?).isSome = (vals[j]?).isSome := fun j => by
    by_cases hj : j < vals.size
    · rw [getElem?_pos vals j hj, getElem?_pos vals' j (by omega)]; rfl
    · rw [getElem?_neg vals j hj, getElem?_neg vals' j (by omega)]; rfl
  refine ⟨?_, wf.ctrl, wf.tag, ?_, wf.room, wf.distinct, wf.probe⟩
  · rcases wf.shape with hu | ⟨lg, hal⟩
    · exact Or.inl ⟨hu.ctrl_eq, hu.keys_size, by rw [h]; exact hu.vals_size, hu.mask_eq,
        hu.shift_eq⟩
    · exact Or.inr ⟨lg, hal.three_le, hal.mirrored, hal.keys_size,
        by rw [h]; exact hal.vals_size, hal.mask_eq, hal.shift_eq⟩
  · rw [wf.size_eq]
    refine (length_entries_congr (s := ⟨ctrl, keys, vals⟩) (s' := ⟨ctrl, keys, vals'⟩) rfl
      fun j _ => ?_).symm
    unfold Slots.entryAt
    simp only
    cases ctrl[j]? with
    | none => rfl
    | some c =>
      simp only
      split
      · cases keys[j]? with
        | none => rfl
        | some k => simp only [Option.bind_some, Option.isSome_map]; exact hv j
      · rfl

/-- Writing `a` over the key of a hit for `a`. -/
theorem WF.keyN (wf : WF ⟨ctrl, keys, vals⟩ size gl mask shift) {a : α} {i : Nat}
    (hi : Slots.Hit ⟨ctrl, keys, vals⟩ shift a i) {h : i < keys.size} :
    WF ⟨ctrl, keys.set i a h, vals⟩ size gl mask shift := by
  obtain ⟨hfull, htag, k, hk, hka⟩ := hi
  have hkey : ∀ j, (keys.set i a h)[j]? = if j = i then some a else keys[j]? :=
    fun j => getElem?_aset j
  -- every new key is `==` to the old key of its slot
  have hrep : ∀ [EquivBEq α] (x : Nat) (kx : α), (keys.set i a h)[x]? = some kx →
      ∃ ky, keys[x]? = some ky ∧ (ky == kx) = true := by
    intro _ x kx hx
    rw [hkey] at hx
    by_cases hxi : x = i
    · rw [ite_eq_left hxi] at hx
      obtain rfl := Option.some.inj hx
      subst hxi
      exact ⟨k, hk, hka⟩
    · rw [ite_eq_right hxi] at hx
      exact ⟨kx, hx, BEq.rfl⟩
  have hentry : ∀ j < ctrl.size - 8,
      (Slots.entryAt ⟨ctrl, keys.set i a h, vals⟩ j).isSome =
        (Slots.entryAt ⟨ctrl, keys, vals⟩ j).isSome := by
    intro j hj
    unfold Slots.entryAt
    simp only
    rw [hkey]
    by_cases hji : j = i
    · subst hji
      rw [ite_eq_left rfl, hk]
      cases ctrl[j]? with
      | none => rfl
      | some c =>
        simp only
        split
        · simp only [Option.bind_some, Option.isSome_map]
        · rfl
    · rw [ite_eq_right hji]
  refine ⟨?_, wf.ctrl, ?_, ?_, wf.room, ?_, ?_⟩
  · rcases wf.shape with hu | ⟨lg, hal⟩
    · exact Or.inl ⟨hu.ctrl_eq, by rw [Array.size_set]; exact hu.keys_size, hu.vals_size,
        hu.mask_eq, hu.shift_eq⟩
    · exact Or.inr ⟨lg, hal.three_le, hal.mirrored, by rw [Array.size_set]; exact hal.keys_size,
        hal.vals_size, hal.mask_eq, hal.shift_eq⟩
  · intro j kx hj hkx
    simp only at hkx
    rw [hkey] at hkx
    by_cases hji : j = i
    · rw [ite_eq_left hji] at hkx
      obtain rfl := Option.some.inj hkx
      subst hji
      exact htag
    · rw [ite_eq_right hji] at hkx
      exact wf.tag j kx hj hkx
  · rw [wf.size_eq]
    exact (length_entries_congr (s := ⟨ctrl, keys, vals⟩) (s' := ⟨ctrl, keys.set i a h, vals⟩)
      rfl hentry).symm
  · intro _ _ j j' k1 k2 hj hj' hk1 hk2 hkk
    obtain ⟨ky1, hky1, he1⟩ := hrep j k1 hk1
    obtain ⟨ky2, hky2, he2⟩ := hrep j' k2 hk2
    exact wf.distinct j j' ky1 ky2 hj hj' hky1 hky2 (BEq.trans he1 (BEq.trans hkk (BEq.symm he2)))
  · intro _ _ j kx hj hkx
    obtain ⟨ky, hky, he⟩ := hrep j kx hkx
    have hh : hashBits shift ky = hashBits shift kx := by unfold hashBits; rw [hash_eq he]
    have := wf.probe j ky hj hky
    rw [hh] at this
    exact this

/-- Writing `a` over the key of a hit for `a` (machine-word index). -/
theorem WF.keyU (wf : WF ⟨ctrl, keys, vals⟩ size gl mask shift) {a : α} {i : USize}
    (hi : Slots.Hit ⟨ctrl, keys, vals⟩ shift a i.toNat) {h : i.toNat < keys.size} :
    WF ⟨ctrl, keys.uset i a h, vals⟩ size gl mask shift := by
  simp only [Array.uset_eq_set]
  exact wf.keyN hi

/-- A new key at an EMPTY slot, with room (machine words). -/
theorem WF.newU_empty (wf : WF ⟨ctrl, keys, vals⟩ size gl mask shift)
    (hs : smallMask mask = true) {a : α} {b : β} {q : UInt64} {i : USize}
    (h : NewSlot ⟨ctrl, keys, vals⟩ shift a q i.toNat) {h0 : i.toNat < ctrl.size}
    (hold : (ctrl.uget i h0 == EMPTY) = true) (hgl : ¬(gl == 0) = true)
    {h1 : i.toNat < ctrl.size} {h2 : mask.toNat + 8 < ctrl.size} {h3 : i.toNat < keys.size}
    {h4 : i.toNat < vals.size} :
    WF ⟨setCtrl ctrl mask i (tagOf q) h1 h2, keys.uset i a h3, vals.uset i b h4⟩ (size + 1)
      (gl - 1) mask shift := by
  have hc : 0 < ctrl.size - 8 := wf.new_alloc_gl h hgl
  have hg : Geom (ctrl.size - 8) mask := wf.geom hs hc
  have hic : i.toNat < ctrl.size - 8 :=
    (h.slot.resolve_right fun ⟨hc0, _⟩ => absurd hc0 (Nat.ne_of_gt hc)).lt
  rw [setCtrl_eq_setCtrlN hg hic (h3 := h1) (h4 := wf.cap_word) (h5 := hc)]
  simp only [Array.uset_eq_set]
  refine wf.newGen h ?_
  have he : ctrl[i.toNat]! = EMPTY := by
    rw [getElem!_pos ctrl _ h0, ← uget_eq_getElem']; exact beq_iff_eq.mp hold
  rw [he, ite_eq_left rfl]
  simp only [beq_iff_eq] at hgl
  omega

/-- A new key at a DELETED slot (machine words). -/
theorem WF.newU_del (wf : WF ⟨ctrl, keys, vals⟩ size gl mask shift)
    (hs : smallMask mask = true) {a : α} {b : β} {q : UInt64} {i : USize}
    (h : NewSlot ⟨ctrl, keys, vals⟩ shift a q i.toNat) {h0 : i.toNat < ctrl.size}
    (hold : ¬(ctrl.uget i h0 == EMPTY) = true)
    {h1 : i.toNat < ctrl.size} {h2 : mask.toNat + 8 < ctrl.size} {h3 : i.toNat < keys.size}
    {h4 : i.toNat < vals.size} :
    WF ⟨setCtrl ctrl mask i (tagOf q) h1 h2, keys.uset i a h3, vals.uset i b h4⟩ (size + 1)
      gl mask shift := by
  have hc : 0 < ctrl.size - 8 := wf.new_alloc_old h hold
  have hg : Geom (ctrl.size - 8) mask := wf.geom hs hc
  have hic : i.toNat < ctrl.size - 8 :=
    (h.slot.resolve_right fun ⟨hc0, _⟩ => absurd hc0 (Nat.ne_of_gt hc)).lt
  rw [setCtrl_eq_setCtrlN hg hic (h3 := h1) (h4 := wf.cap_word) (h5 := hc)]
  simp only [Array.uset_eq_set]
  refine wf.newGen h ?_
  have he : ctrl[i.toNat]! ≠ EMPTY := by
    rw [getElem!_pos ctrl _ h0, ← uget_eq_getElem']; exact fun he => hold (beq_iff_eq.mpr he)
  rw [ite_eq_right he]
  rfl

/-- A new key at an EMPTY slot, with room. -/
theorem WF.newN_empty (wf : WF ⟨ctrl, keys, vals⟩ size gl mask shift) {a : α} {b : β}
    {q : UInt64} {i : Nat} (h : NewSlot ⟨ctrl, keys, vals⟩ shift a q i) {h0 : i < ctrl.size}
    (hold : (ctrl[i]'h0 == EMPTY) = true) (hgl : ¬(gl == 0) = true) {h1 : i < ctrl.size}
    {h2 : ctrl.size - 8 + 8 ≤ ctrl.size} {h3 : 0 < ctrl.size - 8} {h4 : i < keys.size}
    {h5 : i < vals.size} :
    WF ⟨setCtrlN ctrl (ctrl.size - 8) i (tagOf q) h1 h2 h3, keys.set i a h4, vals.set i b h5⟩
      (size + 1) (gl - 1) mask shift := by
  refine wf.newGen h ?_
  have he : ctrl[i]! = EMPTY := by rw [getElem!_pos ctrl i h0]; exact beq_iff_eq.mp hold
  rw [he, ite_eq_left rfl]
  simp only [beq_iff_eq] at hgl
  omega

/-- A new key at a DELETED slot. -/
theorem WF.newN_del (wf : WF ⟨ctrl, keys, vals⟩ size gl mask shift) {a : α} {b : β}
    {q : UInt64} {i : Nat} (h : NewSlot ⟨ctrl, keys, vals⟩ shift a q i) {h0 : i < ctrl.size}
    (hold : ¬(ctrl[i]'h0 == EMPTY) = true) {h1 : i < ctrl.size}
    {h2 : ctrl.size - 8 + 8 ≤ ctrl.size} {h3 : 0 < ctrl.size - 8} {h4 : i < keys.size}
    {h5 : i < vals.size} :
    WF ⟨setCtrlN ctrl (ctrl.size - 8) i (tagOf q) h1 h2 h3, keys.set i a h4, vals.set i b h5⟩
      (size + 1) gl mask shift := by
  refine wf.newGen h ?_
  have he : ctrl[i]! ≠ EMPTY := by
    rw [getElem!_pos ctrl i h0]; exact fun he => hold (beq_iff_eq.mpr he)
  rw [ite_eq_right he]
  rfl

/-- `insertFresh`'s write (machine words): the absent key at the free slot `findFree` finds. -/
theorem WF.freshU (wf : WF ⟨ctrl, keys, vals⟩ size gl mask shift) (hs : smallMask mask = true)
    {a : α} {b : β} (h : FreshPre ⟨ctrl, keys, vals⟩ gl a) {i : USize}
    (hi : i = findFree ctrl mask (homeU (hashBits shift a) mask) 0 (wf.loopU' hs).arr
      (and_mask_le _ _) stride_zero)
    {h1 : i.toNat < ctrl.size} {h2 : mask.toNat + 8 < ctrl.size} {h3 : i.toNat < keys.size}
    {h4 : i.toNat < vals.size} {h5 : i.toNat < ctrl.size} :
    WF ⟨setCtrl ctrl mask i (tagOf (hashBits shift a)) h1 h2, keys.uset i a h3, vals.uset i b h4⟩
      (size + 1) (if ctrl.uget i h5 == EMPTY then gl - 1 else gl) mask shift := by
  subst hi
  have hfs := wf.findFree_slot hs h
  have hc : 0 < ctrl.size - 8 := wf.cap_pos_of_gl h.room
  have hg : Geom (ctrl.size - 8) mask := wf.geom hs hc
  rw [setCtrl_eq_setCtrlN hg hfs.lt (h3 := h1) (h4 := wf.cap_word) (h5 := hc)]
  simp only [Array.uset_eq_set]
  refine wf.newGen ⟨rfl, Or.inl hfs, h.absent⟩ ?_
  have := h.room
  rw [uget_eq_getElem', getElem!_pos ctrl _ h5]
  simp only [beq_iff_eq]
  split <;> omega

/-- `insertFresh`'s write on `Nat` indices. -/
theorem WF.freshN (wf : WF ⟨ctrl, keys, vals⟩ size gl mask shift) (hs : ¬smallMask mask = true)
    {a : α} {b : β} (h : FreshPre ⟨ctrl, keys, vals⟩ gl a) {i : Nat}
    (hi : i = findFreeN ctrl (ctrl.size - 8) (homeN (hashBits shift a) (ctrl.size - 8)) 0
      (wf.ctrlN' hs) (Nat.mod_lt _ (wf.ctrlN' hs).pos))
    {h1 : i < ctrl.size} {h2 : ctrl.size - 8 + 8 ≤ ctrl.size} {h3 : 0 < ctrl.size - 8}
    {h4 : i < keys.size} {h5 : i < vals.size} {h6 : i < ctrl.size} :
    WF ⟨setCtrlN ctrl (ctrl.size - 8) i (tagOf (hashBits shift a)) h1 h2 h3, keys.set i a h4,
      vals.set i b h5⟩ (size + 1) (if ctrl[i]'h6 == EMPTY then gl - 1 else gl) mask shift := by
  subst hi
  have hfs := wf.findFreeN_slot hs h
  refine wf.newGen ⟨rfl, Or.inl hfs, h.absent⟩ ?_
  have := h.room
  rw [getElem!_pos ctrl _ h6]
  simp only [beq_iff_eq]
  split <;> omega

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
  have hc : 0 < ctrl.size - 8 := hi.cap_pos
  have hg : Geom (ctrl.size - 8) mask := wf.geom hs hc
  have hm : Mirrored ctrl (ctrl.size - 8) := wf.mirrored hc
  rw [setCtrl_eq_setCtrlN hg hi.1 (h3 := h1) (h4 := wf.cap_word) (h5 := hc)]
  simp only [Array.uset_eq_set]
  refine wf.eraseGen hi del ?_ ?_
  · intro hd p l₀ hl₀ hp
    have hctrl : ∀ k < ctrl.size - 8, IsCtrl (slotByte ctrl (ctrl.size - 8) k) := fun k hk => by
      rw [slotByte_def, Nat.mod_eq_of_lt hk]; exact wf.ctrl k hk
    obtain ⟨l, hl, he⟩ :=
      exists_empty_of_needsTombstone_eq_false hm hg hctrl hw1 hw2 (hdel ▸ hd) hl₀ hp
    exact ⟨l, hl, by rw [slotByte_def, Nat.mod_mod] at he; exact he⟩
  · subst hgl
    cases del
    · simp
    · simp only [ite_true]
      split <;> omega

/-- The erasure of a full slot by the tombstone rule, with any placeholders. -/
theorem WF.eraseN (wf : WF ⟨ctrl, keys, vals⟩ size gl mask shift) {i : Nat}
    (hi : Slots.IsFull ⟨ctrl, keys, vals⟩ i) {hic : i < ctrl.size - 8}
    {hc : ctrl.size - 8 + 8 ≤ ctrl.size} {c' : ByteArray} {gl' : Nat}
    (he : eraseCtrlN ctrl size gl (ctrl.size - 8) i hic hc = (c', gl')) {k0 : α} {v0 : β}
    {h1 : i < keys.size} {h2 : i < vals.size} :
    WF ⟨c', keys.set i k0 h1, vals.set i v0 h2⟩ (size - 1) gl' mask shift := by
  obtain ⟨del, hdel, rfl, rfl⟩ := eraseCtrlN_spec he
  refine wf.eraseGen hi del ?_ ?_
  · intro hd p l₀ hl₀ hp
    exact exists_empty_of_ruleN (wf.mirrored hi.cap_pos) (fun k hk => wf.ctrl k hk)
      (hdel ▸ hd) hl₀ hp
  · cases del
    · simp
    · simp only [ite_true]
      split <;> omega

/-! ## The entries after a write (`Nat` forms) -/

omit [BEq α] [Hashable α] in
/-- The erasure of slot `i` by the tombstone rule. -/
theorem entryAt_eraseN {i sz g : Nat} {hic : i < ctrl.size - 8}
    {hc : ctrl.size - 8 + 8 ≤ ctrl.size} {c' : ByteArray} {gl' : Nat}
    (he : eraseCtrlN ctrl sz g (ctrl.size - 8) i hic hc = (c', gl')) {k0 : α} {v0 : β}
    {h1 : i < keys.size} {h2 : i < vals.size} {j : Nat} (hj : j < ctrl.size - 8) :
    (Slots.mk c' (keys.set i k0 h1) (vals.set i v0 h2)).entryAt j =
      if j = i then none else Slots.entryAt ⟨ctrl, keys, vals⟩ j := by
  obtain ⟨del, -, rfl, -⟩ := eraseCtrlN_spec he
  rw [entryAt_write hic _ k0 v0 hj]
  by_cases hji : j = i
  · have ht : ¬(if del then DELETED else EMPTY) < 0x80 := by
      split
      · exact DELETED_not_lt
      · exact EMPTY_not_lt
    rw [ite_eq_left hji, ite_eq_left hji, ite_eq_right ht]
  · rw [ite_eq_right hji, ite_eq_right hji]

/-- The control array after an erasure has the same slots. -/
theorem cap_eraseN {ctrl : ByteArray} {sz g cap i : Nat} {hic : i < cap} {hc : cap + 8 ≤ ctrl.size}
    {c' : ByteArray} {gl' : Nat} (he : eraseCtrlN ctrl sz g cap i hic hc = (c', gl')) :
    c'.size = ctrl.size := by
  obtain ⟨del, -, rfl, -⟩ := eraseCtrlN_spec he
  exact size_setCtrlN ..

end Writes

/-- The key and value of a full slot. -/
theorem entryAt_kvN (s : Slots α β) {i : Nat} (hi : s.IsFull i) (a : α) (b : β)
    {h1 : i < s.keys.size} {h2 : i < s.vals.size} (j : Nat) :
    (Slots.mk s.ctrl (s.keys.set i a h1) (s.vals.set i b h2)).entryAt j =
      if j = i then some ⟨a, b⟩ else s.entryAt j := by
  unfold Slots.entryAt
  simp only
  rw [getElem?_aset, getElem?_aset]
  by_cases hji : j = i
  · subst hji
    have hic : j < s.ctrl.size := by have := hi.1; unfold Slots.cap at this; omega
    have hf := hi.2
    rw [getElem!_pos s.ctrl j hic] at hf
    rw [getElem?_pos s.ctrl j hic]
    simp [hf]
  · simp only [hji, ite_false]

section Lists

variable [BEq α] [Hashable α] {ctrl : ByteArray} {keys : Array α} {vals : Array β}
  {size gl : Nat} {mask : USize} {shift : UInt64}

omit [BEq α] [Hashable α] in
/-- A new entry at a free slot: the entries gain it, up to order (no lawfulness). -/
theorem entries_newN_perm {p₀ i : Nat} (hslot : Slots.FreeSlot ⟨ctrl, keys, vals⟩ p₀ i) {t : UInt8}
    (ht : t < 0x80) (a : α) (b : β)
    {h1 : i < ctrl.size} {h2 : ctrl.size - 8 + 8 ≤ ctrl.size} {h3 : 0 < ctrl.size - 8}
    {h4 : i < keys.size} {h5 : i < vals.size} :
    (Slots.mk (setCtrlN ctrl (ctrl.size - 8) i t h1 h2 h3) (keys.set i a h4)
      (vals.set i b h5)).entries.Perm (⟨a, b⟩ :: Slots.entries ⟨ctrl, keys, vals⟩) := by
  have hfree : ctrl[i]! = EMPTY ∨ ctrl[i]! = DELETED := hslot.free
  have hnf : ¬ctrl[i]! < 0x80 := by
    rcases hfree with h | h <;> rw [h]
    · exact EMPTY_not_lt
    · exact DELETED_not_lt
  exact entries_write_perm hslot.lt hnf ht a b

/-- The key and value of a hit for `a` replaced: `replaceEntry` (lawful instances). -/
theorem WF.entries_kvN_replace (wf : WF ⟨ctrl, keys, vals⟩ size gl mask shift) {a : α} {i : Nat}
    (hit : Slots.Hit ⟨ctrl, keys, vals⟩ shift a i) (b : β) {h1 : i < keys.size}
    {h2 : i < vals.size} [EquivBEq α] [LawfulHashable α] :
    (Slots.mk ctrl (keys.set i a h1) (vals.set i b h2)).entries =
      replaceEntry a b (Slots.entries ⟨ctrl, keys, vals⟩) := by
  obtain ⟨hfull, -, k, hk, hka⟩ := hit
  have hk' : keys[i] = k := by
    have hk2 : keys[i]? = some k := hk
    rw [getElem?_pos keys i h1] at hk2; exact Option.some.inj hk2
  unfold Slots.entries
  refine filterMap_replaceEntry (i := i) (e₀ := ⟨keys[i], vals[i]⟩) ?_
    (entryAt_of_isFull hfull h1 h2) (by simp only; rw [hk']; exact hka) List.nodup_range ?_ ?_
  · rw [entryAt_kvN ⟨ctrl, keys, vals⟩ hfull a b i, ite_eq_left rfl]
  · intro j _ hji
    rw [entryAt_kvN ⟨ctrl, keys, vals⟩ hfull a b j, ite_eq_right hji]
  · intro j hj hji e he
    have hjf := isFull_of_entryAt he (List.mem_range.mp hj)
    have hkj := (entryAt_eq_some he).2.2.1
    cases hc : (e.1 == a)
    · rfl
    · exact absurd (wf.distinct j i e.1 k hjf hfull hkj hk (BEq.trans hc (BEq.symm hka))) hji

/-- The erasure of the hit for `a`: `eraseKey` (lawful instances). -/
theorem WF.entries_eraseN_eraseKey (wf : WF ⟨ctrl, keys, vals⟩ size gl mask shift) {a : α}
    {i : Nat} (hit : Slots.Hit ⟨ctrl, keys, vals⟩ shift a i) {sz g : Nat}
    {hic : i < ctrl.size - 8} {hc : ctrl.size - 8 + 8 ≤ ctrl.size} {c' : ByteArray} {gl' : Nat}
    (he : eraseCtrlN ctrl sz g (ctrl.size - 8) i hic hc = (c', gl')) {k0 : α} {v0 : β}
    {h1 : i < keys.size} {h2 : i < vals.size} [EquivBEq α] [LawfulHashable α] :
    (Slots.mk c' (keys.set i k0 h1) (vals.set i v0 h2)).entries =
      eraseKey a (Slots.entries ⟨ctrl, keys, vals⟩) := by
  obtain ⟨hfull, -, k, hk, hka⟩ := hit
  have hk' : keys[i] = k := by
    have hk2 : keys[i]? = some k := hk
    rw [getElem?_pos keys i h1] at hk2; exact Option.some.inj hk2
  have hcap : (Slots.mk c' (keys.set i k0 h1) (vals.set i v0 h2)).cap = ctrl.size - 8 := by
    unfold Slots.cap; simp only; rw [cap_eraseN he]
  unfold Slots.entries
  rw [hcap]
  refine filterMap_eraseKey (i := i) (e₀ := ⟨keys[i], vals[i]⟩) ?_
    (entryAt_of_isFull hfull h1 h2) (by simp only; rw [hk']; exact hka) List.nodup_range ?_ ?_
  · rw [entryAt_eraseN he hic, ite_eq_left rfl]
  · intro j hj hji
    rw [entryAt_eraseN he (List.mem_range.mp hj), ite_eq_right hji]
  · intro j hj hji e he
    have hjf := isFull_of_entryAt he (List.mem_range.mp hj)
    have hkj := (entryAt_eq_some he).2.2.1
    cases hc : (e.1 == a)
    · rfl
    · exact absurd (wf.distinct j i e.1 k hjf hfull hkj hk (BEq.trans hc (BEq.symm hka))) hji

end Lists

/-! ## The rebuilt table (`Build.lean`) -/

/-- A table without key cells has no entries. -/
private theorem entries_eq_nil_of_keys {s : Slots α β} (h : s.keys.size = 0) : s.entries = [] := by
  unfold Slots.entries
  rw [List.filterMap_eq_nil_iff]
  intro j _
  unfold Slots.entryAt
  rw [getElem?_neg s.keys j (by omega)]
  cases s.ctrl[j]? with
  | none => rfl
  | some c => simp

/-- No entry of a table where `a` is absent has a key `== a`. -/
private theorem entries_of_absent [BEq α] {s : Slots α β} {a : α} (h : s.Absent a) :
    ∀ e ∈ s.entries, (e.1 == a) = false := by
  intro e he
  unfold Slots.entries at he
  obtain ⟨j, hj, hje⟩ := List.mem_filterMap.mp he
  have hjf := isFull_of_entryAt hje (List.mem_range.mp hj)
  have hk := (entryAt_eq_some hje).2.2.1
  exact h j e.1 hjf hk

/-- `a` is absent from a well-formed table when no entry has a key `== a`. -/
private theorem absent_of_entries [BEq α] [Hashable α] {s : Slots α β} {size gl : Nat}
    {mask : USize} {shift : UInt64} (wf : WF s size gl mask shift) {a : α}
    (h : ∀ e ∈ s.entries, (e.1 == a) = false) : s.Absent a := by
  intro i k hi hk
  have hik : i < s.keys.size := by
    by_cases hik : i < s.keys.size
    · exact hik
    · rw [getElem?_neg s.keys i hik] at hk; exact absurd hk (by simp)
  have hk' : s.keys[i] = k := by rw [getElem?_pos s.keys i hik] at hk; exact Option.some.inj hk
  have hmem : (⟨s.keys[i], s.vals[i]'(wf.vals_lt hi.1)⟩ : (_ : α) × β) ∈ s.entries := by
    unfold Slots.entries
    exact List.mem_filterMap.mpr ⟨i, List.mem_range.mpr hi.1, entryAt_of_isFull hi hik _⟩
  have := h _ hmem
  simp only at this
  rwa [hk'] at this

/-- The rebuilt table's room. -/
private theorem rebuild_growthLeft [BEq α] [Hashable α] (t : Table α β) (lg : Nat) (k0 : α)
    (v0 : β) (h : RebuildPre t.slots t.size lg) :
    (rebuild t lg k0 v0 h).growthLeft = capacityOf ((2 : Nat) ^ lg) - t.size := by
  obtain ⟨ctrl, keys, vals, size, gl, mask, shift, req, wf⟩ := t
  rfl

section Rebuilt

variable [BEq α] [Hashable α]

/-- A rebuild keeps the entries, up to order. -/
theorem rebuild_perm (t : Table α β) (lg : Nat) (k0 : α) (v0 : β)
    (h : RebuildPre t.slots t.size lg) :
    (rebuild t lg k0 v0 h).slots.entries.Perm t.slots.entries := by
  obtain ⟨ctrl, keys, vals, size, gl, mask, shift, req, wf⟩ := t
  exact rebuild_perm_raw wf h rfl

/-- A fresh table has no entries. -/
theorem emptyTable_entries (lg : Nat) (k0 : α) (v0 : β) (req : Nat) (h : 3 ≤ lg) :
    (emptyTable lg k0 v0 req h : Table α β).slots.entries = [] := by
  have h0 := (emptyTable lg k0 v0 req h : Table α β).wf.size_eq
  exact List.eq_nil_of_length_eq_zero h0.symm

/-- The table an insert that found no room writes into has the same entries, up to order. -/
theorem reserveTable_perm (t : Table α β) (a : α) (b : β) :
    (reserveTable t a b).slots.entries.Perm t.slots.entries := by
  unfold reserveTable
  split
  · rename_i hz
    have hz' : t.slotKeys.size = 0 := by simp only [beq_iff_eq] at hz; exact hz
    rw [emptyTable_entries, entries_eq_nil_of_keys (s := t.slots) hz']
  · dsimp only
    split
    · exact rebuild_perm ..
    · exact rebuild_perm ..

/-- The table an insert that found no room writes into has room for the absent key. -/
theorem freshPre_reserve (t : Table α β) (a : α) (b : β)
    (h : ∀ [EquivBEq α] [LawfulHashable α], t.slots.Absent a) :
    FreshPre (reserveTable t a b).slots (reserveTable t a b).growthLeft a := by
  refine ⟨?_, fun {_ _} => ?_⟩
  · unfold reserveTable
    split
    · have := le_capacityOf_lgFor (max t.reqCap 1)
      have he : (emptyTable (lgFor (max t.reqCap 1)) a b t.reqCap (three_le_lgFor _) :
          Table α β).growthLeft = capacityOf (2 ^ lgFor (max t.reqCap 1)) := rfl
      rw [he]
      omega
    · dsimp only
      split
      · rename_i hh
        have := le_capacityOf_lgFor (capacityOf (t.ctrl.size - 8))
        refine Nat.lt_of_lt_of_eq ?_ (rebuild_growthLeft t _ a b _).symm
        omega
      · have := le_capacityOf_lgFor (max (t.size + 1) (capacityOf (t.ctrl.size - 8) + 1))
        refine Nat.lt_of_lt_of_eq ?_ (rebuild_growthLeft t _ a b _).symm
        omega
  · refine absent_of_entries (reserveTable t a b).wf fun e he => ?_
    exact entries_of_absent h e ((reserveTable_perm t a b).mem_iff.mp he)

end Rebuilt

end SwissTable.Core.Swiss
