module

public import SwissTable.Core.Swiss.Proofs.Write

/-!
# Swiss core proofs, part 5: the bulk passes of `filterMap` and `map`

A proof file of the Swiss core (`SwissTable/Core/Swiss/Table.lean`, "Proof structure"); `Table.lean`
and `Proofs/Traverse.lean` use its statements.

* `firstFull` and `firstSome` find the first full slot (whose entry `f` keeps) from slot `i` on
  (`firstFull_spec`, `firstFull_none`, `firstSome_spec`, `firstSome_none`).
* `filterMapLoop`, from the first kept slot `i0` (`firstSome`), erases every rejected entry in
  place by the tombstone rule and builds the new value array: the result is a well-formed table
  (`WF.filterMap`; no lawfulness is needed here: each erasure is `WF.eraseN` of
  `Proofs/Write.lean`, and the new value array is `WF.replaceVals`) whose entries are those of
  `List.filterMap` over the old ones, in slot order (`filterMap_entries_raw`; each erasure is
  `entryAt_eraseN`).

The proof (the private `fm_loop`, by `fun_induction`) carries an invariant of `filterMapLoop` after
the slots below `i`: `cap = ctrl.size - 8`, `⟨ctrl, keys, vals⟩` with the counters `size`/`gl` is
well formed (`WF.eraseN` at each erasure, the value array kept by `Array.set_getElem_self`), its
entry at each slot `j < i` is the old one if `f` keeps it and none otherwise (`entryAt_eraseN`),
the slots from `i` on are the old ones, `out` has `i` cells, and cell `j < i` holds the mapped
value of each kept entry `j`. At the end `out` has `cap + 1` cells, and swapping in `out` as the
value array (`entryAt_vals`, `WF.replaceVals`) gives the mapped entries (`fm_result`).
-/

@[expose] public section

universe u v w

namespace SwissTable.Core.Swiss

variable {α : Type u} {β : Type v} {γ : Type w}

/-! ## `firstFull` and `firstSome` -/

theorem firstFull_spec {ctrl : ByteArray} {cap i : Nat} {hc : cap ≤ ctrl.size} {j : Nat}
    (h : firstFull ctrl cap i hc = some j) :
    i ≤ j ∧ j < cap ∧ ctrl[j]! < 0x80 ∧ ∀ k, i ≤ k → k < j → ¬ctrl[k]! < 0x80 := by
  induction i using firstFull.induct ctrl cap hc with
  | case1 x hx hf =>
    rw [firstFull, dite_eq_left hx, ite_eq_left hf] at h
    obtain rfl : x = j := Option.some.inj h
    exact ⟨Nat.le_refl _, hx, by rwa [getElem!_pos ctrl x (by omega)],
      fun k h1 h2 => absurd h2 (by omega)⟩
  | case2 x hx hf ih =>
    rw [firstFull, dite_eq_left hx, ite_eq_right hf] at h
    obtain ⟨h1, h2, h3, h4⟩ := ih h
    refine ⟨by omega, h2, h3, fun k hk1 hk2 => ?_⟩
    rcases Nat.eq_or_lt_of_le hk1 with rfl | hk
    · rwa [getElem!_pos ctrl x (by omega)]
    · exact h4 k hk hk2
  | case3 x hx =>
    rw [firstFull, dite_eq_right hx] at h; cases h

theorem firstFull_lt {ctrl : ByteArray} {cap i : Nat} {hc : cap ≤ ctrl.size} {j : Nat}
    (h : firstFull ctrl cap i hc = some j) : j < cap :=
  (firstFull_spec h).2.1

theorem firstFull_none {ctrl : ByteArray} {cap i : Nat} {hc : cap ≤ ctrl.size}
    (h : firstFull ctrl cap i hc = none) : ∀ k, i ≤ k → k < cap → ¬ctrl[k]! < 0x80 := by
  induction i using firstFull.induct ctrl cap hc with
  | case1 x hx hf =>
    rw [firstFull, dite_eq_left hx, ite_eq_left hf] at h; cases h
  | case2 x hx hf ih =>
    rw [firstFull, dite_eq_left hx, ite_eq_right hf] at h
    intro k hk1 hk2
    rcases Nat.eq_or_lt_of_le hk1 with rfl | hk
    · rwa [getElem!_pos ctrl x (by omega)]
    · exact ih h k hk hk2
  | case3 x hx =>
    intro k hk1 hk2; omega

theorem firstSome_spec {f : α → β → Option γ} {ctrl : ByteArray} {keys : Array α}
    {vals : Array β} {cap i : Nat} {hA : FoldN ctrl keys vals cap} {j : Nat} {c : γ}
    (h : firstSome f ctrl keys vals cap i hA = some (j, c)) :
    i ≤ j ∧ j < cap ∧ ctrl[j]! < 0x80 ∧
      (∃ k v, keys[j]? = some k ∧ vals[j]? = some v ∧ f k v = some c) ∧
      ∀ l, i ≤ l → l < j → ctrl[l]! < 0x80 →
        ∀ k v, keys[l]? = some k → vals[l]? = some v → f k v = none := by
  induction i using firstSome.induct f ctrl keys vals cap hA with
  | case1 x hx hf c' hc =>
    rw [firstSome, dite_eq_left hx, ite_eq_left hf] at h
    split at h
    · rename_i c'' hc''
      obtain ⟨rfl, rfl⟩ := Prod.mk.inj (Option.some.inj h)
      refine ⟨Nat.le_refl _, hx, by rwa [getElem!_pos ctrl x (hA.ctrl_lt hx)],
        ⟨keys[x]'(hA.keys_lt hx), vals[x]'(hA.vals_lt hx), by simp [hA.keys_lt hx],
          by simp [hA.vals_lt hx], hc''⟩, fun l h1 h2 => absurd h2 (by omega)⟩
    · rename_i hn; rw [hn] at hc; cases hc
  | case2 x hx hf hn ih =>
    rw [firstSome, dite_eq_left hx, ite_eq_left hf] at h
    split at h
    · rename_i c'' hc''; rw [hn] at hc''; cases hc''
    · obtain ⟨h1, h2, h3, h4, h5⟩ := ih h
      refine ⟨by omega, h2, h3, h4, fun l hl1 hl2 hl3 k v hk hv => ?_⟩
      rcases Nat.eq_or_lt_of_le hl1 with rfl | hl
      · have hk' : keys[x]'(hA.keys_lt hx) = k := by simpa [hA.keys_lt hx] using hk
        have hv' : vals[x]'(hA.vals_lt hx) = v := by simpa [hA.vals_lt hx] using hv
        rw [← hk', ← hv']; exact hn
      · exact h5 l hl hl2 hl3 k v hk hv
  | case3 x hx hf ih =>
    rw [firstSome, dite_eq_left hx, ite_eq_right hf] at h
    obtain ⟨h1, h2, h3, h4, h5⟩ := ih h
    refine ⟨by omega, h2, h3, h4, fun l hl1 hl2 hl3 k v hk hv => ?_⟩
    rcases Nat.eq_or_lt_of_le hl1 with rfl | hl
    · rw [getElem!_pos ctrl x (hA.ctrl_lt hx)] at hl3; exact absurd hl3 hf
    · exact h5 l hl hl2 hl3 k v hk hv
  | case4 x hx =>
    rw [firstSome, dite_eq_right hx] at h; cases h

theorem firstSome_none {f : α → β → Option γ} {ctrl : ByteArray} {keys : Array α}
    {vals : Array β} {cap i : Nat} {hA : FoldN ctrl keys vals cap}
    (h : firstSome f ctrl keys vals cap i hA = none) :
    ∀ l, i ≤ l → l < cap → ctrl[l]! < 0x80 →
      ∀ k v, keys[l]? = some k → vals[l]? = some v → f k v = none := by
  induction i using firstSome.induct f ctrl keys vals cap hA with
  | case1 x hx hf c' hc =>
    rw [firstSome, dite_eq_left hx, ite_eq_left hf] at h
    split at h
    · cases h
    · rename_i hn; rw [hn] at hc; cases hc
  | case2 x hx hf hn ih =>
    rw [firstSome, dite_eq_left hx, ite_eq_left hf] at h
    split at h
    · rename_i c'' hc''; rw [hn] at hc''; cases hc''
    · intro l hl1 hl2 hl3 k v hk hv
      rcases Nat.eq_or_lt_of_le hl1 with rfl | hl
      · have hk' : keys[x]'(hA.keys_lt hx) = k := by simpa [hA.keys_lt hx] using hk
        have hv' : vals[x]'(hA.vals_lt hx) = v := by simpa [hA.vals_lt hx] using hv
        rw [← hk', ← hv']; exact hn
      · exact ih h l hl hl2 hl3 k v hk hv
  | case3 x hx hf ih =>
    rw [firstSome, dite_eq_left hx, ite_eq_right hf] at h
    intro l hl1 hl2 hl3 k v hk hv
    rcases Nat.eq_or_lt_of_le hl1 with rfl | hl
    · rw [getElem!_pos ctrl x (hA.ctrl_lt hx)] at hl3; exact absurd hl3 hf
    · exact ih h l hl hl2 hl3 k v hk hv
  | case4 x hx =>
    intro l hl1 hl2; omega

/-! ## `filterMapLoop` -/

/-! ### Private helpers: entries slot by slot, and the loop invariant -/

/-- Swapping the value array: the entry of a slot is read off the same control byte and key
cell, with the value cell of the new array. -/
private theorem entryAt_vals {c : ByteArray} {k : Array α} {v : Array β} {w : Array γ} {j : Nat}
    (hv : j < v.size) :
    Slots.entryAt ⟨c, k, w⟩ j =
      (Slots.entryAt ⟨c, k, v⟩ j).bind (fun p => w[j]?.map (⟨p.1, ·⟩)) := by
  simp only [Slots.entryAt]
  cases c[j]? with
  | none => rfl
  | some b =>
    simp only
    split
    · cases k[j]? with
      | none => rfl
      | some a => simp [hv]
    · rfl

/-- The invariant on the entries, one slot further: unchanged below and above slot `i`, and slot
`i` as `g` makes it. -/
private theorem hent_step {s s' s0 : Slots α β} {g : ((_ : α) × β) → Option ((_ : α) × β)}
    {cap i : Nat}
    (hent : ∀ j < cap, s.entryAt j = if j < i then (s0.entryAt j).bind g else s0.entryAt j)
    (hsame : ∀ j < cap, j ≠ i → s'.entryAt j = s.entryAt j)
    (hi : i < cap → s'.entryAt i = (s0.entryAt i).bind g) :
    ∀ j < cap, s'.entryAt j = if j < i + 1 then (s0.entryAt j).bind g else s0.entryAt j := by
  intro j hj
  by_cases hji : j = i
  · subst hji; rw [hi hj, ite_eq_left (Nat.lt_succ_self _)]
  · rw [hsame j hj hji, hent j hj]
    by_cases h1 : j < i
    · rw [ite_eq_left h1, ite_eq_left (by omega)]
    · rw [ite_eq_right h1, ite_eq_right (by omega)]

/-- The invariant on the new value array, one cell further. -/
private theorem hout_step {f : α → β → Option γ} {s0 : Slots α β} {out : Array γ} {x : γ}
    {i : Nat} (hos : out.size = i)
    (hout : ∀ j < i, ∀ p c, s0.entryAt j = some p → f p.1 p.2 = some c → out[j]? = some c)
    (hx : ∀ p c, s0.entryAt i = some p → f p.1 p.2 = some c → x = c) :
    ∀ j < i + 1, ∀ p c, s0.entryAt j = some p → f p.1 p.2 = some c →
      (out.push x)[j]? = some c := by
  intro j hj p c hp hc
  rw [Array.getElem?_push]
  by_cases hji : j = i
  · subst hji; rw [ite_eq_left hos.symm, hx p c hp hc]
  · rw [ite_eq_right (by omega)]; exact hout j (by omega) p c hp hc

/-- At the slot `i` the loop is at, the current entry is the original one. -/
private theorem fm_cur {s s0 : Slots α β} {g : ((_ : α) × β) → Option ((_ : α) × β)}
    {cap i : Nat} (hi : i < cap)
    (hent : ∀ j < cap, s.entryAt j = if j < i then (s0.entryAt j).bind g else s0.entryAt j) :
    s0.entryAt i = s.entryAt i := by
  rw [hent i hi, ite_eq_right (Nat.lt_irrefl _)]

/-- The loop's erasure of the full slot `i`, whose entry `f` rejects: the invariant one slot
further (`WF.eraseN`, `entryAt_eraseN`; the value array stays the old one,
`Array.set_getElem_self`). -/
private theorem fm_erase [BEq α] [Hashable α] {mask : USize} {shift : UInt64}
    {f : α → β → Option γ} {vals : Array β} {s0 : Slots α β} {i : Nat} {ctrl : ByteArray}
    {keys : Array α} {size gl : Nat} {out : Array γ} {x : γ}
    (hA : FMArr ctrl keys vals (ctrl.size - 8)) (h : i < ctrl.size - 8)
    (hf : ctrl[i]'(hA.ctrl_lt h) < 0x80)
    (hrej : f (keys[i]'(hA.keys_lt h)) (vals[i]'(hA.vals_lt h)) = none)
    {ctrl1 : ByteArray} {gl1 : Nat}
    (he : eraseCtrlN ctrl size gl (ctrl.size - 8) i h hA.word = (ctrl1, gl1))
    (wf : WF ⟨ctrl, keys, vals⟩ size gl mask shift)
    (hent : ∀ j < ctrl.size - 8, Slots.entryAt ⟨ctrl, keys, vals⟩ j =
       if j < i then (s0.entryAt j).bind (fun p => (f p.1 p.2).map (fun _ => p))
       else s0.entryAt j)
    (hos : out.size = i)
    (hout : ∀ j < i, ∀ p c, s0.entryAt j = some p → f p.1 p.2 = some c → out[j]? = some c) :
    ctrl.size - 8 = ctrl1.size - 8 ∧
    WF ⟨ctrl1, keys.set i (keys[ctrl.size - 8]'hA.keys) (hA.keys_lt h), vals⟩ (size - 1) gl1
      mask shift ∧
    (∀ j < ctrl.size - 8,
      Slots.entryAt ⟨ctrl1, keys.set i (keys[ctrl.size - 8]'hA.keys) (hA.keys_lt h), vals⟩ j =
       if j < i + 1 then (s0.entryAt j).bind (fun p => (f p.1 p.2).map (fun _ => p))
       else s0.entryAt j) ∧
    (∀ j < i + 1, ∀ p c, s0.entryAt j = some p → f p.1 p.2 = some c →
      (out.push x)[j]? = some c) := by
  have hk : i < keys.size := hA.keys_lt h
  have hv : i < vals.size := hA.vals_lt h
  have hfull : Slots.IsFull ⟨ctrl, keys, vals⟩ i :=
    ⟨h, by rw [getElem!_pos ctrl i (hA.ctrl_lt h)]; exact hf⟩
  have hs0 : s0.entryAt i = some ⟨keys[i], vals[i]⟩ := by
    rw [fm_cur h hent]; exact entryAt_of_full (s := ⟨ctrl, keys, vals⟩) (hA.ctrl_lt h) hf hk hv
  have hsz := size_eraseCtrlN ctrl size gl _ i h hA.word
  rw [he] at hsz
  have wf' := wf.eraseN hfull he (k0 := keys[ctrl.size - 8]'hA.keys) (v0 := vals[i])
    (h1 := hk) (h2 := hv)
  rw [Array.set_getElem_self] at wf'
  have hE := fun j (hj : j < ctrl.size - 8) => entryAt_eraseN he
    (k0 := keys[ctrl.size - 8]'hA.keys) (v0 := vals[i]) (h1 := hk) (h2 := hv) hj
  simp only [Array.set_getElem_self] at hE
  refine ⟨by simp only at hsz; omega, wf', ?_, ?_⟩
  · apply hent_step hent
    · intro j hj hji; rw [hE j hj, ite_eq_right hji]
    · intro hi'; rw [hE i hi', ite_eq_left rfl, hs0]; simp [hrej]
  · apply hout_step hos hout
    intro p c hp hc; rw [hs0] at hp; cases hp; simp only at hc; rw [hrej] at hc; cases hc

/-- The loop's step over the full slot `i` whose entry `f` keeps, mapped to `x`. -/
private theorem fm_keep {f : α → β → Option γ} {vals : Array β} {s0 : Slots α β} {cap i : Nat}
    {ctrl : ByteArray} {keys : Array α} {out : Array γ} {x : γ}
    (hA : FMArr ctrl keys vals cap) (h : i < cap) (hf : ctrl[i]'(hA.ctrl_lt h) < 0x80)
    (hkeep : f (keys[i]'(hA.keys_lt h)) (vals[i]'(hA.vals_lt h)) = some x)
    (hent : ∀ j < cap, Slots.entryAt ⟨ctrl, keys, vals⟩ j =
       if j < i then (s0.entryAt j).bind (fun p => (f p.1 p.2).map (fun _ => p))
       else s0.entryAt j)
    (hos : out.size = i)
    (hout : ∀ j < i, ∀ p c, s0.entryAt j = some p → f p.1 p.2 = some c → out[j]? = some c) :
    (∀ j < cap, Slots.entryAt ⟨ctrl, keys, vals⟩ j =
       if j < i + 1 then (s0.entryAt j).bind (fun p => (f p.1 p.2).map (fun _ => p))
       else s0.entryAt j) ∧
    (∀ j < i + 1, ∀ p c, s0.entryAt j = some p → f p.1 p.2 = some c →
      (out.push x)[j]? = some c) := by
  have hcur := entryAt_of_full (s := ⟨ctrl, keys, vals⟩) (hA.ctrl_lt h) hf (hA.keys_lt h)
    (hA.vals_lt h)
  have hs0 : s0.entryAt i = some ⟨keys[i]'(hA.keys_lt h), vals[i]'(hA.vals_lt h)⟩ := by
    rw [fm_cur h hent]; exact hcur
  refine ⟨hent_step hent (fun j _ _ => rfl) fun _ => ?_, hout_step hos hout fun p c hp hc => ?_⟩
  · rw [hcur, hs0]; simp [hkeep]
  · rw [hs0] at hp; cases hp; simp only at hc; rw [hkeep] at hc; cases hc; rfl

/-- **The invariant of `filterMapLoop`** after the slots below `i`: the table `⟨ctrl, keys, vals⟩`
is well formed, its entry at each slot `j < i` is the original one if `f` keeps it and none
otherwise, the slots from `i` on are the original ones, and `out` has `i` cells, cell `j` holding
the mapped value of each kept entry `j`. The original table `s0` has its entries below `i0`
rejected and its entry at `i0` mapped to `c0` (`firstSome_spec`). -/
private theorem fm_loop [BEq α] [Hashable α] {mask : USize} {shift : UInt64}
    {f : α → β → Option γ} {vals : Array β} {cap i0 : Nat} {c0 : γ} {s0 : Slots α β}
    (hrej : ∀ j < i0, ∀ p, s0.entryAt j = some p → f p.1 p.2 = none)
    (hi0 : ∀ p, s0.entryAt i0 = some p → f p.1 p.2 = some c0)
    (i : Nat) (ctrl : ByteArray) (keys : Array α) (size gl : Nat) (out : Array γ)
    (hA : FMArr ctrl keys vals cap) :
    cap = ctrl.size - 8 → i ≤ cap → WF ⟨ctrl, keys, vals⟩ size gl mask shift →
    (∀ j < cap, Slots.entryAt ⟨ctrl, keys, vals⟩ j =
       if j < i then (s0.entryAt j).bind (fun p => (f p.1 p.2).map (fun _ => p))
       else s0.entryAt j) →
    out.size = i →
    (∀ j < i, ∀ p c, s0.entryAt j = some p → f p.1 p.2 = some c → out[j]? = some c) →
    ∀ ctrl' keys' size' gl' out',
      filterMapLoop f vals cap i0 c0 i ctrl keys size gl out hA =
        (ctrl', keys', size', gl', out') →
    cap = ctrl'.size - 8 ∧ WF ⟨ctrl', keys', vals⟩ size' gl' mask shift ∧
    (∀ j < cap, Slots.entryAt ⟨ctrl', keys', vals⟩ j =
       (s0.entryAt j).bind (fun p => (f p.1 p.2).map (fun _ => p))) ∧
    out'.size = cap + 1 ∧
    (∀ j < cap, ∀ p c, s0.entryAt j = some p → f p.1 p.2 = some c → out'[j]? = some c) := by
  fun_induction filterMapLoop f vals cap i0 c0 i ctrl keys size gl out hA with
  | case1 i ctrl keys size gl out hA h hf hlt ctrl1 gl1 he keys1 ih =>
    intro hcap hi wf hent hos hout
    subst hcap
    have hs0 : s0.entryAt i = some ⟨keys[i]'(hA.keys_lt h), vals[i]'(hA.vals_lt h)⟩ := by
      rw [fm_cur h hent]
      exact entryAt_of_full (s := ⟨ctrl, keys, vals⟩) (hA.ctrl_lt h) hf (hA.keys_lt h)
        (hA.vals_lt h)
    obtain ⟨h1, h2, h3, h4⟩ :=
      fm_erase (x := c0) hA h hf (hrej i hlt _ hs0) he wf hent hos hout
    exact ih h1 (by omega) h2 h3 (by simp [hos]) h4
  | case2 ctrl keys size gl out hA h hf hlt ih =>
    intro hcap hi wf hent hos hout
    have hs0 : s0.entryAt i0 = some ⟨keys[i0]'(hA.keys_lt h), vals[i0]'(hA.vals_lt h)⟩ := by
      rw [fm_cur h hent]
      exact entryAt_of_full (s := ⟨ctrl, keys, vals⟩) (hA.ctrl_lt h) hf (hA.keys_lt h)
        (hA.vals_lt h)
    obtain ⟨h3, h4⟩ := fm_keep hA h hf (hi0 _ hs0) hent hos hout
    exact ih hcap (by omega) wf h3 (by simp [hos]) h4
  | case3 i ctrl keys size gl out hA h hf hlt hne c hc ih =>
    intro hcap hi wf hent hos hout
    obtain ⟨h3, h4⟩ := fm_keep hA h hf hc hent hos hout
    exact ih hcap (by omega) wf h3 (by simp [hos]) h4
  | case4 i ctrl keys size gl out hA h hf hlt hne hfn ctrl1 gl1 he keys1 ih =>
    intro hcap hi wf hent hos hout
    subst hcap
    obtain ⟨h1, h2, h3, h4⟩ := fm_erase (x := c0) hA h hf hfn he wf hent hos hout
    exact ih h1 (by omega) h2 h3 (by simp [hos]) h4
  | case5 i ctrl keys size gl out hA h hf ih =>
    intro hcap hi wf hent hos hout
    have hcur := entryAt_of_not_full (s := ⟨ctrl, keys, vals⟩) (hA.ctrl_lt h) hf
    have hs0 : s0.entryAt i = none := by rw [fm_cur h hent]; exact hcur
    apply ih hcap (by omega) wf ?_ (by simp [hos]) ?_
    · exact hent_step hent (fun j _ _ => rfl) fun _ => by rw [hcur, hs0]; rfl
    · exact hout_step hos hout fun p c hp _ => by rw [hs0] at hp; cases hp
  | case6 i ctrl keys size gl out hA h =>
    intro hcap hi wf hent hos hout ctrl' keys' size' gl' out' hl
    simp only [Prod.mk.injEq] at hl
    obtain ⟨rfl, rfl, rfl, rfl, rfl⟩ := hl
    have hic : i = cap := by omega
    subst hic
    refine ⟨hcap, wf, fun j hj => by rw [hent j hj, ite_eq_left hj], by simp [hos],
      fun j hj p c hp hc => ?_⟩
    rw [Array.getElem?_push, ite_eq_right (by omega)]; exact hout j hj p c hp hc

/-- The table `filterMapImpl` builds: the same slots, well formed, and the entry of each slot is
the original one mapped by `f` (none when `f` rejects it). -/
private theorem fm_result [BEq α] [Hashable α] {ctrl : ByteArray} {keys : Array α}
    {vals : Array β} {size gl : Nat} {mask : USize} {shift : UInt64}
    (wf : WF ⟨ctrl, keys, vals⟩ size gl mask shift) {f : α → β → Option γ}
    {hA : FoldN ctrl keys vals (ctrl.size - 8)} {i0 : Nat} {c0 : γ}
    (hs : firstSome f ctrl keys vals (ctrl.size - 8) 0 hA = some (i0, c0))
    {hB : FMArr ctrl keys vals (ctrl.size - 8)} {ctrl' : ByteArray} {keys' : Array α}
    {size' gl' : Nat} {out : Array γ}
    (hl : filterMapLoop f vals (ctrl.size - 8) i0 c0 0 ctrl keys size gl
      (Array.emptyWithCapacity (ctrl.size - 8 + 1)) hB = (ctrl', keys', size', gl', out)) :
    ctrl.size - 8 = ctrl'.size - 8 ∧ WF ⟨ctrl', keys', out⟩ size' gl' mask shift ∧
    ∀ j < ctrl.size - 8, Slots.entryAt ⟨ctrl', keys', out⟩ j =
      (Slots.entryAt ⟨ctrl, keys, vals⟩ j).bind fun p => (f p.1 p.2).map (⟨p.1, ·⟩) := by
  obtain ⟨-, hi0lt, -, ⟨k0, v0, hk0, hv0, hf0⟩, hrej⟩ := firstSome_spec hs
  have hcap : 0 < ctrl.size - 8 := by omega
  have hvs : vals.size = ctrl.size - 8 + 1 := wf.vals_size hcap
  obtain ⟨hcap', wf', hent', hos', hout'⟩ :=
    fm_loop (s0 := ⟨ctrl, keys, vals⟩) (f := f) (c0 := c0) (i0 := i0)
      (fun j hj p hp => by
        obtain ⟨-, h1, h2, h3⟩ := entryAt_eq_some hp
        exact hrej j (Nat.zero_le _) hj h1 p.1 p.2 h2 h3)
      (fun p hp => by
        obtain ⟨-, -, h2, h3⟩ := entryAt_eq_some hp
        have e1 : p.1 = k0 := Option.some.inj (h2.symm.trans hk0)
        have e2 : p.2 = v0 := Option.some.inj (h3.symm.trans hv0)
        rw [e1, e2]; exact hf0)
      0 ctrl keys size gl _ hB rfl (Nat.zero_le _) wf (fun j _ => by simp) (by simp)
      (fun j hj => absurd hj (Nat.not_lt_zero _)) ctrl' keys' size' gl' out hl
  refine ⟨hcap', wf'.replaceVals (by omega), fun j hj => ?_⟩
  rw [entryAt_vals (v := vals) (by omega), hent' j hj]
  cases he : Slots.entryAt ⟨ctrl, keys, vals⟩ j with
  | none => rfl
  | some p =>
    cases hfp : f p.1 p.2 with
    | none => simp [hfp]
    | some c => simp [hfp, hout' j hj p c he hfp]

/-! ### The statements -/

section FilterMap

variable [BEq α] [Hashable α] {ctrl : ByteArray} {keys : Array α} {vals : Array β}
  {size gl : Nat} {mask : USize} {shift : UInt64}

/-- When `firstSome` finds a slot, the table is allocated, so `filterMapLoop` may read the
placeholder cell. -/
theorem WF.fmArr (wf : WF ⟨ctrl, keys, vals⟩ size gl mask shift) {f : α → β → Option γ}
    {hA : FoldN ctrl keys vals (ctrl.size - 8)} {i0 : Nat} {c0 : γ}
    (hs : firstSome f ctrl keys vals (ctrl.size - 8) 0 hA = some (i0, c0)) :
    FMArr ctrl keys vals (ctrl.size - 8) := by
  obtain ⟨-, hi0, -⟩ := firstSome_spec hs
  have hc : 0 < ctrl.size - 8 := by omega
  exact ⟨wf.cap_word, wf.place_keysN hc, Nat.le_of_lt (wf.place_valsN hc)⟩

/-- **`filterMap` builds a well-formed table** (no lawfulness). The hypotheses are the two
calls of `Table.lean`'s `filterMapImpl`, word for word. -/
theorem WF.filterMap (wf : WF ⟨ctrl, keys, vals⟩ size gl mask shift) {f : α → β → Option γ}
    {hA : FoldN ctrl keys vals (ctrl.size - 8)} {i0 : Nat} {c0 : γ}
    (hs : firstSome f ctrl keys vals (ctrl.size - 8) 0 hA = some (i0, c0))
    {hB : FMArr ctrl keys vals (ctrl.size - 8)} {ctrl' : ByteArray} {keys' : Array α}
    {size' gl' : Nat} {out : Array γ}
    (hl : filterMapLoop f vals (ctrl.size - 8) i0 c0 0 ctrl keys size gl
      (Array.emptyWithCapacity (ctrl.size - 8 + 1)) hB = (ctrl', keys', size', gl', out)) :
    WF ⟨ctrl', keys', vals.propagateMark out⟩ size' gl' mask shift := by
  rw [Array.propagateMark_eq]
  exact (fm_result wf hs hl).2.1

/-- **`filterMap`'s entries** are `List.filterMap` of the old ones, in slot order (no
lawfulness). -/
theorem filterMap_entries_raw (wf : WF ⟨ctrl, keys, vals⟩ size gl mask shift)
    {f : α → β → Option γ} {hA : FoldN ctrl keys vals (ctrl.size - 8)} {i0 : Nat} {c0 : γ}
    (hs : firstSome f ctrl keys vals (ctrl.size - 8) 0 hA = some (i0, c0))
    {hB : FMArr ctrl keys vals (ctrl.size - 8)} {ctrl' : ByteArray} {keys' : Array α}
    {size' gl' : Nat} {out : Array γ}
    (hl : filterMapLoop f vals (ctrl.size - 8) i0 c0 0 ctrl keys size gl
      (Array.emptyWithCapacity (ctrl.size - 8 + 1)) hB = (ctrl', keys', size', gl', out)) :
    (Slots.mk ctrl' keys' (vals.propagateMark out)).entries =
      (Slots.entries ⟨ctrl, keys, vals⟩).filterMap fun p => (f p.1 p.2).map (⟨p.1, ·⟩) := by
  rw [Array.propagateMark_eq]
  obtain ⟨hc, -, hE⟩ := fm_result wf hs hl
  unfold Slots.entries Slots.cap
  rw [List.filterMap_filterMap, ← hc]
  exact filterMap_congr_mem fun j hj => hE j (List.mem_range.mp hj)

end FilterMap

end SwissTable.Core.Swiss
