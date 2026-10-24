module

public import OAMap.Core.Swiss.Proofs.Write

/-!
# Swiss core proofs, part 5: the bulk passes of `filterMap` and `map`

A proof file of the SwissTable core (`OAMap/Core/Swiss/Table.lean`, "Proof structure"). Its
owner edits only this file: the proofs, and any private helper lemmas or definitions. The
statements are fixed: `Table.lean` and `Proofs/Traverse.lean` use them.

* `firstFull` and `firstSome` find the first full slot (whose entry `f` keeps) from slot `i` on
  (`firstFull_spec`, `firstFull_none`, `firstSome_spec`, `firstSome_none`).
* `filterMapLoop`, from the first kept slot `i0` (`firstSome`), erases every rejected entry in
  place by the tombstone rule and builds the new value array: the result is a well-formed table
  (`WF.filterMap`; no lawfulness is needed here: each erasure is `WF.eraseN` of
  `Proofs/Write.lean`, and the new value array is `WF.replaceVals`) whose entries are those of
  `List.filterMap` over the old ones, in slot order (`filterMap_entries_raw`; each erasure is
  `entryAt_eraseN`).

Suggested route: an invariant of `filterMapLoop` after the slots below `i`: `cap = ctrl.size - 8`,
the control bytes and keys are those of the old table with the rejected full slots below `i`
erased, `⟨ctrl, keys, vals⟩` with the counters `size`/`gl` is well formed (`WF.eraseN` at each
erasure), `out` has `i` cells, and cell `j < i` holds the mapped value of each kept full slot `j`.
-/

@[expose] public section

universe u v w

namespace OAMap.Core.Swiss

variable {α : Type u} {β : Type v} {γ : Type w}

/-! ## `firstFull` and `firstSome` -/

theorem firstFull_spec {ctrl : ByteArray} {cap i : Nat} {hc : cap ≤ ctrl.size} {j : Nat}
    (h : firstFull ctrl cap i hc = some j) :
    i ≤ j ∧ j < cap ∧ ctrl[j]! < 0x80 ∧ ∀ k, i ≤ k → k < j → ¬ctrl[k]! < 0x80 := by
  sorry

theorem firstFull_lt {ctrl : ByteArray} {cap i : Nat} {hc : cap ≤ ctrl.size} {j : Nat}
    (h : firstFull ctrl cap i hc = some j) : j < cap :=
  (firstFull_spec h).2.1

theorem firstFull_none {ctrl : ByteArray} {cap i : Nat} {hc : cap ≤ ctrl.size}
    (h : firstFull ctrl cap i hc = none) : ∀ k, i ≤ k → k < cap → ¬ctrl[k]! < 0x80 := by
  sorry

theorem firstSome_spec {f : α → β → Option γ} {ctrl : ByteArray} {keys : Array α}
    {vals : Array β} {cap i : Nat} {hA : FoldN ctrl keys vals cap} {j : Nat} {c : γ}
    (h : firstSome f ctrl keys vals cap i hA = some (j, c)) :
    i ≤ j ∧ j < cap ∧ ctrl[j]! < 0x80 ∧
      (∃ k v, keys[j]? = some k ∧ vals[j]? = some v ∧ f k v = some c) ∧
      ∀ l, i ≤ l → l < j → ctrl[l]! < 0x80 →
        ∀ k v, keys[l]? = some k → vals[l]? = some v → f k v = none := by
  sorry

theorem firstSome_none {f : α → β → Option γ} {ctrl : ByteArray} {keys : Array α}
    {vals : Array β} {cap i : Nat} {hA : FoldN ctrl keys vals cap}
    (h : firstSome f ctrl keys vals cap i hA = none) :
    ∀ l, i ≤ l → l < cap → ctrl[l]! < 0x80 →
      ∀ k v, keys[l]? = some k → vals[l]? = some v → f k v = none := by
  sorry

/-! ## `filterMapLoop` -/

section FilterMap

variable [BEq α] [Hashable α] {ctrl : ByteArray} {keys : Array α} {vals : Array β}
  {size gl : Nat} {mask : USize} {shift : UInt64}

/-- When `firstSome` finds a slot, the table is allocated, so `filterMapLoop` may read the
placeholder cell. -/
theorem WF.fmArr (wf : WF ⟨ctrl, keys, vals⟩ size gl mask shift) {f : α → β → Option γ}
    {hA : FoldN ctrl keys vals (ctrl.size - 8)} {i0 : Nat} {c0 : γ}
    (hs : firstSome f ctrl keys vals (ctrl.size - 8) 0 hA = some (i0, c0)) :
    FMArr ctrl keys vals (ctrl.size - 8) := by
  sorry

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
  sorry

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
  sorry

end FilterMap

end OAMap.Core.Swiss
