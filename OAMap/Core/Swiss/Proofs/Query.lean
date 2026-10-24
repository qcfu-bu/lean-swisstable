module

public import OAMap.Core.Swiss.Table
public import Std.Data.Internal.List.Associative

/-!
# Swiss core proofs, part 6: the model, the lookups and the fused operations (contract 1–11)

A proof file of the SwissTable core (`OAMap/Core/Swiss/Table.lean`, "Proof structure"): the
contract lemmas 1–11 (`docs/ARCHITECTURE.md` §3.3, checked by `test/OAMapTest/CoreSpec.lean`),
and what `Proofs/Update.lean` reads off a hit or a miss (`WF.getEntry?_hit`, `getEntry?_absent`).

* Lemmas 1–4, 6: the model is the entries in slot order; the size is their number
  (`WF.size_eq`); distinct keys come from `WF.distinct`; the unallocated table has no slot, so
  every probe of it misses (`WF.findU_hit` would give a full slot below `cap = 0`).
* Lemmas 5, 7, 8: a lookup is a probe; a hit is the entry `getEntry?` finds (keys are distinct
  under lawfulness), a miss is an absence (`WF.findU_absent`, `WF.findN_absent`). `erase` of the
  unallocated table misses and returns the table itself.
* Lemmas 9–11, **U**: the fused operations probe once. Their first components equal the lookup's
  by `WF.insProbeU_le_iff`, `insProbeU_eq_findU`, `fast_findU`, `insSlotN_inl_iff`,
  `insProbeN_inl_iff` (`Proofs/Probe.lean`) and the guard equivalence `WF.smallMask_eq`; their
  second components are `insert`/`insertIfNew` by definition (`Table.insert_def`, ...).

The contract definitions are sealed; the proofs unfold them with the `Table.*_def` lemmas of
`Table.lean` and then the exposed `Swiss.*Impl` bodies.
-/

@[expose] public section

universe u v w w'

open Std.Internal.List

namespace OAMap.Core

namespace Swiss

variable {α : Type u} {β : Type v}

section Entries

/-- The entry of a full slot with both cells. -/
private theorem entryAt_of {s : Slots α β} {i : Nat} (hf : s.IsFull i) {k : α} {v : β}
    (hk : s.keys[i]? = some k) (hv : s.vals[i]? = some v) : s.entryAt i = some ⟨k, v⟩ := by
  have hi : i < s.ctrl.size := by have := hf.1; unfold Slots.cap at this; omega
  have hlt : s.ctrl[i] < 0x80 := by have := hf.2; rwa [getElem!_pos s.ctrl i hi] at this
  unfold Slots.entryAt
  rw [getElem?_pos s.ctrl i hi]
  simp only [hlt, ↓reduceIte, hk, hv, Option.bind_some, Option.map_some]

end Entries

section Model

variable [BEq α] [Hashable α] {s : Slots α β} {size gl : Nat} {mask : USize} {shift : UInt64}

/-- The stored keys are distinct, as `Std.Internal.List` states it. -/
theorem WF.distinctKeys (wf : WF s size gl mask shift) [EquivBEq α] [LawfulHashable α] :
    DistinctKeys s.entries := by
  rw [DistinctKeys.def]
  unfold Slots.entries
  rw [List.pairwise_filterMap]
  refine List.Pairwise.imp_of_mem ?_ (List.pairwise_lt_range (n := s.cap))
  intro i j hi hj hij e he e' he'
  rw [List.mem_range] at hi hj
  have hfi := isFull_of_entryAt he hi
  have hfj := isFull_of_entryAt he' hj
  cases hb : e.1 == e'.1 with
  | false => rfl
  | true =>
    have := wf.distinct i j e.1 e'.1 hfi hfj (entryAt_eq_some he).2.2.1
      (entryAt_eq_some he').2.2.1 hb
    omega

/-- A hit for `a` is the entry `getEntry?` finds (lawful instances: the keys are distinct). -/
theorem WF.getEntry?_hit (wf : WF s size gl mask shift) {a : α} {i : Nat}
    (hit : s.Hit shift a i) {k : α} {v : β} (hk : s.keys[i]? = some k) (hv : s.vals[i]? = some v)
    [EquivBEq α] [LawfulHashable α] : getEntry? a s.entries = some ⟨k, v⟩ := by
  obtain ⟨hf, -, k', hk', hka⟩ := hit
  rw [hk] at hk'
  cases hk'
  exact getEntry?_of_mem wf.distinctKeys hka (mem_entries.2 ⟨i, hf.1, entryAt_of hf hk hv⟩)

set_option linter.unusedSectionVars false in
/-- No entry of an absent key. -/
theorem getEntry?_absent {a : α} (habs : s.Absent a) : getEntry? a s.entries = none := by
  rw [getEntry?_eq_find, List.find?_eq_none]
  intro e he
  obtain ⟨i, hi, h⟩ := mem_entries.1 he
  simp [habs i e.1 (isFull_of_entryAt h hi) (entryAt_eq_some h).2.2.1]

end Model

section Lookup

variable [BEq α] [Hashable α]

/-- **The lookup**: a hit for `a`, whose cells the continuation receives, or a miss, which is an
absence for lawful instances. -/
theorem lookupImpl_cases {σ : Type w} (t : Table α β) (a : α) (f : α → β → σ) (g : Unit → σ) :
    (∃ i k v, t.slots.Hit t.shift a i ∧ t.slotKeys[i]? = some k ∧ t.slotVals[i]? = some v ∧
      lookupImpl t a f g = f k v) ∨
    ((∀ [EquivBEq α] [LawfulHashable α], t.slots.Absent a) ∧ lookupImpl t a f g = g ()) := by
  unfold lookupImpl
  split
  · rename_i hs
    dsimp only
    split
    · rename_i hi
      exact Or.inl ⟨_, _, _, t.wf.findU_hit (t.wf.loopU hs) hi, getElem?_pos _ _ _,
        getElem?_pos _ _ _, rfl⟩
    · rename_i hi
      refine Or.inr ⟨?_, rfl⟩
      intro _ _
      exact t.wf.findU_absent (t.wf.loopU hs) hi
  · rename_i hs
    split
    · rename_i i he
      exact Or.inl ⟨i, _, _, t.wf.findN_hit (t.wf.arrN hs) he, getElem?_pos _ _ _,
        getElem?_pos _ _ _, rfl⟩
    · rename_i he
      refine Or.inr ⟨?_, rfl⟩
      intro _ _
      exact t.wf.findN_absent (t.wf.arrN hs) he

/-- `lookupMemImpl` takes the lookup's hit. -/
private theorem lookupMemImpl_eq {σ : Type w} (t : Table α β) (a : α) (h : containsImpl t a = true)
    (f : α → β → σ) : ∃ i k v, t.slots.Hit t.shift a i ∧ t.slotKeys[i]? = some k ∧
      t.slotVals[i]? = some v ∧ lookupMemImpl t a h f = f k v := by
  unfold lookupMemImpl
  split
  · rename_i hs
    dsimp only
    split
    · rename_i hi
      exact ⟨_, _, _, t.wf.findU_hit (t.wf.loopU hs) hi, getElem?_pos _ _ _,
        getElem?_pos _ _ _, rfl⟩
    · rename_i hi
      exact absurd h (by simp [containsImpl, lookupImpl, hs, hi])
  · rename_i hs
    unfold lookupMemN
    split
    · rename_i i he
      exact ⟨i, _, _, t.wf.findN_hit (t.wf.arrN hs) he, getElem?_pos _ _ _,
        getElem?_pos _ _ _, rfl⟩
    · rename_i he
      exact absurd h (by unfold containsImpl lookupImpl; rw [dite_eq_right hs]; split <;> simp_all)

/-! ## The fused operations probe where the lookup does (no lawfulness) -/

/-- A continuation-passing lookup commutes with a function of its result. -/
private theorem lookupImpl_comp {σ : Type w} {τ : Type w'} (t : Table α β) (a : α)
    (φ : σ → τ) {f : α → β → σ} {g : Unit → σ} :
    φ (lookupImpl t a f g) = lookupImpl t a (fun k v => φ (f k v)) (fun u => φ (g u)) := by
  unfold lookupImpl
  split
  · dsimp only
    split <;> rfl
  · split <;> rfl

private theorem uget_congr {γ : Type w} {xs : Array γ} {i j : USize} (h : i = j)
    (hi : i.toNat < xs.size) (hj : j.toNat < xs.size) : xs.uget i hi = xs.uget j hj := by
  subst h; rfl

/-- The first component of `containsThenInsertImpl` is `containsImpl`. -/
private theorem containsThenInsertImpl_fst (t : Table α β) (a : α) (b : β) :
    (containsThenInsertImpl t a b).1 = containsImpl t a := by
  obtain ⟨ctrl, keys, vals, size, gl, mask, shift, req, wf⟩ := t
  unfold containsThenInsertImpl containsImpl lookupImpl
  dsimp only
  by_cases hsm : smallMask mask = true
  · have hss : smallShift shift = true := wf.smallMask_eq ▸ hsm
    rw [dite_eq_left hsm, dite_eq_left hss]
    -- `split` decides the insertion probe's test `r ≤ mask` from `hr` in each branch.
    by_cases hf : findU ctrl keys mask shift a (wf.loopU hss) ≤ mask
    · have hr := (wf.insProbeU_le_iff (a := a) (wf.loopU' hsm)).2 hf
      rw [dite_eq_left hf]
      split
      · split
        · exact absurd hf (fast_findU (wf.loopU' hsm) ‹_› ‹_›)
        · rfl
      · rfl
    · have hr := mt (wf.insProbeU_le_iff (a := a) (wf.loopU' hsm)).1 hf
      rw [dite_eq_right hf]
      split
      · split
        · rfl
        · rfl
      · rfl
  · have hss : ¬smallShift shift = true := wf.smallMask_eq ▸ hsm
    rw [dite_eq_right hsm, dite_eq_right hss]
    unfold containsThenInsertN
    dsimp only
    split
    · rename_i i he
      split
      · rfl
      · rename_i he'
        have := (insSlotN_inl_iff (wf.arrN' hsm)).1 he
        simp_all
    · rename_i j he
      split
      · rename_i i he'
        have := (insSlotN_inl_iff (wf.arrN' hsm)).2 he'
        simp_all
      · rfl

/-- The first component of `getThenInsertIfNewImpl` is the lookup of the value. -/
private theorem getThenInsertIfNewImpl_fst (t : Table α β) (a : α) (b : β) :
    (getThenInsertIfNewImpl t a b).1 = lookupImpl t a (fun _ v => some v) (fun _ => none) := by
  obtain ⟨ctrl, keys, vals, size, gl, mask, shift, req, wf⟩ := t
  unfold getThenInsertIfNewImpl lookupImpl
  dsimp only
  by_cases hss : smallShift shift = true
  · rw [dite_eq_left hss, dite_eq_left hss]
    by_cases hf : findU ctrl keys mask shift a (wf.loopU hss) ≤ mask
    · have hr := (wf.insProbeU_le_iff (a := a) (wf.loopU hss)).2 hf
      rw [dite_eq_left hf, dite_eq_left hr]
      exact congrArg some (uget_congr (insProbeU_eq_findU (wf.loopU hss) hf) _ _)
    · have hr := mt (wf.insProbeU_le_iff (a := a) (wf.loopU hss)).1 hf
      rw [dite_eq_right hf, dite_eq_right hr]
  · rw [dite_eq_right hss, dite_eq_right hss]
    unfold getThenInsertIfNewN
    dsimp only
    split
    · rename_i i he
      split
      · rename_i i' he'
        have := (insProbeN_inl_iff (wf.arrN hss)).1 he
        rw [this] at he'
        cases he'
        rfl
      · rename_i he'
        have := (insProbeN_inl_iff (wf.arrN hss)).1 he
        simp_all
    · rename_i j he
      split
      · rename_i i he'
        have := (insProbeN_inl_iff (wf.arrN hss)).2 he'
        simp_all
      · rfl

end Lookup

end Swiss

namespace Table

open Swiss

variable {α : Type u} {β : Type v} {γ : Type w} {_ : BEq α} {_ : Hashable α}

theorem distinctKeys [EquivBEq α] [LawfulHashable α] (t : Table α β) :
    DistinctKeys t.toListModel := by
  rw [toListModel_def]; exact t.wf.distinctKeys

theorem size_eq_length (t : Table α β) : t.size = t.toListModel.length := by
  rw [toListModel_def]; exact t.wf.size_eq

theorem toListModel_emptyWithCapacity {c : Nat} :
    (emptyWithCapacity c : Table α β).toListModel = [] := by
  rw [toListModel_def, emptyWithCapacity_def]
  rfl

theorem lookup_emptyWithCapacity {σ : Type w} {c : Nat} {a : α} {f : α → β → σ}
    {g : Unit → σ} : (emptyWithCapacity c : Table α β).lookup a f g = g () := by
  rw [lookup_def, emptyWithCapacity_def]
  rcases lookupImpl_cases (emptyImpl c : Table α β) a f g with ⟨i, k, v, hit, -, -, -⟩ | ⟨-, h⟩
  · exact absurd hit.1.1 (by simp [Slots.cap, Table.slots, emptyImpl, emptyGroup, ByteArray.size])
  · exact h

theorem erase_emptyWithCapacity {c : Nat} {a : α} :
    (emptyWithCapacity c : Table α β).erase a = emptyWithCapacity c := by
  rw [erase_def, emptyWithCapacity_def]
  unfold eraseImpl
  split
  · rename_i hs
    dsimp only
    split
    · rename_i hi
      exact absurd ((emptyImpl c : Table α β).wf.findU_hit _ hi).1.1
        (by simp [Slots.cap, emptyImpl, emptyGroup, ByteArray.size])
    · rfl
  · rename_i hs
    exact absurd rfl hs

theorem contains_eq_lookup (t : Table α β) (a : α) :
    t.contains a = t.lookup a (fun _ _ => true) (fun _ => false) := by
  rw [contains_def, lookup_def]; rfl

theorem lookup_eq [EquivBEq α] [LawfulHashable α] {σ : Type w} (t : Table α β) (a : α)
    (f : α → β → σ) (g : Unit → σ) :
    t.lookup a f g = (getEntry? a t.toListModel).elim (g ()) (fun e => f e.1 e.2) := by
  rw [lookup_def, toListModel_def]
  rcases lookupImpl_cases t a f g with ⟨i, k, v, hit, hk, hv, h⟩ | ⟨habs, h⟩
  · have he : getEntry? a t.slots.entries = some ⟨k, v⟩ := t.wf.getEntry?_hit hit hk hv
    rw [h, he]; rfl
  · rw [h, getEntry?_absent habs]; rfl

theorem lookupMem_eq [EquivBEq α] [LawfulHashable α] {σ : Type w} (t : Table α β) (a : α)
    (h : t.contains a = true) (f : α → β → σ) {e : (_ : α) × β}
    (he : getEntry? a t.toListModel = some e) : t.lookupMem a h f = f e.1 e.2 := by
  rw [lookupMem_def]
  obtain ⟨i, k, v, hit, hk, hv, h'⟩ := lookupMemImpl_eq t a ((contains_def t a) ▸ h) f
  rw [h']
  have he' : getEntry? a t.slots.entries = some ⟨k, v⟩ := t.wf.getEntry?_hit hit hk hv
  rw [toListModel_def, he'] at he
  cases he
  rfl

theorem containsThenInsert_eq (t : Table α β) (a : α) (b : β) :
    t.containsThenInsert a b = (t.contains a, t.insert a b) := by
  rw [containsThenInsert_def, contains_def, insert_def, ← containsThenInsertImpl_fst t a b]

theorem containsThenInsertIfNew_eq (t : Table α β) (a : α) (b : β) :
    t.containsThenInsertIfNew a b = (t.contains a, t.insertIfNew a b) := by
  rw [containsThenInsertIfNew_def, contains_def, insertIfNew_def, getThenInsertIfNewImpl_fst,
    containsImpl, lookupImpl_comp t a Option.isSome]
  rfl

theorem getThenInsertIfNew?_eq (t : Table α β) (a : α) (b : β) :
    t.getThenInsertIfNew? a b =
      (t.lookup a (fun _ v => some v) (fun _ => none), t.insertIfNew a b) := by
  rw [getThenInsertIfNew?_def, lookup_def, insertIfNew_def, ← getThenInsertIfNewImpl_fst t a b]

end Table

end OAMap.Core
