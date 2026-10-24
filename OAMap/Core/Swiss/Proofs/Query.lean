module

public import OAMap.Core.Swiss.Table
public import Std.Data.Internal.List.Associative

/-!
# Swiss core proofs, part 6: the model, the lookups and the fused operations (contract 1–11)

A proof file of the SwissTable core (`OAMap/Core/Swiss/Table.lean`, "Proof structure"). Its
owner edits only this file: the proofs, and any private helper lemmas or definitions. The
contract lemmas (`docs/ARCHITECTURE.md` §3.3, checked by `test/OAMapTest/CoreSpec.lean`) are
fixed word for word; so are the helpers in namespace `Swiss` that `Proofs/Update.lean` uses
(`WF.distinctKeys`, `WF.getEntry?_hit`, `getEntry?_absent`, `lookupImpl_cases`). Those marked
*suggested route* may be changed or dropped.

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

The contract definitions are sealed; unfold them with the `Table.*_def` lemmas of `Table.lean`
and then the exposed `Swiss.*Impl` bodies.
-/

@[expose] public section

universe u v w w'

open Std.Internal.List

namespace OAMap.Core

namespace Swiss

variable {α : Type u} {β : Type v}

section Model

variable [BEq α] [Hashable α] {s : Slots α β} {size gl : Nat} {mask : USize} {shift : UInt64}

/-- The stored keys are distinct, as `Std.Internal.List` states it. -/
theorem WF.distinctKeys (wf : WF s size gl mask shift) [EquivBEq α] [LawfulHashable α] :
    DistinctKeys s.entries := by
  sorry

/-- A hit for `a` is the entry `getEntry?` finds (lawful instances: the keys are distinct). -/
theorem WF.getEntry?_hit (wf : WF s size gl mask shift) {a : α} {i : Nat}
    (hit : s.Hit shift a i) {k : α} {v : β} (hk : s.keys[i]? = some k) (hv : s.vals[i]? = some v)
    [EquivBEq α] [LawfulHashable α] : getEntry? a s.entries = some ⟨k, v⟩ := by
  sorry

/-- No entry of an absent key. -/
theorem getEntry?_absent {a : α} (habs : s.Absent a) : getEntry? a s.entries = none := by
  sorry

end Model

section Lookup

variable [BEq α] [Hashable α]

/-- **The lookup**: a hit for `a`, whose cells the continuation receives, or a miss, which is an
absence for lawful instances. -/
theorem lookupImpl_cases {σ : Type w} (t : Table α β) (a : α) (f : α → β → σ) (g : Unit → σ) :
    (∃ i k v, t.slots.Hit t.shift a i ∧ t.slotKeys[i]? = some k ∧ t.slotVals[i]? = some v ∧
      lookupImpl t a f g = f k v) ∨
    ((∀ [EquivBEq α] [LawfulHashable α], t.slots.Absent a) ∧ lookupImpl t a f g = g ()) := by
  sorry

/-- *Suggested route.* `lookupMemImpl` takes the lookup's hit. -/
theorem lookupMemImpl_eq {σ : Type w} (t : Table α β) (a : α) (h : containsImpl t a = true)
    (f : α → β → σ) : ∃ i k v, t.slots.Hit t.shift a i ∧ t.slotKeys[i]? = some k ∧
      t.slotVals[i]? = some v ∧ lookupMemImpl t a h f = f k v := by
  sorry

end Lookup

end Swiss

namespace Table

open Swiss

variable {α : Type u} {β : Type v} {γ : Type w} {_ : BEq α} {_ : Hashable α}

theorem distinctKeys [EquivBEq α] [LawfulHashable α] (t : Table α β) :
    DistinctKeys t.toListModel := sorry

theorem size_eq_length (t : Table α β) : t.size = t.toListModel.length := sorry

theorem toListModel_emptyWithCapacity {c : Nat} :
    (emptyWithCapacity c : Table α β).toListModel = [] := sorry

theorem lookup_emptyWithCapacity {σ : Type w} {c : Nat} {a : α} {f : α → β → σ}
    {g : Unit → σ} : (emptyWithCapacity c : Table α β).lookup a f g = g () := sorry

theorem erase_emptyWithCapacity {c : Nat} {a : α} :
    (emptyWithCapacity c : Table α β).erase a = emptyWithCapacity c := sorry

theorem contains_eq_lookup (t : Table α β) (a : α) :
    t.contains a = t.lookup a (fun _ _ => true) (fun _ => false) := sorry

theorem lookup_eq [EquivBEq α] [LawfulHashable α] {σ : Type w} (t : Table α β) (a : α)
    (f : α → β → σ) (g : Unit → σ) :
    t.lookup a f g = (getEntry? a t.toListModel).elim (g ()) (fun e => f e.1 e.2) := sorry

theorem lookupMem_eq [EquivBEq α] [LawfulHashable α] {σ : Type w} (t : Table α β) (a : α)
    (h : t.contains a = true) (f : α → β → σ) {e : (_ : α) × β}
    (he : getEntry? a t.toListModel = some e) : t.lookupMem a h f = f e.1 e.2 := sorry

theorem containsThenInsert_eq (t : Table α β) (a : α) (b : β) :
    t.containsThenInsert a b = (t.contains a, t.insert a b) := sorry

theorem containsThenInsertIfNew_eq (t : Table α β) (a : α) (b : β) :
    t.containsThenInsertIfNew a b = (t.contains a, t.insertIfNew a b) := sorry

theorem getThenInsertIfNew?_eq (t : Table α β) (a : α) (b : β) :
    t.getThenInsertIfNew? a b =
      (t.lookup a (fun _ v => some v) (fun _ => none), t.insertIfNew a b) := sorry

end Table

end OAMap.Core
