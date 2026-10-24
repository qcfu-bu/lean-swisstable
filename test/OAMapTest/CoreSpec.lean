import OAMap.Core.Table

/-!
# The core contract as a test

This file compiles exactly when the core selected by `OAMap.Core.Table` provides the 23
definitions and 22 lemmas of `docs/ARCHITECTURE.md` §3, each with a type at least as general as
the one below. It is the acceptance test for a core: run `lake build OAMapTest.CoreSpec` (or
`lake test`). The text is §3.4 verbatim.
-/

open OAMap.Core Std.Internal.List

universe u v w w'
variable {α : Type u} {β : Type v} {γ : Type w}

/-! ## Definitions -/
example : (α : Type u) → (β : Type v) → [BEq α] → [Hashable α] → Type (max u v) := @Table
section
variable [BEq α] [Hashable α]
example : Table α β → List ((_ : α) × β) := Table.toListModel
example : Nat → Table α β := Table.emptyWithCapacity
example : Table α β → Nat := Table.size
example : Table α β → Nat := Table.numBuckets
example : Table α β → Table α β := Table.markLinear
example {σ : Type w} : Table α β → α → (α → β → σ) → (Unit → σ) → σ := Table.lookup
example : Table α β → α → Bool := Table.contains
example {σ : Type w} : (t : Table α β) → (a : α) → t.contains a = true → (α → β → σ) → σ :=
  Table.lookupMem
example : Table α β → α → β → Table α β := Table.insert
example : Table α β → α → β → Table α β := Table.insertIfNew
example : Table α β → α → β → Bool × Table α β := Table.containsThenInsert
example : Table α β → α → β → Bool × Table α β := Table.containsThenInsertIfNew
example : Table α β → α → β → Option β × Table α β := Table.getThenInsertIfNew?
example : Table α β → α → Table α β := Table.erase
example : Table α β → α → (Option β → Option β) → Table α β := Table.alter
example : Table α β → α → (β → β) → Table α β := Table.modify
example : (α → β → Bool) → Table α β → Table α β := Table.filter
example : (α → β → Option γ) → Table α β → Table α γ := Table.filterMap
example : (α → β → γ) → Table α β → Table α γ := Table.map
example {ε : Type w} {m : Type w → Type w'} [Monad m] :
    (ε → α → β → m ε) → ε → Table α β → m ε := Table.foldM
example {ε : Type w} : (ε → α → β → ε) → ε → Table α β → ε := Table.foldRev
example {ε : Type w} {m : Type w → Type w'} [Monad m] :
    (α → β → ε → m (ForInStep ε)) → ε → Table α β → m ε := Table.forIn
end

/-! ## Lemmas -/
section
variable {_ : BEq α} {_ : Hashable α}

example [EquivBEq α] [LawfulHashable α] (t : Table α β) : DistinctKeys t.toListModel :=
  t.distinctKeys
example (t : Table α β) : t.size = t.toListModel.length := t.size_eq_length
example {c : Nat} : (Table.emptyWithCapacity c : Table α β).toListModel = [] :=
  Table.toListModel_emptyWithCapacity
example {σ : Type w} {c : Nat} {a : α} {f : α → β → σ} {g : Unit → σ} :
    (Table.emptyWithCapacity c : Table α β).lookup a f g = g () := Table.lookup_emptyWithCapacity
example {c : Nat} {a : α} :
    (Table.emptyWithCapacity c : Table α β).erase a = Table.emptyWithCapacity c :=
  Table.erase_emptyWithCapacity
example (t : Table α β) (a : α) : t.contains a = t.lookup a (fun _ _ => true) (fun _ => false) :=
  t.contains_eq_lookup a
example [EquivBEq α] [LawfulHashable α] {σ : Type w} (t : Table α β) (a : α)
    (f : α → β → σ) (g : Unit → σ) :
    t.lookup a f g = (getEntry? a t.toListModel).elim (g ()) (fun e => f e.1 e.2) :=
  t.lookup_eq a f g
example [EquivBEq α] [LawfulHashable α] {σ : Type w} (t : Table α β) (a : α)
    (h : t.contains a = true) (f : α → β → σ) {e : (_ : α) × β}
    (he : getEntry? a t.toListModel = some e) : t.lookupMem a h f = f e.1 e.2 :=
  t.lookupMem_eq a h f he
example (t : Table α β) (a : α) (b : β) :
    t.containsThenInsert a b = (t.contains a, t.insert a b) := t.containsThenInsert_eq a b
example (t : Table α β) (a : α) (b : β) :
    t.containsThenInsertIfNew a b = (t.contains a, t.insertIfNew a b) :=
  t.containsThenInsertIfNew_eq a b
example (t : Table α β) (a : α) (b : β) :
    t.getThenInsertIfNew? a b =
      (t.lookup a (fun _ v => some v) (fun _ => none), t.insertIfNew a b) :=
  t.getThenInsertIfNew?_eq a b
example [EquivBEq α] [LawfulHashable α] (t : Table α β) (a : α) (b : β) :
    (t.insert a b).toListModel.Perm (insertEntry a b t.toListModel) := t.toListModel_insert a b
example [EquivBEq α] [LawfulHashable α] (t : Table α β) (a : α) (b : β) :
    (t.insertIfNew a b).toListModel.Perm (insertEntryIfNew a b t.toListModel) :=
  t.toListModel_insertIfNew a b
example [EquivBEq α] [LawfulHashable α] (t : Table α β) (a : α) :
    (t.erase a).toListModel.Perm (eraseKey a t.toListModel) := t.toListModel_erase a
example [EquivBEq α] [LawfulHashable α] (t : Table α β) (a : α) (f : Option β → Option β) :
    (t.alter a f).toListModel.Perm (Const.alterKey a f t.toListModel) := t.toListModel_alter a f
example [EquivBEq α] [LawfulHashable α] (t : Table α β) (a : α) (f : β → β) :
    (t.modify a f).toListModel.Perm (Const.modifyKey a f t.toListModel) := t.toListModel_modify a f
example (t : Table α β) (f : α → β → Bool) :
    (t.filter f).toListModel.Perm (t.toListModel.filter fun p => f p.1 p.2) :=
  t.toListModel_filter f
example (t : Table α β) (f : α → β → Option γ) :
    (t.filterMap f).toListModel.Perm
      (t.toListModel.filterMap fun p => (f p.1 p.2).map (⟨p.1, ·⟩)) := t.toListModel_filterMap f
example (t : Table α β) (f : α → β → γ) :
    (t.map f).toListModel.Perm (t.toListModel.map fun p => ⟨p.1, f p.1 p.2⟩) :=
  t.toListModel_map f
example {ε : Type w} {m : Type w → Type w'} [Monad m] [LawfulMonad m] (t : Table α β)
    (f : ε → α → β → m ε) (init : ε) :
    t.foldM f init = t.toListModel.foldlM (fun d e => f d e.1 e.2) init :=
  t.foldM_eq_foldlM_toListModel f init
example {ε : Type w} (t : Table α β) (f : ε → α → β → ε) (init : ε) :
    t.foldRev f init = t.toListModel.foldr (fun e d => f d e.1 e.2) init :=
  t.foldRev_eq_foldr_toListModel f init
example {ε : Type w} {m : Type w → Type w'} [Monad m] [LawfulMonad m] (t : Table α β)
    (f : α → β → ε → m (ForInStep ε)) (init : ε) :
    t.forIn f init = ForIn.forIn t.toListModel init (fun e d => f e.1 e.2 d) :=
  t.forIn_eq_forIn_toListModel f init
end
