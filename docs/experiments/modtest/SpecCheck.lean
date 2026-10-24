import Std
/-! A stub core with the 23 contract signatures (bodies on a list model, lemmas `sorry`),
used only to check that the CoreSpec `example`s of ARCHITECTURE.md §3.4 elaborate. -/
open Std.Internal.List

universe u v w w'

namespace SwissTable.Core

structure Table (α : Type u) (β : Type v) [BEq α] [Hashable α] : Type (max u v) where
  impl : List ((_ : α) × β)

namespace Table
variable {α : Type u} {β : Type v} {γ : Type w} [BEq α] [Hashable α]

def toListModel (t : Table α β) : List ((_ : α) × β) := t.impl
def emptyWithCapacity (_capacity : Nat) : Table α β := ⟨[]⟩
def size (t : Table α β) : Nat := t.impl.length
def numBuckets (t : Table α β) : Nat := t.impl.length
def markLinear (t : Table α β) : Table α β := t
@[inline] def lookup {σ : Type w} (t : Table α β) (a : α) (found : α → β → σ) (missing : Unit → σ) : σ :=
  match getEntry? a t.impl with
  | some e => found e.1 e.2
  | none => missing ()
def contains (t : Table α β) (a : α) : Bool := t.lookup a (fun _ _ => true) (fun _ => false)
@[inline] def lookupMem {σ : Type w} (t : Table α β) (a : α) (_h : t.contains a = true)
    (found : α → β → σ) : σ :=
  match h : getEntry? a t.impl with
  | some e => found e.1 e.2
  | none => by simp [contains, lookup, h] at _h
def insert (t : Table α β) (a : α) (b : β) : Table α β := ⟨insertEntry a b t.impl⟩
def insertIfNew (t : Table α β) (a : α) (b : β) : Table α β := ⟨insertEntryIfNew a b t.impl⟩
def containsThenInsert (t : Table α β) (a : α) (b : β) : Bool × Table α β := (t.contains a, t.insert a b)
def containsThenInsertIfNew (t : Table α β) (a : α) (b : β) : Bool × Table α β := (t.contains a, t.insertIfNew a b)
def getThenInsertIfNew? (t : Table α β) (a : α) (b : β) : Option β × Table α β :=
  (t.lookup a (fun _ v => some v) (fun _ => none), t.insertIfNew a b)
def erase (t : Table α β) (a : α) : Table α β := ⟨eraseKey a t.impl⟩
def alter (t : Table α β) (a : α) (f : Option β → Option β) : Table α β := ⟨Const.alterKey a f t.impl⟩
def modify (t : Table α β) (a : α) (f : β → β) : Table α β := ⟨Const.modifyKey a f t.impl⟩
def filter (f : α → β → Bool) (t : Table α β) : Table α β := ⟨t.impl.filter fun p => f p.1 p.2⟩
def filterMap (f : α → β → Option γ) (t : Table α β) : Table α γ :=
  ⟨t.impl.filterMap fun p => (f p.1 p.2).map (⟨p.1, ·⟩)⟩
def map (f : α → β → γ) (t : Table α β) : Table α γ := ⟨t.impl.map fun p => ⟨p.1, f p.1 p.2⟩⟩
def foldM {ε : Type w} {m : Type w → Type w'} [Monad m] (f : ε → α → β → m ε) (init : ε) (t : Table α β) : m ε :=
  t.impl.foldlM (fun d e => f d e.1 e.2) init
def foldRev {ε : Type w} (f : ε → α → β → ε) (init : ε) (t : Table α β) : ε :=
  t.impl.foldr (fun e d => f d e.1 e.2) init
def forIn {ε : Type w} {m : Type w → Type w'} [Monad m] (f : α → β → ε → m (ForInStep ε)) (init : ε) (t : Table α β) : m ε :=
  ForIn.forIn t.impl init (fun e d => f e.1 e.2 d)

end Table

namespace Table
variable {α : Type u} {β : Type v} {γ : Type w} {_ : BEq α} {_ : Hashable α}
theorem distinctKeys [EquivBEq α] [LawfulHashable α] (t : Table α β) : DistinctKeys t.toListModel := sorry
theorem size_eq_length (t : Table α β) : t.size = t.toListModel.length := sorry
theorem toListModel_emptyWithCapacity {c : Nat} : (emptyWithCapacity c : Table α β).toListModel = [] := sorry
theorem lookup_emptyWithCapacity {σ : Type w} {c : Nat} {a : α} {f : α → β → σ} {g : Unit → σ} :
    (emptyWithCapacity c : Table α β).lookup a f g = g () := sorry
theorem erase_emptyWithCapacity {c : Nat} {a : α} :
    (emptyWithCapacity c : Table α β).erase a = emptyWithCapacity c := sorry
theorem contains_eq_lookup (t : Table α β) (a : α) : t.contains a = t.lookup a (fun _ _ => true) (fun _ => false) := sorry
theorem lookup_eq [EquivBEq α] [LawfulHashable α] {σ : Type w} (t : Table α β) (a : α) (f : α → β → σ) (g : Unit → σ) :
    t.lookup a f g = (getEntry? a t.toListModel).elim (g ()) (fun e => f e.1 e.2) := sorry
theorem lookupMem_eq [EquivBEq α] [LawfulHashable α] {σ : Type w} (t : Table α β) (a : α)
    (h : t.contains a = true) (f : α → β → σ) {e : (_ : α) × β}
    (he : getEntry? a t.toListModel = some e) : t.lookupMem a h f = f e.1 e.2 := sorry
theorem containsThenInsert_eq (t : Table α β) (a : α) (b : β) : t.containsThenInsert a b = (t.contains a, t.insert a b) := sorry
theorem containsThenInsertIfNew_eq (t : Table α β) (a : α) (b : β) : t.containsThenInsertIfNew a b = (t.contains a, t.insertIfNew a b) := sorry
theorem getThenInsertIfNew?_eq (t : Table α β) (a : α) (b : β) :
    t.getThenInsertIfNew? a b = (t.lookup a (fun _ v => some v) (fun _ => none), t.insertIfNew a b) := sorry
theorem toListModel_insert [EquivBEq α] [LawfulHashable α] (t : Table α β) (a : α) (b : β) :
    (t.insert a b).toListModel.Perm (insertEntry a b t.toListModel) := sorry
theorem toListModel_insertIfNew [EquivBEq α] [LawfulHashable α] (t : Table α β) (a : α) (b : β) :
    (t.insertIfNew a b).toListModel.Perm (insertEntryIfNew a b t.toListModel) := sorry
theorem toListModel_erase [EquivBEq α] [LawfulHashable α] (t : Table α β) (a : α) :
    (t.erase a).toListModel.Perm (eraseKey a t.toListModel) := sorry
theorem toListModel_alter [EquivBEq α] [LawfulHashable α] (t : Table α β) (a : α) (f : Option β → Option β) :
    (t.alter a f).toListModel.Perm (Const.alterKey a f t.toListModel) := sorry
theorem toListModel_modify [EquivBEq α] [LawfulHashable α] (t : Table α β) (a : α) (f : β → β) :
    (t.modify a f).toListModel.Perm (Const.modifyKey a f t.toListModel) := sorry
theorem toListModel_filter (t : Table α β) (f : α → β → Bool) :
    (t.filter f).toListModel.Perm (t.toListModel.filter fun p => f p.1 p.2) := sorry
theorem toListModel_filterMap (t : Table α β) (f : α → β → Option γ) :
    (t.filterMap f).toListModel.Perm (t.toListModel.filterMap fun p => (f p.1 p.2).map (⟨p.1, ·⟩)) := sorry
theorem toListModel_map (t : Table α β) (f : α → β → γ) :
    (t.map f).toListModel.Perm (t.toListModel.map fun p => ⟨p.1, f p.1 p.2⟩) := sorry
theorem foldM_eq_foldlM_toListModel {ε : Type w} {m : Type w → Type w'} [Monad m] [LawfulMonad m] (t : Table α β)
    (f : ε → α → β → m ε) (init : ε) : t.foldM f init = t.toListModel.foldlM (fun d e => f d e.1 e.2) init := sorry
theorem foldRev_eq_foldr_toListModel {ε : Type w} (t : Table α β) (f : ε → α → β → ε) (init : ε) :
    t.foldRev f init = t.toListModel.foldr (fun e d => f d e.1 e.2) init := sorry
theorem forIn_eq_forIn_toListModel {ε : Type w} {m : Type w → Type w'} [Monad m] [LawfulMonad m] (t : Table α β)
    (f : α → β → ε → m (ForInStep ε)) (init : ε) :
    t.forIn f init = ForIn.forIn t.toListModel init (fun e d => f e.1 e.2 d) := sorry

-- Derived snippet of §4.1
@[inline] def get? [BEq α] [Hashable α] (t : Table α β) (a : α) : Option β := t.lookup a (fun _ v => some v) (fun _ => none)
theorem get?_eq_getValue? [EquivBEq α] [LawfulHashable α] (t : Table α β) (a : α) :
    t.get? a = getValue? a t.toListModel := by
  unfold get?
  rw [lookup_eq, getValue?_eq_getEntry?]
  cases getEntry? a t.toListModel <;> rfl
theorem getThenInsertIfNew?_fst (t : Table α β) (a : α) (b : β) :
    (t.getThenInsertIfNew? a b).1 = t.get? a := by
  rw [getThenInsertIfNew?_eq]; unfold get?; rfl
end Table
end SwissTable.Core
open SwissTable.Core Std.Internal.List

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
