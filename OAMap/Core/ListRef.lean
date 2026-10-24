module

public import Std.Data.Internal.List.Associative

/-!
# The list-backed reference core

This module implements the core contract of `docs/ARCHITECTURE.md` §3 (23 definitions and 22
lemmas in namespace `OAMap.Core.Table`) on an association list. It is the core that
`OAMap.Core.Table` selects until the layout chosen by the bake-off passes
`test/OAMapTest/CoreSpec.lean`, and every layer above the core is developed and proved against it.

Design rules (ARCHITECTURE.md §2.3, §3.6):

* The section is `public` but not `@[expose]`d, so importing modules see the statements but cannot
  unfold the definitions. The one exception is `markLinear`, which must be exposed so that
  `HashMap.markLinear_eq` holds by `rfl`.
* The constructor and the fields of `Table` are private: code above the core can only reach a
  table through the contract names.
* Every lemma is proved by `unfold`, never by a bare `rfl`, so none of them becomes a
  definitional (`dsimp`) lemma.
* Every lemma states exactly the hypotheses of the contract, including the lawfulness instances
  of the L lemmas even where this list model does not need them. A proof above the core that
  checks against this core therefore checks against any core that satisfies the contract.
-/

public section

universe u v w w'

open Std.Internal.List

namespace OAMap.Core

/-- The reference table: an association list whose keys are distinct whenever the `BEq` and
`Hashable` instances are lawful. Only the contract operations below can build or inspect it. -/
structure Table (α : Type u) (β : Type v) [BEq α] [Hashable α] : Type (max u v) where
  private mk ::
  /-- The entries, in iteration order. -/
  private impl : List ((_ : α) × β)
  /-- The keys are distinct under lawful instances. -/
  private distinct : ∀ [EquivBEq α] [LawfulHashable α], DistinctKeys impl

namespace Table

/-! ## The 23 primitive definitions -/

section Defs

variable {α : Type u} {β : Type v} {γ : Type w} [BEq α] [Hashable α]

/-- The entries of the table, in iteration order. -/
def toListModel (t : Table α β) : List ((_ : α) × β) :=
  t.impl

/-- The empty table. The list model ignores the capacity hint. -/
def emptyWithCapacity (_capacity : Nat) : Table α β :=
  ⟨[], DistinctKeys.nil⟩

/-- The number of entries. -/
def size (t : Table α β) : Nat :=
  t.impl.length

/-- The number of buckets: the list model is a single bucket. -/
def numBuckets (_t : Table α β) : Nat :=
  1

/-- The identity; a hint to the compiler that the table is used linearly. -/
@[expose] def markLinear (t : Table α β) : Table α β :=
  t

/-- One probe for `a`: `found k v` on the stored key and value, `missing ()` otherwise. -/
@[inline] def lookup {σ : Type w} (t : Table α β) (a : α) (found : α → β → σ)
    (missing : Unit → σ) : σ :=
  match getEntry? a t.impl with
  | some e => found e.1 e.2
  | none => missing ()

/-- Whether some stored key is `==` to `a`. -/
def contains (t : Table α β) (a : α) : Bool :=
  containsKey a t.impl

/-- One probe for a key known to be present: `found k v` on the stored key and value. -/
@[inline] def lookupMem {σ : Type w} (t : Table α β) (a : α) (h : t.contains a = true)
    (found : α → β → σ) : σ :=
  match he : getEntry? a t.impl with
  | some e => found e.1 e.2
  | none => absurd h (by
      unfold contains
      rw [getEntry?_eq_none.1 he]
      exact Bool.false_ne_true)

/-- Inserts `a ↦ b`, replacing the stored key and value if `a` is present. -/
def insert (t : Table α β) (a : α) (b : β) : Table α β :=
  ⟨insertEntry a b t.impl, t.distinct.insertEntry⟩

/-- Inserts `a ↦ b` if `a` is absent; otherwise returns the table unchanged. -/
def insertIfNew (t : Table α β) (a : α) (b : β) : Table α β :=
  ⟨insertEntryIfNew a b t.impl, t.distinct.insertEntryIfNew⟩

/-- `insert`, also returning whether `a` was present before. -/
def containsThenInsert (t : Table α β) (a : α) (b : β) : Bool × Table α β :=
  (t.contains a, t.insert a b)

/-- `insertIfNew`, also returning whether `a` was present before. -/
def containsThenInsertIfNew (t : Table α β) (a : α) (b : β) : Bool × Table α β :=
  (t.contains a, t.insertIfNew a b)

/-- `insertIfNew`, also returning the value stored for `a` before, if any. -/
def getThenInsertIfNew? (t : Table α β) (a : α) (b : β) : Option β × Table α β :=
  (t.lookup a (fun _ v => some v) (fun _ => none), t.insertIfNew a b)

/-- Removes the entry for `a`, if any. -/
def erase (t : Table α β) (a : α) : Table α β :=
  ⟨eraseKey a t.impl, t.distinct.eraseKey⟩

/-- Replaces the value `v?` stored for `a` (`none` if absent) by `f v?`; `none` removes it. -/
def alter (t : Table α β) (a : α) (f : Option β → Option β) : Table α β :=
  ⟨Const.alterKey a f t.impl, t.distinct.constAlterKey⟩

/-- Applies `f` to the value stored for `a`, if any, keeping the stored key. -/
def modify (t : Table α β) (a : α) (f : β → β) : Table α β :=
  ⟨Const.modifyKey a f t.impl, t.distinct.constModifyKey⟩

/-- Keeps the entries that satisfy `f`. -/
def filter (f : α → β → Bool) (t : Table α β) : Table α β :=
  ⟨t.impl.filter fun p => f p.1 p.2, t.distinct.filter⟩

/-- Maps the values through `f`, dropping the entries where `f` returns `none`. -/
def filterMap (f : α → β → Option γ) (t : Table α β) : Table α γ :=
  ⟨t.impl.filterMap fun p => (f p.1 p.2).map (⟨p.1, ·⟩), t.distinct.filterMap⟩

/-- Maps the values through `f`. -/
def map (f : α → β → γ) (t : Table α β) : Table α γ :=
  ⟨t.impl.map fun p => ⟨p.1, f p.1 p.2⟩, t.distinct.map⟩

/-- Monadic left fold over the entries, in model order. -/
def foldM {ε : Type w} {m : Type w → Type w'} [Monad m] (f : ε → α → β → m ε) (init : ε)
    (t : Table α β) : m ε :=
  t.impl.foldlM (fun d e => f d e.1 e.2) init

/-- Right fold over the entries: `f` sees them in reverse model order. -/
def foldRev {ε : Type w} (f : ε → α → β → ε) (init : ε) (t : Table α β) : ε :=
  t.impl.foldr (fun e d => f d e.1 e.2) init

/-- Monadic loop over the entries in model order, with early exit. -/
def forIn {ε : Type w} {m : Type w → Type w'} [Monad m] (f : α → β → ε → m (ForInStep ε))
    (init : ε) (t : Table α β) : m ε :=
  ForIn.forIn t.impl init (fun e d => f e.1 e.2 d)

end Defs

/-! ## The 22 primitive lemmas -/

section Lemmas

variable {α : Type u} {β : Type v} {γ : Type w} {_ : BEq α} {_ : Hashable α}

theorem distinctKeys [EquivBEq α] [LawfulHashable α] (t : Table α β) :
    DistinctKeys t.toListModel := by
  unfold toListModel
  exact t.distinct

theorem size_eq_length (t : Table α β) : t.size = t.toListModel.length := by
  unfold size toListModel
  exact Eq.refl _

theorem toListModel_emptyWithCapacity {c : Nat} :
    (emptyWithCapacity c : Table α β).toListModel = [] := by
  unfold emptyWithCapacity toListModel
  exact Eq.refl _

theorem lookup_emptyWithCapacity {σ : Type w} {c : Nat} {a : α} {f : α → β → σ}
    {g : Unit → σ} : (emptyWithCapacity c : Table α β).lookup a f g = g () := by
  unfold lookup emptyWithCapacity
  simp only [getEntry?_nil]

theorem erase_emptyWithCapacity {c : Nat} {a : α} :
    (emptyWithCapacity c : Table α β).erase a = emptyWithCapacity c := by
  unfold erase emptyWithCapacity
  simp only [eraseKey_nil]

theorem contains_eq_lookup (t : Table α β) (a : α) :
    t.contains a = t.lookup a (fun _ _ => true) (fun _ => false) := by
  unfold contains lookup
  rw [containsKey_eq_isSome_getEntry?]
  cases getEntry? a t.impl <;> exact Eq.refl _

theorem lookup_eq [EquivBEq α] [LawfulHashable α] {σ : Type w} (t : Table α β) (a : α)
    (f : α → β → σ) (g : Unit → σ) :
    t.lookup a f g = (getEntry? a t.toListModel).elim (g ()) (fun e => f e.1 e.2) := by
  unfold lookup toListModel
  cases getEntry? a t.impl <;> exact Eq.refl _

theorem lookupMem_eq [EquivBEq α] [LawfulHashable α] {σ : Type w} (t : Table α β) (a : α)
    (h : t.contains a = true) (f : α → β → σ) {e : (_ : α) × β}
    (he : getEntry? a t.toListModel = some e) : t.lookupMem a h f = f e.1 e.2 := by
  unfold toListModel at he
  unfold lookupMem
  split
  · rename_i e' he'
    rw [he] at he'
    cases he'
    exact Eq.refl _
  · rename_i he'
    rw [he] at he'
    cases he'

theorem containsThenInsert_eq (t : Table α β) (a : α) (b : β) :
    t.containsThenInsert a b = (t.contains a, t.insert a b) := by
  unfold containsThenInsert
  exact Eq.refl _

theorem containsThenInsertIfNew_eq (t : Table α β) (a : α) (b : β) :
    t.containsThenInsertIfNew a b = (t.contains a, t.insertIfNew a b) := by
  unfold containsThenInsertIfNew
  exact Eq.refl _

theorem getThenInsertIfNew?_eq (t : Table α β) (a : α) (b : β) :
    t.getThenInsertIfNew? a b =
      (t.lookup a (fun _ v => some v) (fun _ => none), t.insertIfNew a b) := by
  unfold getThenInsertIfNew?
  exact Eq.refl _

theorem toListModel_insert [EquivBEq α] [LawfulHashable α] (t : Table α β) (a : α) (b : β) :
    (t.insert a b).toListModel.Perm (insertEntry a b t.toListModel) := by
  unfold insert toListModel
  exact List.Perm.refl _

theorem toListModel_insertIfNew [EquivBEq α] [LawfulHashable α] (t : Table α β) (a : α)
    (b : β) : (t.insertIfNew a b).toListModel.Perm (insertEntryIfNew a b t.toListModel) := by
  unfold insertIfNew toListModel
  exact List.Perm.refl _

theorem toListModel_erase [EquivBEq α] [LawfulHashable α] (t : Table α β) (a : α) :
    (t.erase a).toListModel.Perm (eraseKey a t.toListModel) := by
  unfold erase toListModel
  exact List.Perm.refl _

theorem toListModel_alter [EquivBEq α] [LawfulHashable α] (t : Table α β) (a : α)
    (f : Option β → Option β) :
    (t.alter a f).toListModel.Perm (Const.alterKey a f t.toListModel) := by
  unfold alter toListModel
  exact List.Perm.refl _

theorem toListModel_modify [EquivBEq α] [LawfulHashable α] (t : Table α β) (a : α)
    (f : β → β) : (t.modify a f).toListModel.Perm (Const.modifyKey a f t.toListModel) := by
  unfold modify toListModel
  exact List.Perm.refl _

theorem toListModel_filter (t : Table α β) (f : α → β → Bool) :
    (t.filter f).toListModel.Perm (t.toListModel.filter fun p => f p.1 p.2) := by
  unfold filter toListModel
  exact List.Perm.refl _

theorem toListModel_filterMap (t : Table α β) (f : α → β → Option γ) :
    (t.filterMap f).toListModel.Perm
      (t.toListModel.filterMap fun p => (f p.1 p.2).map (⟨p.1, ·⟩)) := by
  unfold filterMap toListModel
  exact List.Perm.refl _

theorem toListModel_map (t : Table α β) (f : α → β → γ) :
    (t.map f).toListModel.Perm (t.toListModel.map fun p => ⟨p.1, f p.1 p.2⟩) := by
  unfold map toListModel
  exact List.Perm.refl _

theorem foldM_eq_foldlM_toListModel {ε : Type w} {m : Type w → Type w'} [Monad m]
    [LawfulMonad m] (t : Table α β) (f : ε → α → β → m ε) (init : ε) :
    t.foldM f init = t.toListModel.foldlM (fun d e => f d e.1 e.2) init := by
  unfold foldM toListModel
  exact Eq.refl _

theorem foldRev_eq_foldr_toListModel {ε : Type w} (t : Table α β) (f : ε → α → β → ε)
    (init : ε) : t.foldRev f init = t.toListModel.foldr (fun e d => f d e.1 e.2) init := by
  unfold foldRev toListModel
  exact Eq.refl _

theorem forIn_eq_forIn_toListModel {ε : Type w} {m : Type w → Type w'} [Monad m]
    [LawfulMonad m] (t : Table α β) (f : α → β → ε → m (ForInStep ε)) (init : ε) :
    t.forIn f init = ForIn.forIn t.toListModel init (fun e d => f e.1 e.2 d) := by
  unfold forIn toListModel
  exact Eq.refl _

end Lemmas

end Table

end OAMap.Core
