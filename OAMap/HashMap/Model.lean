module

public import OAMap.HashMap.AdditionalOperations

/-!
# The model bridge

Namespace `OAMap.Model`: the `HashMap`-level forms of the core lemmas (§3.3) and of the
`OAMap.Core.Derived`/`OAMap.Core.Bulk` lemmas, stated against
`OAMap.Model.toListModel m : List ((_ : α) × β)` (defined in `OAMap.HashMap.Basic`). These are
the lemmas `simp_to_model` rewrites with (`OAMap.HashMap.Tactic`), and the vocabulary of every
hand-written proof in `OAMap.HashMap.Lemmas.*` (`docs/ARCHITECTURE.md` §4.4, `docs/proofs.md` §4).

The namespace is outside `OAMap.HashMap`, so the user-facing namespace contains only Std's names.

Rules:

* Every lemma is a one-line application of a core, `Derived` or `Bulk` lemma, or a short proof
  from the lemmas above it. None is proved by `rfl`, so none becomes a definitional (`dsimp`)
  lemma (`proofs.md` §9.8). The core is used only through its contract names, in the shapes of
  `test/OAMapTest/CoreSpec.lean`, so this file is the same for every core.
* **U** lemmas take no hypotheses on `BEq`/`Hashable`, **L** lemmas take
  `[EquivBEq α] [LawfulHashable α]`, exactly as the Table lemma they come from. The map is
  explicit, the keys, values and functions are implicit (`proofs.md` §4).
* There is no bridge from `m₁ == m₂` to `Const.beqModel` (Std's `Raw₀.Const.beq_eq_beqModel`):
  `Const.beqModel` is not `@[expose]`d and cannot be pinned down from Std's public lemmas (see
  `OAMap.Core.Bulk`). The user lemmas about `==` (`Equiv.beq`, `equiv_of_beq`, `beq_iff_equiv`,
  `Equiv.beq_congr`) are proved from `beq_of_perm`, `perm_of_beq`, `beq_congr` and
  `beq_iff_equiv` instead.

Owner: API, Wave 1.
-/

public section

universe u v w w'

variable {α : Type u} {β : Type v} {γ : Type w} {_ : BEq α} {_ : Hashable α}

namespace OAMap.Model

open Std.Internal.List

private theorem ext {m m' : HashMap α β} : m.inner = m'.inner → m = m' := by
  cases m; cases m'; intro h; cases h; exact Eq.refl _

/-! ## The invariant (L) -/

theorem distinctKeys [EquivBEq α] [LawfulHashable α] (m : HashMap α β) :
    DistinctKeys (toListModel m) :=
  m.inner.distinctKeys

/-! ## Size and emptiness (U) -/

theorem size_eq_length (m : HashMap α β) : m.size = (toListModel m).length :=
  m.inner.size_eq_length

theorem isEmpty_eq_isEmpty (m : HashMap α β) : m.isEmpty = (toListModel m).isEmpty :=
  m.inner.isEmpty_eq_isEmpty

theorem isEmpty_eq_size_eq_zero (m : HashMap α β) : m.isEmpty = (m.size == 0) :=
  m.inner.isEmpty_eq_size_eq_zero

/-! ## Queries (L) -/

theorem contains_eq_containsKey [EquivBEq α] [LawfulHashable α] (m : HashMap α β) {a : α} :
    m.contains a = containsKey a (toListModel m) :=
  m.inner.contains_eq_containsKey a

theorem mem_iff_containsKey [EquivBEq α] [LawfulHashable α] (m : HashMap α β) {a : α} :
    a ∈ m ↔ containsKey a (toListModel m) = true := by
  rw [← contains_eq_containsKey]
  exact Iff.rfl

theorem getElem?_eq_getValue? [EquivBEq α] [LawfulHashable α] (m : HashMap α β) {a : α} :
    m[a]? = getValue? a (toListModel m) :=
  m.inner.get?_eq_getValue? a

theorem getElem_eq_getValue [EquivBEq α] [LawfulHashable α] (m : HashMap α β) {a : α}
    {h : a ∈ m} : m[a]'h = getValue a (toListModel m) ((mem_iff_containsKey m).1 h) :=
  m.inner.get_eq_getValue a h

theorem getElem!_eq_getValue! [EquivBEq α] [LawfulHashable α] [Inhabited β] (m : HashMap α β)
    {a : α} : m[a]! = getValue! a (toListModel m) :=
  m.inner.get!_eq_getValue! a

theorem getD_eq_getValueD [EquivBEq α] [LawfulHashable α] (m : HashMap α β) {a : α}
    {fallback : β} : m.getD a fallback = getValueD a (toListModel m) fallback :=
  m.inner.getD_eq_getValueD a fallback

theorem getKey?_eq_getKey? [EquivBEq α] [LawfulHashable α] (m : HashMap α β) {a : α} :
    m.getKey? a = Std.Internal.List.getKey? a (toListModel m) :=
  m.inner.getKey?_eq_getKey? a

theorem getKey_eq_getKey [EquivBEq α] [LawfulHashable α] (m : HashMap α β) {a : α}
    {h : a ∈ m} :
    m.getKey a h = Std.Internal.List.getKey a (toListModel m) ((mem_iff_containsKey m).1 h) :=
  m.inner.getKey_eq_getKey a h

theorem getKey!_eq_getKey! [EquivBEq α] [LawfulHashable α] [Inhabited α] (m : HashMap α β)
    {a : α} : m.getKey! a = Std.Internal.List.getKey! a (toListModel m) :=
  m.inner.getKey!_eq_getKey! a

theorem getKeyD_eq_getKeyD [EquivBEq α] [LawfulHashable α] (m : HashMap α β) {a fallback : α} :
    m.getKeyD a fallback = Std.Internal.List.getKeyD a (toListModel m) fallback :=
  m.inner.getKeyD_eq_getKeyD a fallback

/-! ## The empty map (U) -/

theorem toListModel_emptyWithCapacity {c : Nat} :
    toListModel (HashMap.emptyWithCapacity c : HashMap α β) = [] :=
  Core.Table.toListModel_emptyWithCapacity

theorem toListModel_empty : toListModel (∅ : HashMap α β) = [] :=
  toListModel_emptyWithCapacity

theorem size_emptyWithCapacity {c : Nat} :
    (HashMap.emptyWithCapacity c : HashMap α β).size = 0 :=
  Core.Table.size_emptyWithCapacity

theorem isEmpty_emptyWithCapacity {c : Nat} :
    (HashMap.emptyWithCapacity c : HashMap α β).isEmpty = true :=
  Core.Table.isEmpty_emptyWithCapacity

theorem contains_emptyWithCapacity {c : Nat} {a : α} :
    (HashMap.emptyWithCapacity c : HashMap α β).contains a = false :=
  Core.Table.contains_emptyWithCapacity

theorem getElem?_emptyWithCapacity {c : Nat} {a : α} :
    (HashMap.emptyWithCapacity c : HashMap α β)[a]? = none :=
  Core.Table.get?_emptyWithCapacity

theorem getElem!_emptyWithCapacity [Inhabited β] {c : Nat} {a : α} :
    (HashMap.emptyWithCapacity c : HashMap α β)[a]! = default :=
  Core.Table.get!_emptyWithCapacity

theorem getD_emptyWithCapacity {c : Nat} {a : α} {fallback : β} :
    (HashMap.emptyWithCapacity c : HashMap α β).getD a fallback = fallback :=
  Core.Table.getD_emptyWithCapacity

theorem getKey?_emptyWithCapacity {c : Nat} {a : α} :
    (HashMap.emptyWithCapacity c : HashMap α β).getKey? a = none :=
  Core.Table.getKey?_emptyWithCapacity

theorem getKey!_emptyWithCapacity [Inhabited α] {c : Nat} {a : α} :
    (HashMap.emptyWithCapacity c : HashMap α β).getKey! a = default :=
  Core.Table.getKey!_emptyWithCapacity

theorem getKeyD_emptyWithCapacity {c : Nat} {a fallback : α} :
    (HashMap.emptyWithCapacity c : HashMap α β).getKeyD a fallback = fallback :=
  Core.Table.getKeyD_emptyWithCapacity

theorem toList_emptyWithCapacity {c : Nat} :
    (HashMap.emptyWithCapacity c : HashMap α β).toList = [] :=
  Core.Table.toList_emptyWithCapacity

theorem keys_emptyWithCapacity {c : Nat} :
    (HashMap.emptyWithCapacity c : HashMap α β).keys = [] :=
  Core.Table.keys_emptyWithCapacity

theorem values_emptyWithCapacity {c : Nat} :
    (HashMap.emptyWithCapacity c : HashMap α β).values = [] :=
  Core.Table.values_emptyWithCapacity

/-! ## Iteration (U): every traversal enumerates `toListModel` in order -/

theorem toList_eq_toListModel_map (m : HashMap α β) :
    m.toList = (toListModel m).map fun x => (x.1, x.2) :=
  m.inner.toList_eq_toListModel_map

theorem keys_eq_keys_toListModel (m : HashMap α β) :
    m.keys = Std.Internal.List.keys (toListModel m) :=
  m.inner.keys_eq_keys_toListModel

theorem values_eq_values_toListModel (m : HashMap α β) :
    m.values = Std.Internal.List.values (toListModel m) :=
  m.inner.values_eq_values_toListModel

theorem toArray_eq_toArray_map_toListModel (m : HashMap α β) :
    m.toArray = ((toListModel m).map fun x => (x.1, x.2)).toArray :=
  m.inner.toArray_eq_toArray_map_toListModel

theorem keysArray_eq_toArray_keys_toListModel (m : HashMap α β) :
    m.keysArray = (Std.Internal.List.keys (toListModel m)).toArray :=
  m.inner.keysArray_eq_toArray_keys_toListModel

theorem valuesArray_eq_toArray_values_toListModel (m : HashMap α β) :
    m.valuesArray = (Std.Internal.List.values (toListModel m)).toArray :=
  m.inner.valuesArray_eq_toArray_values_toListModel

theorem fold_eq_foldl_toListModel {δ : Type w} (m : HashMap α β) {f : δ → α → β → δ}
    {init : δ} : m.fold f init = (toListModel m).foldl (fun a b => f a b.1 b.2) init :=
  m.inner.fold_eq_foldl_toListModel f init

theorem foldM_eq_foldlM_toListModel {δ : Type w} {n : Type w → Type w'} [Monad n]
    [LawfulMonad n] (m : HashMap α β) {f : δ → α → β → n δ} {init : δ} :
    m.foldM f init = (toListModel m).foldlM (fun a b => f a b.1 b.2) init :=
  m.inner.foldM_eq_foldlM_toListModel f init

theorem forM_eq_forM_toListModel {n : Type w → Type w'} [Monad n] [LawfulMonad n]
    (m : HashMap α β) {f : α → β → n PUnit} :
    m.forM f = (toListModel m).forM (fun a => f a.1 a.2) :=
  m.inner.forM_eq_forM_toListModel f

theorem forIn_eq_forIn_toListModel {δ : Type w} {n : Type w → Type w'} [Monad n]
    [LawfulMonad n] (m : HashMap α β) {f : α → β → δ → n (ForInStep δ)} {init : δ} :
    m.forIn f init = ForIn.forIn (toListModel m) init (fun a d => f a.1 a.2 d) :=
  m.inner.forIn_eq_forIn_toListModel f init

theorem all_eq_all_toListModel (m : HashMap α β) {p : α → β → Bool} :
    m.all p = (toListModel m).all fun x => p x.1 x.2 :=
  m.inner.all_eq_all_toListModel p

theorem any_eq_any_toListModel (m : HashMap α β) {p : α → β → Bool} :
    m.any p = (toListModel m).any fun x => p x.1 x.2 :=
  m.inner.any_eq_any_toListModel p

/-! ## Operations: the model of the result, up to permutation -/

theorem toListModel_insert [EquivBEq α] [LawfulHashable α] (m : HashMap α β) {a : α} {b : β} :
    (toListModel (m.insert a b)).Perm (insertEntry a b (toListModel m)) :=
  m.inner.toListModel_insert a b

theorem toListModel_insertIfNew [EquivBEq α] [LawfulHashable α] (m : HashMap α β) {a : α}
    {b : β} : (toListModel (m.insertIfNew a b)).Perm (insertEntryIfNew a b (toListModel m)) :=
  m.inner.toListModel_insertIfNew a b

theorem toListModel_erase [EquivBEq α] [LawfulHashable α] (m : HashMap α β) {a : α} :
    (toListModel (m.erase a)).Perm (eraseKey a (toListModel m)) :=
  m.inner.toListModel_erase a

theorem toListModel_alter [EquivBEq α] [LawfulHashable α] (m : HashMap α β) {a : α}
    {f : Option β → Option β} :
    (toListModel (m.alter a f)).Perm (Const.alterKey a f (toListModel m)) :=
  m.inner.toListModel_alter a f

theorem toListModel_modify [EquivBEq α] [LawfulHashable α] (m : HashMap α β) {a : α}
    {f : β → β} : (toListModel (m.modify a f)).Perm (Const.modifyKey a f (toListModel m)) :=
  m.inner.toListModel_modify a f

theorem toListModel_filter (m : HashMap α β) {f : α → β → Bool} :
    (toListModel (m.filter f)).Perm ((toListModel m).filter fun p => f p.1 p.2) :=
  m.inner.toListModel_filter f

theorem toListModel_filterMap (m : HashMap α β) {f : α → β → Option γ} :
    (toListModel (m.filterMap f)).Perm
      ((toListModel m).filterMap fun p => (f p.1 p.2).map (⟨p.1, ·⟩)) :=
  m.inner.toListModel_filterMap f

theorem toListModel_map (m : HashMap α β) {f : α → β → γ} :
    (toListModel (m.map f)).Perm ((toListModel m).map fun p => ⟨p.1, f p.1 p.2⟩) :=
  m.inner.toListModel_map f

/-- A restatement of `mem_of_mem_insertIfNew` matching the proof obligation in the statement of
`HashSet.get_insert` (the one DHashMap lemma Std's HashSet proofs use, `proofs.md` §8). -/
theorem mem_of_mem_insertIfNew' [EquivBEq α] [LawfulHashable α] {m : HashMap α β} {k a : α}
    {v : β} : a ∈ m.insertIfNew k v → ¬((k == a) ∧ ¬k ∈ m) → a ∈ m := by
  simp only [mem_iff_containsKey, containsKey_of_perm (toListModel_insertIfNew m),
    containsKey_insertEntryIfNew, Bool.or_eq_true]
  intro h₁ h₂
  cases hka : k == a
  · simpa [hka] using h₁
  · have hk : containsKey k (toListModel m) = true := Classical.byContradiction fun hk =>
      h₂ ⟨hka, hk⟩
    exact (containsKey_congr hka).symm.trans hk

/-! ## Bulk operations (`OAMap.Core.Bulk`) -/

theorem toListModel_insertMany_list [EquivBEq α] [LawfulHashable α] (m : HashMap α β)
    {l : List (α × β)} :
    (toListModel (m.insertMany l)).Perm (insertListConst (toListModel m) l) :=
  m.inner.toListModel_insertMany_list l

theorem toListModel_insertManyIfNewUnit_list [EquivBEq α] [LawfulHashable α]
    (m : HashMap α Unit) {l : List α} :
    (toListModel (m.insertManyIfNewUnit l)).Perm (insertListIfNewUnit (toListModel m) l) :=
  m.inner.toListModel_insertManyIfNewUnit_list l

theorem toListModel_ofList [EquivBEq α] [LawfulHashable α] {l : List (α × β)} :
    (toListModel (HashMap.ofList l : HashMap α β)).Perm (insertListConst [] l) := by
  have h := (Core.Table.emptyWithCapacity 8 : Core.Table α β).toListModel_insertMany_list l
  rw [Core.Table.toListModel_emptyWithCapacity, ← Core.Table.ofList_eq_insertMany_empty] at h
  exact h

theorem toListModel_unitOfList [EquivBEq α] [LawfulHashable α] {l : List α} :
    (toListModel (HashMap.unitOfList l : HashMap α Unit)).Perm (insertListIfNewUnit [] l) := by
  have h :=
    (Core.Table.emptyWithCapacity 8 : Core.Table α Unit).toListModel_insertManyIfNewUnit_list l
  rw [Core.Table.toListModel_emptyWithCapacity,
    ← Core.Table.unitOfList_eq_insertManyIfNewUnit_empty] at h
  exact h

theorem toListModel_union [EquivBEq α] [LawfulHashable α] (m₁ m₂ : HashMap α β) :
    (toListModel (m₁ ∪ m₂)).Perm (insertList (toListModel m₁) (toListModel m₂)) :=
  m₁.inner.toListModel_union m₂.inner

theorem toListModel_inter [EquivBEq α] [LawfulHashable α] (m₁ m₂ : HashMap α β) :
    (toListModel (m₁ ∩ m₂)).Perm
      ((toListModel m₁).filter fun p => containsKey p.1 (toListModel m₂)) :=
  m₁.inner.toListModel_inter m₂.inner

theorem toListModel_diff [EquivBEq α] [LawfulHashable α] (m₁ m₂ : HashMap α β) :
    (toListModel (m₁ \ m₂)).Perm
      ((toListModel m₁).filter fun k => !((toListModel m₂).map Sigma.fst).contains k.1) :=
  m₁.inner.toListModel_diff m₂.inner

/-- `insertMany` on a list is a left fold of `insert`, as an equality of maps (U). -/
theorem insertMany_list_eq_foldl (m : HashMap α β) {l : List (α × β)} :
    m.insertMany l = l.foldl (fun acc p => acc.insert p.1 p.2) m := by
  apply ext
  show (m.inner.insertMany l).1 = _
  rw [Core.Table.insertMany_list_eq_foldl]
  exact List.foldl_hom HashMap.inner fun _ _ => Eq.refl _

/-- `insertManyIfNewUnit` on a list is a left fold of `insertIfNew`, as an equality of maps (U). -/
theorem insertManyIfNewUnit_list_eq_foldl (m : HashMap α Unit) {l : List α} :
    m.insertManyIfNewUnit l = l.foldl (fun acc a => acc.insertIfNew a ()) m := by
  apply ext
  show (m.inner.insertManyIfNewUnit l).1 = _
  rw [Core.Table.insertManyIfNewUnit_list_eq_foldl]
  exact List.foldl_hom HashMap.inner fun _ _ => Eq.refl _

/-! ## Boolean equality -/

theorem beq_of_perm [EquivBEq α] [LawfulHashable α] [BEq β] [ReflBEq β] {m₁ m₂ : HashMap α β}
    (h : (toListModel m₁).Perm (toListModel m₂)) : (m₁ == m₂) = true :=
  Core.Table.beq_of_perm h

theorem perm_of_beq [LawfulBEq α] [BEq β] [LawfulBEq β] {m₁ m₂ : HashMap α β}
    (h : (m₁ == m₂) = true) : (toListModel m₁).Perm (toListModel m₂) :=
  Core.Table.perm_of_beq h

theorem beq_congr [EquivBEq α] [LawfulHashable α] [BEq β] {m₁ m₂ m₃ m₄ : HashMap α β}
    (h₁ : (toListModel m₁).Perm (toListModel m₃)) (h₂ : (toListModel m₂).Perm (toListModel m₄)) :
    (m₁ == m₂) = (m₃ == m₄) :=
  Core.Table.beq_congr h₁ h₂

/-! ## Equivalence (U) -/

theorem equiv_iff_toListModel_perm {m₁ m₂ : HashMap α β} :
    m₁.Equiv m₂ ↔ (toListModel m₁).Perm (toListModel m₂) :=
  ⟨fun h => h.1, fun h => ⟨h⟩⟩

theorem beq_iff_equiv [LawfulBEq α] [BEq β] [LawfulBEq β] {m₁ m₂ : HashMap α β} :
    (m₁ == m₂) = true ↔ m₁.Equiv m₂ :=
  ⟨fun h => ⟨perm_of_beq h⟩, fun h => beq_of_perm h.1⟩

/-! ## Congruence lemmas for `simp_to_model` (Std's private `perm_map_congr_left` and
`perm_keys_congr_left` of `RawLemmas.lean`, public here because the tactic's expansions in other
modules refer to them) -/

theorem perm_map_congr_left {α : Type u} {β : Type v} {l l' : List α} {f : α → β}
    {l₂ : List β} (h : l.Perm l') : (l.map f).Perm l₂ ↔ (l'.map f).Perm l₂ :=
  (h.map f).congr_left _

theorem perm_keys_congr_left {α : Type u} {β : α → Type v} {l l' : List ((a : α) × β a)}
    {l₂ : List α} (h : l.Perm l') :
    (Std.Internal.List.keys l).Perm l₂ ↔ (Std.Internal.List.keys l').Perm l₂ := by
  rw [keys_eq_map, keys_eq_map]
  exact perm_map_congr_left h

end OAMap.Model
