module

public import OAMap.Core.Derived

/-!
# Std's bulk algorithms on the core

`insertMany`, `insertManyIfNewUnit`, `ofList`, `ofArray`, `unitOfList`, `unitOfArray`, `union`,
`inter`, `diff`, `beq` and `partition`, transcribed from Std (`Std.Data.DHashMap.Internal.Defs`,
`Std.Data.DHashMap.Basic`) onto the core primitives, with their Table-level model lemmas and the
Table-level twins of Std's structural equalities (`docs/ARCHITECTURE.md` §4.2, §6.3).

* `insertMany` and `insertManyIfNewUnit` are Std's `for` loops whose state carries its own
  induction principle, so `insertMany_ind` holds for every `ForIn` instance. `ofList`, `ofArray`,
  `unitOfList` and `unitOfArray` start from `emptyWithCapacity 8` (the table behind `∅`) with no
  presizing, as Std's do, so the user-level equalities (`ofList_cons`, `ofArray_eq_ofList`, ...)
  hold as equalities of maps.
* `union`, `inter` and `diff` keep Std's size branches (merge the smaller map into the larger);
  `beq` is Std's size check followed by `all`/`get?`; `partition` is Std's fold.

Layout-free: uses only the contract names of `OAMap.Core.Table` and the definitions and lemmas of
`OAMap.Core.Derived`. Not exposed. The twins of Std's `ext DHashMap.X` equalities take all their
arguments implicitly (except where Std's take them explicitly), so that `ext Core.Table.X` and
`apply Core.Table.X` elaborate as in Std.

Two statements are left as `sorry` because the public API of `Std.Internal.List` cannot prove
them: `toListModel_insertMany_list` needs the defining equations of `insertListConst`, and
`beq_eq_beqModel` needs the definition of `Const.beqModel`. Neither definition is `@[expose]`d,
and `import all` is forbidden here. The docstrings of the two lemmas give the details.

Owner: GEN, Wave 1.
-/

public section

universe u v w

open Std.Internal.List

namespace OAMap.Core.Table

/-! ## Definitions -/

section Defs

variable {α : Type u} {β : Type v} [BEq α] [Hashable α]

/-- Inserts every pair of `l`, in iteration order, with `insert` (the last occurrence of a key
wins). The loop state carries the induction principle `insertMany_ind` (Std's construction). -/
def insertMany {ρ : Type w} [ForIn Id ρ (α × β)] (t : Table α β) (l : ρ) :
    { t' : Table α β // ∀ (P : Table α β → Prop),
      (∀ {t'' a b}, P t'' → P (t''.insert a b)) → P t → P t' } := Id.run do
  let mut r : { t' : Table α β // ∀ (P : Table α β → Prop),
    (∀ {t'' a b}, P t'' → P (t''.insert a b)) → P t → P t' } := ⟨t, fun _ _ => id⟩
  for (a, b) in l do
    r := ⟨r.1.insert a b, fun _ h hm => h (r.2 _ h hm)⟩
  return r

/-- Inserts every key of `l` with value `()`, in iteration order, with `insertIfNew` (the first
occurrence of a key wins). The loop state carries the induction principle
`insertManyIfNewUnit_ind` (Std's construction). -/
def insertManyIfNewUnit {ρ : Type w} [ForIn Id ρ α] (t : Table α Unit) (l : ρ) :
    { t' : Table α Unit // ∀ (P : Table α Unit → Prop),
      (∀ {t'' a b}, P t'' → P (t''.insertIfNew a b)) → P t → P t' } := Id.run do
  let mut r : { t' : Table α Unit // ∀ (P : Table α Unit → Prop),
    (∀ {t'' a b}, P t'' → P (t''.insertIfNew a b)) → P t → P t' } := ⟨t, fun _ _ => id⟩
  for a in l do
    r := ⟨r.1.insertIfNew a (), fun _ h hm => h (r.2 _ h hm)⟩
  return r

/-- The table of the pairs of `l` (the last occurrence of a key wins). -/
@[inline] def ofList (l : List (α × β)) : Table α β :=
  (insertMany (emptyWithCapacity 8) l).1

/-- The table of the pairs of `l` (the last occurrence of a key wins). -/
@[inline] def ofArray (l : Array (α × β)) : Table α β :=
  (insertMany (emptyWithCapacity 8) l).1

/-- The table of the keys of `l` with value `()` (the first occurrence of a key wins). -/
@[inline] def unitOfList (l : List α) : Table α Unit :=
  (insertManyIfNewUnit (emptyWithCapacity 8) l).1

/-- The table of the keys of `l` with value `()` (the first occurrence of a key wins). -/
@[inline] def unitOfArray (l : Array α) : Table α Unit :=
  (insertManyIfNewUnit (emptyWithCapacity 8) l).1

/-- The union, right-biased: an entry of `t₂` replaces the entry of `t₁` for the same key. The
smaller table is merged into the larger one (Std's `Raw₀.union`). -/
@[inline] def union (t₁ t₂ : Table α β) : Table α β :=
  if t₁.size ≤ t₂.size then t₁.fold (fun acc k v => acc.insertIfNew k v) t₂
  else t₂.fold (fun acc k v => acc.insert k v) t₁

/-- The entries of `t₁` whose key is in `t₂` (Std's `Raw₀.inter`: filter the smaller table, or
look up the keys of the smaller one in the larger one). -/
def inter (t₁ t₂ : Table α β) : Table α β :=
  if t₁.size ≤ t₂.size then t₁.filter fun k _ => t₂.contains k
  else t₂.fold (fun acc k _ => t₁.lookup k (fun k' v' => acc.insert k' v') (fun _ => acc))
    (emptyWithCapacity 8)

/-- The entries of `t₁` whose key is not in `t₂` (Std's `Raw₀.diff`: filter `t₁`, or erase the
keys of `t₂` from it). -/
@[inline] def diff (t₁ t₂ : Table α β) : Table α β :=
  if t₁.size ≤ t₂.size then t₁.filter fun k _ => !t₂.contains k
  else t₂.fold (fun acc k _ => acc.erase k) t₁

/-- Boolean equality of tables: same size, and every entry of `t₁` is in `t₂` (Std's
`Raw₀.Const.beq`). -/
def beq [BEq β] (t₁ t₂ : Table α β) : Bool :=
  if t₁.size ≠ t₂.size then false else t₁.all fun k v => t₂.get? k == some v

/-- Splits a table by a predicate: the entries satisfying `f`, and the others (Std's
`DHashMap.partition`). -/
@[inline] def partition (f : α → β → Bool) (t : Table α β) : Table α β × Table α β :=
  t.fold (fun ⟨l, r⟩ k v => if f k v then (l.insert k v, r) else (l, r.insert k v))
    (emptyWithCapacity 8, emptyWithCapacity 8)

end Defs

/-! ## Lemmas -/

section Lemmas

variable {α : Type u} {β : Type v} {_ : BEq α} {_ : Hashable α}

/-! ### The loops as left folds (U) -/

theorem insertMany_list_eq_foldl {t : Table α β} {l : List (α × β)} :
    (t.insertMany l).1 = l.foldl (fun acc p => acc.insert p.1 p.2) t := by
  unfold insertMany
  simpa using (List.foldl_hom Subtype.val (fun _ _ => Eq.refl _)).symm

theorem insertManyIfNewUnit_list_eq_foldl {t : Table α Unit} {l : List α} :
    (t.insertManyIfNewUnit l).1 = l.foldl (fun acc a => acc.insertIfNew a ()) t := by
  unfold insertManyIfNewUnit
  simpa using (List.foldl_hom Subtype.val (fun _ _ => Eq.refl _)).symm

/-! ### Induction principles (U) -/

theorem insertMany_ind {ρ : Type w} [ForIn Id ρ (α × β)] {motive : Table α β → Prop}
    (t : Table α β) (l : ρ) (init : motive t)
    (insert : ∀ t a b, motive t → motive (t.insert a b)) : motive (t.insertMany l).1 :=
  (t.insertMany l).2 motive (fun h => insert _ _ _ h) init

theorem insertManyIfNewUnit_ind {ρ : Type w} [ForIn Id ρ α] {motive : Table α Unit → Prop}
    (t : Table α Unit) (l : ρ) (init : motive t)
    (insert : ∀ t a, motive t → motive (t.insertIfNew a ())) :
    motive (t.insertManyIfNewUnit l).1 :=
  (t.insertManyIfNewUnit l).2 motive (fun h => insert _ _ h) init

/-! ### Twins of Std's structural equalities (U, implicit arguments) -/

theorem insertMany_nil {t : Table α β} : (t.insertMany ([] : List (α × β))).1 = t := by
  rw [insertMany_list_eq_foldl, List.foldl_nil]

theorem insertMany_list_singleton {t : Table α β} {k : α} {v : β} :
    (t.insertMany [(k, v)]).1 = t.insert k v := by
  rw [insertMany_list_eq_foldl, List.foldl_cons, List.foldl_nil]

theorem insertMany_cons {t : Table α β} {l : List (α × β)} {k : α} {v : β} :
    (t.insertMany ((k, v) :: l)).1 = ((t.insert k v).insertMany l).1 := by
  rw [insertMany_list_eq_foldl, insertMany_list_eq_foldl, List.foldl_cons]

theorem insertManyIfNewUnit_nil {t : Table α Unit} :
    (t.insertManyIfNewUnit ([] : List α)).1 = t := by
  rw [insertManyIfNewUnit_list_eq_foldl, List.foldl_nil]

theorem insertManyIfNewUnit_list_singleton {t : Table α Unit} {k : α} :
    (t.insertManyIfNewUnit [k]).1 = t.insertIfNew k () := by
  rw [insertManyIfNewUnit_list_eq_foldl, List.foldl_cons, List.foldl_nil]

theorem insertManyIfNewUnit_cons {t : Table α Unit} {l : List α} {k : α} :
    (t.insertManyIfNewUnit (k :: l)).1 = ((t.insertIfNew k ()).insertManyIfNewUnit l).1 := by
  rw [insertManyIfNewUnit_list_eq_foldl, insertManyIfNewUnit_list_eq_foldl, List.foldl_cons]

theorem ofList_eq_insertMany_empty {l : List (α × β)} :
    ofList l = ((emptyWithCapacity 8 : Table α β).insertMany l).1 := by
  unfold ofList
  exact Eq.refl _

theorem ofList_nil : ofList ([] : List (α × β)) = (emptyWithCapacity 8 : Table α β) := by
  rw [ofList_eq_insertMany_empty, insertMany_nil]

theorem ofList_singleton {k : α} {v : β} :
    ofList [(k, v)] = (emptyWithCapacity 8 : Table α β).insert k v := by
  rw [ofList_eq_insertMany_empty, insertMany_list_singleton]

theorem ofList_cons {k : α} {v : β} {tl : List (α × β)} :
    ofList ((k, v) :: tl) = (((emptyWithCapacity 8 : Table α β).insert k v).insertMany tl).1 := by
  rw [ofList_eq_insertMany_empty, insertMany_cons]

theorem ofArray_eq_ofList (a : Array (α × β)) : (ofArray a : Table α β) = ofList a.toList := by
  unfold ofArray ofList insertMany
  simp only [Array.forIn_toList]

theorem unitOfList_eq_insertManyIfNewUnit_empty {l : List α} :
    unitOfList l = ((emptyWithCapacity 8 : Table α Unit).insertManyIfNewUnit l).1 := by
  unfold unitOfList
  exact Eq.refl _

theorem unitOfList_nil : unitOfList ([] : List α) = (emptyWithCapacity 8 : Table α Unit) := by
  rw [unitOfList_eq_insertManyIfNewUnit_empty, insertManyIfNewUnit_nil]

theorem unitOfList_singleton {k : α} :
    unitOfList [k] = (emptyWithCapacity 8 : Table α Unit).insertIfNew k () := by
  rw [unitOfList_eq_insertManyIfNewUnit_empty, insertManyIfNewUnit_list_singleton]

theorem unitOfList_cons {hd : α} {tl : List α} :
    unitOfList (hd :: tl) =
      (((emptyWithCapacity 8 : Table α Unit).insertIfNew hd ()).insertManyIfNewUnit tl).1 := by
  rw [unitOfList_eq_insertManyIfNewUnit_empty, insertManyIfNewUnit_cons]

theorem unitOfArray_eq_unitOfList (a : Array α) :
    (unitOfArray a : Table α Unit) = unitOfList a.toList := by
  unfold unitOfArray unitOfList insertManyIfNewUnit
  simp only [Array.forIn_toList]

/-! ### Entry-wise behaviour of the folds (L, used for the model lemmas) -/

/-- Folding `insertIfNew` keeps the existing entry, else the first one in `L`. -/
private theorem getEntry?_foldl_insertIfNew [EquivBEq α] [LawfulHashable α]
    (L : List ((_ : α) × β)) (acc : Table α β) (k : α) :
    getEntry? k (L.foldl (fun acc e => acc.insertIfNew e.1 e.2) acc).toListModel =
      (getEntry? k acc.toListModel).or (getEntry? k L) := by
  induction L generalizing acc with
  | nil => rw [List.foldl_nil, getEntry?_nil, Option.or_none]
  | cons e L ih =>
    obtain ⟨a, b⟩ := e
    rw [List.foldl_cons, ih, getEntry?_of_perm (distinctKeys _) (toListModel_insertIfNew acc a b),
      getEntry?_insertEntryIfNew, getEntry?_cons]
    cases hak : a == k
    · simp
    · rw [containsKey_congr hak]
      cases hc : containsKey k acc.toListModel
      · rw [getEntry?_eq_none.2 hc]
        simp
      · obtain ⟨x, hx⟩ := Option.isSome_iff_exists.1
          ((containsKey_eq_isSome_getEntry? (a := k) (l := acc.toListModel)).symm.trans hc)
        rw [hx]
        simp

/-- Folding `insert` over a list with distinct keys: the entry of `L` wins. -/
private theorem getEntry?_foldl_insert [EquivBEq α] [LawfulHashable α]
    (L : List ((_ : α) × β)) (hL : DistinctKeys L) (acc : Table α β) (k : α) :
    getEntry? k (L.foldl (fun acc e => acc.insert e.1 e.2) acc).toListModel =
      (getEntry? k L).or (getEntry? k acc.toListModel) := by
  induction L generalizing acc with
  | nil => rw [List.foldl_nil, getEntry?_nil, Option.none_or]
  | cons e L ih =>
    obtain ⟨a, b⟩ := e
    rw [List.foldl_cons, ih hL.tail, getEntry?_of_perm (distinctKeys _) (toListModel_insert acc a b),
      getEntry?_insertEntry, getEntry?_cons]
    cases hak : a == k
    · simp
    · have hk : getEntry? k L = none :=
        getEntry?_eq_none.2 ((containsKey_congr hak).symm.trans hL.containsKey_eq_false)
      simp [hk]

/-- One step of `inter`'s second branch. -/
private theorem getEntry?_interStep [EquivBEq α] [LawfulHashable α] (t₁ acc : Table α β)
    (a k : α) :
    getEntry? k (t₁.lookup a (fun k' v' => acc.insert k' v') (fun _ => acc)).toListModel =
      ((getEntry? k t₁.toListModel).filter (fun e => a == e.1)).or
        (getEntry? k acc.toListModel) := by
  rw [lookup_eq]
  cases ha : getEntry? a t₁.toListModel with
  | none =>
    cases hk : getEntry? k t₁.toListModel with
    | none => simp
    | some x =>
      have hxk := beq_of_getEntry?_eq_some hk
      cases hax : a == x.1
      · simp [Option.filter_some, hax]
      · rw [getEntry?_congr (BEq.trans hax hxk), hk] at ha
        cases ha
  | some y =>
    have hya := beq_of_getEntry?_eq_some ha
    simp only [Option.elim]
    rw [getEntry?_of_perm (distinctKeys _) (toListModel_insert acc y.1 y.2), getEntry?_insertEntry]
    cases hyk : y.1 == k
    · cases hk : getEntry? k t₁.toListModel with
      | none => simp
      | some x =>
        have hxk := beq_of_getEntry?_eq_some hk
        cases hax : a == x.1
        · simp [Option.filter_some, hax]
        · have : (y.1 == k) = true := BEq.trans hya (BEq.trans hax hxk)
          rw [hyk] at this
          cases this
    · have hak : (a == k) = true := BEq.trans (BEq.symm hya) hyk
      rw [← getEntry?_congr (l := t₁.toListModel) hak, ha]
      simp [Option.filter_some, BEq.symm hya]

/-- `inter`'s second branch, entry-wise. -/
private theorem getEntry?_foldl_inter [EquivBEq α] [LawfulHashable α] (t₁ : Table α β)
    (L : List ((_ : α) × β)) (acc : Table α β) (k : α) :
    getEntry? k (L.foldl (fun acc e => t₁.lookup e.1 (fun k' v' => acc.insert k' v')
        (fun _ => acc)) acc).toListModel =
      ((getEntry? k t₁.toListModel).filter (fun e => containsKey e.1 L)).or
        (getEntry? k acc.toListModel) := by
  induction L generalizing acc with
  | nil => simp
  | cons e L ih =>
    obtain ⟨a, b⟩ := e
    rw [List.foldl_cons, ih, getEntry?_interStep]
    simp only [containsKey_cons, Bool.or_comm (a == _), Std.Internal.List.Option.filter_or,
      Option.or_assoc]

/-- Folding `erase`: the keys of `L` are gone, the rest is unchanged. -/
private theorem getEntry?_foldl_erase [EquivBEq α] [LawfulHashable α]
    (L : List ((_ : α) × β)) (acc : Table α β) (k : α) :
    getEntry? k (L.foldl (fun acc e => acc.erase e.1) acc).toListModel =
      if containsKey k L then none else getEntry? k acc.toListModel := by
  induction L generalizing acc with
  | nil => simp
  | cons e L ih =>
    obtain ⟨a, b⟩ := e
    rw [List.foldl_cons, ih, getEntry?_of_perm (distinctKeys _) (toListModel_erase acc a),
      getEntry?_eraseKey (distinctKeys acc), containsKey_cons]
    cases a == k <;> cases containsKey k L <;> simp

/-! ### Model lemmas (L) -/

/-- **Blocked (`sorry`).** Std proves this by unfolding `insertListConst` and `insertList`.
Neither is `@[expose]`d, and this module may not `import all Std.Data.Internal.List.Associative`
(`tools/audit.py`), so their defining equations are out of reach. The public lemmas about
`insertListConst` describe a key only when it does not occur in `l` or when the keys of `l` are
pairwise distinct, so they cannot settle a list with duplicate keys. -/
theorem toListModel_insertMany_list [EquivBEq α] [LawfulHashable α] (t : Table α β)
    (l : List (α × β)) :
    (t.insertMany l).1.toListModel.Perm (insertListConst t.toListModel l) := by
  sorry

theorem toListModel_insertManyIfNewUnit_list [EquivBEq α] [LawfulHashable α]
    (t : Table α Unit) (l : List α) :
    (t.insertManyIfNewUnit l).1.toListModel.Perm (insertListIfNewUnit t.toListModel l) := by
  apply getEntry?_ext (distinctKeys _) (distinctKeys t).insertListIfNewUnit
  intro k
  rw [insertManyIfNewUnit_list_eq_foldl, getEntry?_insertListIfNewUnit,
    ← getEntry?_foldl_insertIfNew, List.foldl_map]

theorem toListModel_union [EquivBEq α] [LawfulHashable α] (t₁ t₂ : Table α β) :
    (t₁.union t₂).toListModel.Perm (insertList t₁.toListModel t₂.toListModel) := by
  apply getEntry?_ext (distinctKeys _) (distinctKeys t₁).insertList
  intro k
  rw [getEntry?_insertList (distinctKeys t₁) (DistinctKeys.def.1 (distinctKeys t₂))]
  unfold union
  split
  · rw [fold_eq_foldl_toListModel, getEntry?_foldl_insertIfNew]
  · rw [fold_eq_foldl_toListModel, getEntry?_foldl_insert _ (distinctKeys t₂)]

theorem toListModel_inter [EquivBEq α] [LawfulHashable α] (t₁ t₂ : Table α β) :
    (t₁.inter t₂).toListModel.Perm
      (t₁.toListModel.filter fun p => containsKey p.1 t₂.toListModel) := by
  unfold inter
  split
  · refine (toListModel_filter _ _).trans ?_
    simp only [contains_eq_containsKey]
    exact List.Perm.refl _
  · apply getEntry?_ext (distinctKeys _)
      ((distinctKeys t₁).filter (f := fun k _ => containsKey k t₂.toListModel))
    intro k
    rw [fold_eq_foldl_toListModel, getEntry?_foldl_inter, toListModel_emptyWithCapacity,
      getEntry?_filter (distinctKeys t₁), getEntry?_nil, Option.or_none]

theorem toListModel_diff [EquivBEq α] [LawfulHashable α] (t₁ t₂ : Table α β) :
    (t₁.diff t₂).toListModel.Perm
      (List.filter (fun k => !List.contains (t₂.toListModel.map Sigma.fst) k.fst)
        t₁.toListModel) := by
  unfold diff
  split
  · refine (toListModel_filter _ _).trans ?_
    simp only [contains_eq_containsKey, containsKey_eq_contains_map_fst]
    exact List.Perm.refl _
  · apply getEntry?_ext (distinctKeys _) ((distinctKeys t₁).filter
      (f := fun k _ => !List.contains (t₂.toListModel.map Sigma.fst) k))
    intro k
    rw [fold_eq_foldl_toListModel, getEntry?_foldl_erase, getEntry?_filter (distinctKeys t₁)]
    cases hk : getEntry? k t₁.toListModel with
    | none => simp
    | some x =>
      have hxk := beq_of_getEntry?_eq_some hk
      simp only [Option.filter_some, ← containsKey_eq_contains_map_fst, containsKey_congr hxk]
      cases containsKey k t₂.toListModel <;> simp

/-! ### `beq` -/

/-- `beq` in terms of the models: the definition of `Const.beqModel`, unfolded. -/
theorem beq_eq_all_getValue? [EquivBEq α] [LawfulHashable α] [BEq β] (t₁ t₂ : Table α β) :
    t₁.beq t₂ = if t₁.toListModel.length ≠ t₂.toListModel.length then false
      else t₁.toListModel.all fun x => getValue? x.1 t₂.toListModel == some x.2 := by
  unfold beq
  rw [size_eq_length, size_eq_length, all_eq_all_toListModel]
  simp only [get?_eq_getValue?]

/-- **Blocked (`sorry`).** `Const.beqModel` is not `@[expose]`d and no public lemma states its
definition; with it, this lemma is `beq_eq_all_getValue?` followed by unfolding. The three lemmas
below, `beq_of_perm`, `perm_of_beq` and `beq_congr`, are proved without it and give what Std's user
lemmas take from `Const.beqModel_eq_true_of_perm`, `Const.perm_of_beqModel` and
`Const.beqModel_congr`. Std's `Raw₀` version needs only `[PartialEquivBEq α]`; this one takes
`[EquivBEq α]` because the contract's `lookup_eq` does, and every user lemma about `==` has it. -/
theorem beq_eq_beqModel [EquivBEq α] [LawfulHashable α] [BEq β] (t₁ t₂ : Table α β) :
    t₁.beq t₂ = Const.beqModel t₁.toListModel t₂.toListModel := by
  sorry

theorem beq_of_perm [EquivBEq α] [LawfulHashable α] [BEq β] [ReflBEq β] {t₁ t₂ : Table α β}
    (h : t₁.toListModel.Perm t₂.toListModel) : t₁.beq t₂ = true := by
  rw [beq_eq_all_getValue?, h.length_eq]
  simp only [ne_eq, not_true_eq_false, ↓reduceIte, List.all_eq_true]
  intro x hx
  rw [← getValue?_of_perm (distinctKeys t₁) h,
    getValue?_eq_some_getValue (containsKey_of_mem hx), getValue_of_mem hx (distinctKeys t₁)]
  exact BEq.rfl

theorem perm_of_beq [LawfulBEq α] [BEq β] [LawfulBEq β] {t₁ t₂ : Table α β}
    (h : t₁.beq t₂ = true) : t₁.toListModel.Perm t₂.toListModel := by
  rw [beq_eq_all_getValue?] at h
  simp only [ne_eq, ite_not, Bool.ite_false_right, Bool.and_eq_true, decide_eq_true_eq,
    List.all_eq_true, beq_iff_eq] at h
  obtain ⟨he, hyp⟩ := h
  have h₁ := distinctKeys t₁
  have h₂ := distinctKeys t₂
  have hyp2 : ∀ (a : α), containsKey a t₁.toListModel = true →
      getValue? a t₂.toListModel = getValue? a t₁.toListModel := by
    intro a mem
    rw [getValue?_eq_some_getValue mem]
    have hmem : (⟨a, getValue a t₁.toListModel mem⟩ : (_ : α) × β) ∈ t₁.toListModel := by
      rw [mem_iff_getValue?_eq_some h₁, getValue?_eq_some_getValue mem]
    exact hyp _ hmem
  apply getValueCast?_ext h₁ h₂
  intro a
  rw [← getValue?_eq_getValueCast?, ← getValue?_eq_getValueCast?]
  by_cases hc₁ : containsKey a t₁.toListModel = true
  · exact (hyp2 a hc₁).symm
  · rw [Bool.not_eq_true] at hc₁
    by_cases hc₂ : containsKey a t₂.toListModel = true
    · have := containsKey_of_length_eq h₁ h₂ he.symm (fun k' mem => by
        rw [containsKey_eq_isSome_getValue?, hyp2 k' mem, ← containsKey_eq_isSome_getValue?]
        exact mem) a hc₂
      rw [this] at hc₁
      cases hc₁
    · rw [Bool.not_eq_true] at hc₂
      rw [getValue?_eq_none.2 hc₁, getValue?_eq_none.2 hc₂]

theorem beq_congr [EquivBEq α] [LawfulHashable α] [BEq β] {t₁ t₂ t₃ t₄ : Table α β}
    (h₁ : t₁.toListModel.Perm t₃.toListModel) (h₂ : t₂.toListModel.Perm t₄.toListModel) :
    t₁.beq t₂ = t₃.beq t₄ := by
  rw [beq_eq_all_getValue?, beq_eq_all_getValue?, h₁.length_eq, h₂.length_eq, h₁.all_eq]
  simp only [getValue?_of_perm (distinctKeys t₂) h₂]

end Lemmas

end OAMap.Core.Table
