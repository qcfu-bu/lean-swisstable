import Std

/-!
# Uniformity experiment: 50 random Std lemmas ported onto a mock map

Layer 0: a list-backed mock with the full operation set the sample needs.
Layer 1: the model interface (`Model.*`), the only thing a real open-addressing table proves.
Layer 2: `simp_to_model` and the ported lemmas. Every ported proof is Std's own proof text
(`RawLemmas.lean` for primitive lemmas, `DHashMap/Lemmas.lean` or `HashMap/Lemmas.lean` for
derived ones) after the mechanical renaming described in `proofs.md`; deviations are marked
`-- EDIT:`. Lemmas from the random sample are marked `-- [S]`; the others are the siblings they
need.
-/

open Std.Internal.List Std.Internal

set_option autoImplicit false
set_option linter.unusedVariables false

universe u v w w'

namespace Mock

/-! ## Layer 0 -/

structure HashMap (α : Type u) (β : Type v) [BEq α] [Hashable α] where
  impl : List ((_ : α) × β)
  distinct : ∀ [EquivBEq α] [LawfulHashable α], DistinctKeys impl

namespace HashMap

variable {α : Type u} {β : Type v} {γ : Type w} {δ : Type w'} [BEq α] [Hashable α]

def emptyWithCapacity (_capacity : Nat := 8) : HashMap α β := ⟨[], DistinctKeys.nil⟩
instance : EmptyCollection (HashMap α β) := ⟨emptyWithCapacity⟩

def insert (m : HashMap α β) (a : α) (b : β) : HashMap α β :=
  ⟨insertEntry a b m.impl, m.distinct.insertEntry⟩
instance : Singleton (α × β) (HashMap α β) := ⟨fun ⟨a, b⟩ => (∅ : HashMap α β).insert a b⟩
instance : Insert (α × β) (HashMap α β) := ⟨fun ⟨a, b⟩ s => s.insert a b⟩
def insertIfNew (m : HashMap α β) (a : α) (b : β) : HashMap α β :=
  ⟨insertEntryIfNew a b m.impl, m.distinct.insertEntryIfNew⟩
def erase (m : HashMap α β) (a : α) : HashMap α β :=
  ⟨eraseKey a m.impl, m.distinct.eraseKey⟩
def contains (m : HashMap α β) (a : α) : Bool := containsKey a m.impl
instance : Membership α (HashMap α β) where mem m a := m.contains a
instance {m : HashMap α β} {a : α} : Decidable (a ∈ m) :=
  inferInstanceAs (Decidable (m.contains a = true))
def get? (m : HashMap α β) (a : α) : Option β := getValue? a m.impl
def get (m : HashMap α β) (a : α) (h : a ∈ m) : β := getValue a m.impl h
def get! [Inhabited β] (m : HashMap α β) (a : α) : β := getValue! a m.impl
def getD (m : HashMap α β) (a : α) (fallback : β) : β := getValueD a m.impl fallback
instance : GetElem? (HashMap α β) α β (fun m a => a ∈ m) where
  getElem m a h := m.get a h
  getElem? m a := m.get? a
  getElem! m a := m.get! a
def getKey? (m : HashMap α β) (a : α) : Option α := List.getKey? a m.impl
def getKey (m : HashMap α β) (a : α) (h : a ∈ m) : α := List.getKey a m.impl h
def getKey! [Inhabited α] (m : HashMap α β) (a : α) : α := List.getKey! a m.impl
def getKeyD (m : HashMap α β) (a : α) (fallback : α) : α := List.getKeyD a m.impl fallback
def getThenInsertIfNew? (m : HashMap α β) (a : α) (b : β) : Option β × HashMap α β :=
  (m.get? a, m.insertIfNew a b)
def size (m : HashMap α β) : Nat := m.impl.length
def isEmpty (m : HashMap α β) : Bool := m.size == 0
def toList (m : HashMap α β) : List (α × β) := m.impl.map fun x => (x.1, x.2)
def keys (m : HashMap α β) : List α := List.keys m.impl
def fold (f : δ → α → β → δ) (init : δ) (m : HashMap α β) : δ :=
  m.impl.foldl (fun a b => f a b.1 b.2) init
def all (m : HashMap α β) (p : α → β → Bool) : Bool := m.impl.all fun x => p x.1 x.2
def any (m : HashMap α β) (p : α → β → Bool) : Bool := m.impl.any fun x => p x.1 x.2
def filter (f : α → β → Bool) (m : HashMap α β) : HashMap α β :=
  ⟨m.impl.filter fun p => f p.1 p.2, m.distinct.filter⟩
def filterMap (f : α → β → Option γ) (m : HashMap α β) : HashMap α γ :=
  ⟨m.impl.filterMap fun p => (f p.1 p.2).map (⟨p.1, ·⟩), m.distinct.filterMap⟩
def map (f : α → β → γ) (m : HashMap α β) : HashMap α γ :=
  ⟨m.impl.map fun p => ⟨p.1, f p.1 p.2⟩, m.distinct.map⟩
def alter (m : HashMap α β) (a : α) (f : Option β → Option β) : HashMap α β :=
  ⟨Const.alterKey a f m.impl, m.distinct.constAlterKey⟩
def modify (m : HashMap α β) (a : α) (f : β → β) : HashMap α β :=
  ⟨Const.modifyKey a f m.impl, m.distinct.constModifyKey⟩
def union (m₁ m₂ : HashMap α β) : HashMap α β := ⟨insertList m₁.impl m₂.impl, m₁.distinct.insertList⟩
instance : Union (HashMap α β) := ⟨union⟩
def inter (m₁ m₂ : HashMap α β) : HashMap α β :=
  ⟨m₁.impl.filter fun p => containsKey p.1 m₂.impl,
    DistinctKeys.filter (f := fun a _ => containsKey a m₂.impl) m₁.distinct⟩
instance : Inter (HashMap α β) := ⟨inter⟩
def diff (m₁ m₂ : HashMap α β) : HashMap α β :=
  ⟨m₁.impl.filter fun k => !(m₂.impl.map Sigma.fst).contains k.1,
    DistinctKeys.filter (f := fun a _ => !(m₂.impl.map Sigma.fst).contains a) m₁.distinct⟩
instance : SDiff (HashMap α β) := ⟨diff⟩

/-- Std's construction: the loop state carries the induction principle. -/
def insertMany' {ρ : Type w} [ForIn Id ρ (α × β)] (m : HashMap α β) (l : ρ) :
    { m' : HashMap α β // ∀ (P : HashMap α β → Prop),
      (∀ {m'' a b}, P m'' → P (m''.insert a b)) → P m → P m' } := Id.run do
  let mut r : { m' : HashMap α β // ∀ (P : HashMap α β → Prop),
    (∀ {m'' a b}, P m'' → P (m''.insert a b)) → P m → P m' } := ⟨m, fun _ _ => id⟩
  for (a, b) in l do
    r := ⟨r.1.insert a b, fun _ h hm => h (r.2 _ h hm)⟩
  return r
def insertMany {ρ : Type w} [ForIn Id ρ (α × β)] (m : HashMap α β) (l : ρ) : HashMap α β :=
  (insertMany' m l).1

def insertManyIfNewUnit' {ρ : Type w} [ForIn Id ρ α] (m : HashMap α Unit) (l : ρ) :
    { m' : HashMap α Unit // ∀ (P : HashMap α Unit → Prop),
      (∀ {m'' a b}, P m'' → P (m''.insertIfNew a b)) → P m → P m' } := Id.run do
  let mut r : { m' : HashMap α Unit // ∀ (P : HashMap α Unit → Prop),
    (∀ {m'' a b}, P m'' → P (m''.insertIfNew a b)) → P m → P m' } := ⟨m, fun _ _ => id⟩
  for a in l do
    r := ⟨r.1.insertIfNew a (), fun _ h hm => h (r.2 _ h hm)⟩
  return r
def insertManyIfNewUnit {ρ : Type w} [ForIn Id ρ α] (m : HashMap α Unit) (l : ρ) : HashMap α Unit :=
  (insertManyIfNewUnit' m l).1
def unitOfList (l : List α) : HashMap α Unit := insertManyIfNewUnit ∅ l
def unitOfArray (l : Array α) : HashMap α Unit := insertManyIfNewUnit ∅ l

/-- The model of a map: its entries, in iteration order. -/
def toListModel (m : HashMap α β) : List ((_ : α) × β) := m.impl

structure Equiv (m₁ m₂ : HashMap α β) : Prop where
  inner : (toListModel m₁).Perm (toListModel m₂)

scoped infixl:50 " ~m " => Equiv

/-! ## Layer 1: the model interface -/

namespace Model

/-- Proves an interface lemma without making it a `rfl` (dsimp) lemma: a real table's lemmas are
not definitional, and `simp` treats the two kinds differently. -/
theorem nr {γ : Sort _} {a b : γ} (h : a = b) : a = b := h

theorem distinctKeys [EquivBEq α] [LawfulHashable α] (m : HashMap α β) :
    DistinctKeys (toListModel m) := m.distinct

theorem size_eq_length (m : HashMap α β) : m.size = (toListModel m).length := nr rfl
theorem isEmpty_eq_isEmpty (m : HashMap α β) : m.isEmpty = (toListModel m).isEmpty := by
  cases h : m.impl <;> simp [isEmpty, size, toListModel, h]
theorem contains_eq_containsKey [EquivBEq α] [LawfulHashable α] (m : HashMap α β) {a : α} :
    m.contains a = containsKey a (toListModel m) := nr rfl
theorem mem_iff_containsKey [EquivBEq α] [LawfulHashable α] (m : HashMap α β) {a : α} :
    a ∈ m ↔ containsKey a (toListModel m) = true := ⟨id, id⟩
theorem getElem?_eq_getValue? [EquivBEq α] [LawfulHashable α] (m : HashMap α β) {a : α} :
    m[a]? = getValue? a (toListModel m) := nr rfl
theorem getElem_eq_getValue [EquivBEq α] [LawfulHashable α] (m : HashMap α β) {a : α} {h : a ∈ m} :
    m[a]'h = getValue a (toListModel m) ((mem_iff_containsKey m).1 h) := nr rfl
theorem getElem!_eq_getValue! [EquivBEq α] [LawfulHashable α] [Inhabited β] (m : HashMap α β)
    {a : α} : m[a]! = getValue! a (toListModel m) := nr rfl
theorem getD_eq_getValueD [EquivBEq α] [LawfulHashable α] (m : HashMap α β) {a : α} {fallback : β} :
    m.getD a fallback = getValueD a (toListModel m) fallback := nr rfl
theorem getKey?_eq_getKey? [EquivBEq α] [LawfulHashable α] (m : HashMap α β) {a : α} :
    m.getKey? a = List.getKey? a (toListModel m) := nr rfl
theorem getKey_eq_getKey [EquivBEq α] [LawfulHashable α] (m : HashMap α β) {a : α} {h : a ∈ m} :
    m.getKey a h = List.getKey a (toListModel m) ((mem_iff_containsKey m).1 h) := nr rfl
theorem getKey!_eq_getKey! [EquivBEq α] [LawfulHashable α] [Inhabited α] (m : HashMap α β)
    {a : α} : m.getKey! a = List.getKey! a (toListModel m) := nr rfl
theorem getKeyD_eq_getKeyD [EquivBEq α] [LawfulHashable α] (m : HashMap α β) {a fallback : α} :
    m.getKeyD a fallback = List.getKeyD a (toListModel m) fallback := nr rfl
theorem toList_eq_toListModel_map (m : HashMap α β) :
    m.toList = (toListModel m).map fun x => (x.1, x.2) := nr rfl
theorem keys_eq_keys_toListModel (m : HashMap α β) : m.keys = List.keys (toListModel m) := nr rfl
theorem fold_eq_foldl_toListModel (m : HashMap α β) {f : δ → α → β → δ} {init : δ} :
    m.fold f init = (toListModel m).foldl (fun a b => f a b.1 b.2) init := nr rfl
theorem all_eq_all_toListModel (m : HashMap α β) {p : α → β → Bool} :
    m.all p = (toListModel m).all fun x => p x.1 x.2 := nr rfl
theorem any_eq_any_toListModel (m : HashMap α β) {p : α → β → Bool} :
    m.any p = (toListModel m).any fun x => p x.1 x.2 := nr rfl
theorem equiv_iff_toListModel_perm {m₁ m₂ : HashMap α β} :
    m₁ ~m m₂ ↔ (toListModel m₁).Perm (toListModel m₂) := ⟨fun h => h.1, fun h => ⟨h⟩⟩

theorem toListModel_emptyWithCapacity {c : Nat} :
    toListModel (emptyWithCapacity c : HashMap α β) = [] := nr rfl
theorem toListModel_insert [EquivBEq α] [LawfulHashable α] (m : HashMap α β) {a : α} {b : β} :
    (toListModel (m.insert a b)).Perm (insertEntry a b (toListModel m)) := .refl _
theorem toListModel_insertIfNew [EquivBEq α] [LawfulHashable α] (m : HashMap α β) {a : α} {b : β} :
    (toListModel (m.insertIfNew a b)).Perm (insertEntryIfNew a b (toListModel m)) := .refl _
theorem toListModel_erase [EquivBEq α] [LawfulHashable α] (m : HashMap α β) {a : α} :
    (toListModel (m.erase a)).Perm (eraseKey a (toListModel m)) := .refl _
theorem toListModel_filter (m : HashMap α β) {f : α → β → Bool} :
    (toListModel (m.filter f)).Perm ((toListModel m).filter fun p => f p.1 p.2) := .refl _
theorem toListModel_filterMap (m : HashMap α β) {f : α → β → Option γ} :
    (toListModel (m.filterMap f)).Perm
      ((toListModel m).filterMap fun p => (f p.1 p.2).map (⟨p.1, ·⟩)) := .refl _
theorem toListModel_map (m : HashMap α β) {f : α → β → γ} :
    (toListModel (m.map f)).Perm ((toListModel m).map fun p => ⟨p.1, f p.1 p.2⟩) := .refl _
theorem toListModel_alter [EquivBEq α] [LawfulHashable α] (m : HashMap α β) {a : α}
    {f : Option β → Option β} :
    (toListModel (m.alter a f)).Perm (Const.alterKey a f (toListModel m)) := .refl _
theorem toListModel_modify [EquivBEq α] [LawfulHashable α] (m : HashMap α β) {a : α} {f : β → β} :
    (toListModel (m.modify a f)).Perm (Const.modifyKey a f (toListModel m)) := .refl _
theorem toListModel_union [EquivBEq α] [LawfulHashable α] (m₁ m₂ : HashMap α β) :
    (toListModel (m₁ ∪ m₂)).Perm (insertList (toListModel m₁) (toListModel m₂)) := .refl _
theorem toListModel_inter [EquivBEq α] [LawfulHashable α] (m₁ m₂ : HashMap α β) :
    (toListModel (m₁ ∩ m₂)).Perm
      ((toListModel m₁).filter fun p => containsKey p.1 (toListModel m₂)) := .refl _
theorem toListModel_diff [EquivBEq α] [LawfulHashable α] (m₁ m₂ : HashMap α β) :
    (toListModel (m₁ \ m₂)).Perm
      ((toListModel m₁).filter fun k => !((toListModel m₂).map Sigma.fst).contains k.1) := .refl _

theorem getThenInsertIfNew?_snd (m : HashMap α β) {k : α} {v : β} :
    (getThenInsertIfNew? m k v).2 = m.insertIfNew k v := nr rfl

end Model

/-! ## seal -/

attribute [irreducible] toListModel insert insertIfNew erase contains get? get get! getD getKey?
  getKey getKey! getKeyD size isEmpty toList keys fold all any filter filterMap map alter modify
  union inter diff emptyWithCapacity getThenInsertIfNew?

/-! ## Layer 1.5: generic lemmas about the bulk operations

`insertMany` and `insertManyIfNewUnit` are loops of `insert`/`insertIfNew` (Std's construction),
so their lemmas follow from the definitions and the Layer-1 lemmas of `insert`/`insertIfNew`,
whatever the table layout. -/

namespace Model

theorem loop_val {Q : HashMap α β → Prop} (g : ∀ (r : Subtype Q) (a : α) (b : β), Q (r.1.insert a b))
    (l : List (α × β)) (r : Subtype Q) :
    (Id.run (forIn l r fun p r => pure (ForInStep.yield ⟨r.1.insert p.1 p.2, g r p.1 p.2⟩))).1 =
      l.foldl (fun acc p => acc.insert p.1 p.2) r.1 := by
  induction l generalizing r with
  | nil => rfl
  | cons hd tl ih => simp only [List.forIn_cons, List.foldl_cons]; exact ih _

theorem insertMany_list_eq_foldl (m : HashMap α β) (l : List (α × β)) :
    insertMany m l = l.foldl (fun acc p => acc.insert p.1 p.2) m := by
  unfold insertMany insertMany'
  exact loop_val (fun r a b P h hm => h (r.2 P h hm)) l _

theorem loop_val_unit {Q : HashMap α Unit → Prop}
    (g : ∀ (r : Subtype Q) (a : α), Q (r.1.insertIfNew a ())) (l : List α) (r : Subtype Q) :
    (Id.run (forIn l r fun a r => pure (ForInStep.yield ⟨r.1.insertIfNew a (), g r a⟩))).1 =
      l.foldl (fun acc a => acc.insertIfNew a ()) r.1 := by
  induction l generalizing r with
  | nil => rfl
  | cons hd tl ih => simp only [List.forIn_cons, List.foldl_cons]; exact ih _

theorem insertManyIfNewUnit_list_eq_foldl (m : HashMap α Unit) (l : List α) :
    insertManyIfNewUnit m l = l.foldl (fun acc a => acc.insertIfNew a ()) m := by
  unfold insertManyIfNewUnit insertManyIfNewUnit'
  exact loop_val_unit (fun r a P h hm => h (r.2 P h hm)) l _

theorem insertMany_ind {ρ : Type w} [ForIn Id ρ (α × β)] {motive : HashMap α β → Prop}
    (m : HashMap α β) {l : ρ} (init : motive m) (insert : ∀ m a b, motive m → motive (m.insert a b)) :
    motive (m.insertMany l) :=
  (insertMany' m l).2 motive (fun h => insert _ _ _ h) init

theorem toListModel_insertMany_list [EquivBEq α] [LawfulHashable α] (m : HashMap α β)
    {l : List (α × β)} :
    (toListModel (insertMany m l)).Perm (insertListConst (toListModel m) l) := by
  rw [insertMany_list_eq_foldl]
  induction l generalizing m with
  | nil => exact .refl _
  | cons hd tl ih =>
    refine (ih (m.insert hd.1 hd.2)).trans ?_
    exact insertList_perm_of_perm_first (toListModel_insert m) (distinctKeys _)

theorem toListModel_insertManyIfNewUnit_list [EquivBEq α] [LawfulHashable α] (m : HashMap α Unit)
    {l : List α} :
    (toListModel (insertManyIfNewUnit m l)).Perm (insertListIfNewUnit (toListModel m) l) := by
  rw [insertManyIfNewUnit_list_eq_foldl]
  induction l generalizing m with
  | nil => exact .refl _
  | cons hd tl ih =>
    refine (ih (m.insertIfNew hd ())).trans ?_
    exact insertListIfNewUnit_perm_of_perm_first (toListModel_insertIfNew m) (distinctKeys _)

theorem unitOfArray_eq_unitOfList (a : Array α) : unitOfArray a = unitOfList a.toList := by
  simp only [unitOfArray, unitOfList, insertManyIfNewUnit, insertManyIfNewUnit', Array.forIn_toList]

end Model

/-! ## Layer 2: `simp_to_model` -/

open Lean in
meta def queryMap : Std.HashMap Name (Name × Array (MacroM (TSyntax `term))) :=
  .ofList
    [⟨`isEmpty, (``Model.isEmpty_eq_isEmpty, #[`(_root_.List.Perm.isEmpty_eq)])⟩,
     ⟨`contains, (``Model.contains_eq_containsKey, #[`(containsKey_of_perm)])⟩,
     ⟨`mem, (``Model.mem_iff_containsKey, #[`(containsKey_of_perm)])⟩,
     ⟨`size, (``Model.size_eq_length, #[`(_root_.List.Perm.length_eq)])⟩,
     ⟨`getElem?, (``Model.getElem?_eq_getValue?, #[`(getValue?_of_perm _)])⟩,
     ⟨`getElem, (``Model.getElem_eq_getValue, #[`(getValue_of_perm _)])⟩,
     ⟨`getElem!, (``Model.getElem!_eq_getValue!, #[`(getValue!_of_perm _)])⟩,
     ⟨`getD, (``Model.getD_eq_getValueD, #[`(getValueD_of_perm _)])⟩,
     ⟨`getKey?, (``Model.getKey?_eq_getKey?, #[`(getKey?_of_perm _)])⟩,
     ⟨`getKey, (``Model.getKey_eq_getKey, #[`(getKey_of_perm _)])⟩,
     ⟨`getKey!, (``Model.getKey!_eq_getKey!, #[`(getKey!_of_perm _)])⟩,
     ⟨`getKeyD, (``Model.getKeyD_eq_getKeyD, #[`(getKeyD_of_perm _)])⟩,
     ⟨`toList, (``Model.toList_eq_toListModel_map, #[])⟩,
     ⟨`keys, (``Model.keys_eq_keys_toListModel, #[])⟩,
     ⟨`fold, (``Model.fold_eq_foldl_toListModel, #[])⟩,
     ⟨`all, (``Model.all_eq_all_toListModel, #[])⟩,
     ⟨`any, (``Model.any_eq_any_toListModel, #[])⟩,
     ⟨`Equiv, (``Model.equiv_iff_toListModel_perm,
       #[`(_root_.List.Perm.congr_left), `(_root_.List.Perm.congr_right)])⟩]

open Lean in
meta def modifyMap : Std.HashMap Name Name :=
  .ofList
    [⟨`insert, ``Model.toListModel_insert⟩,
     ⟨`insertIfNew, ``Model.toListModel_insertIfNew⟩,
     ⟨`erase, ``Model.toListModel_erase⟩,
     ⟨`filter, ``Model.toListModel_filter⟩,
     ⟨`filterMap, ``Model.toListModel_filterMap⟩,
     ⟨`map, ``Model.toListModel_map⟩,
     ⟨`alter, ``Model.toListModel_alter⟩,
     ⟨`modify, ``Model.toListModel_modify⟩,
     ⟨`union, ``Model.toListModel_union⟩,
     ⟨`inter, ``Model.toListModel_inter⟩,
     ⟨`diff, ``Model.toListModel_diff⟩,
     ⟨`insertMany, ``Model.toListModel_insertMany_list⟩,
     ⟨`insertManyIfNewUnit, ``Model.toListModel_insertManyIfNewUnit_list⟩]

macro "wf_trivial" : tactic => `(tactic| first | assumption | apply Model.distinctKeys)
/-- The closing step: side conditions, and hypotheses that `simp ... at *` could not rewrite in
place because the goal mentioned them. -/
macro "wf_finish" : tactic => `(tactic| first
  | wf_trivial
  | (simp only [Bool.not_eq_true, Model.mem_iff_containsKey] at *; assumption))

/-- Std's `simp_to_model` with our tables and discharger, plus `Bool.not_eq_true` (so that `¬k ∈ m`
becomes `containsKey k l = false`, Std's normal form) and an optional location. -/
syntax "simp_to_model" (" [" (ident,*) "]")? (Lean.Parser.Tactic.location)? ("using" term)? : tactic

macro_rules
| `(tactic| simp_to_model $[[$names,*]]? $[$loc]? $[using $using?]?) => do
  let mut queryNames : Array Lean.Name := #[]
  let mut congrNames : Array Lean.Term := #[]
  if let some names := names then
    for query in names.getElems do
      let some (query, congr) := queryMap.get? query.getId | continue
      queryNames := queryNames.push query
      for c in congr do
        congrNames := congrNames.push (← c)
  if queryNames.isEmpty then
    for (q, c) in queryMap.valuesArray do
      queryNames := queryNames.push q
      for c' in c do
        congrNames := congrNames.push (← c')
  let mut congrModify : Array (Lean.TSyntax `term) := #[]
  if let some modifyNames := names then
    for modify in modifyNames.getElems.flatMap
        (fun n => modifyMap.get? (Lean.Syntax.getId n) |>.toArray) do
      for congr in congrNames do
        congrModify := congrModify.push (← `($congr:term ($(Lean.mkIdent modify) ..)))
  `(tactic|
    (simp (discharger := wf_trivial) only
      [Bool.not_eq_true, $[$(Array.map Lean.mkIdent queryNames ++ congrModify):term],*] $[$loc]?
     $[apply $(using?.toArray):term];*)
    <;> try wf_finish)

variable {m m₁ m₂ : HashMap α β}

/-! ### Ported lemmas -/

-- basics (siblings)
theorem mem_iff_contains {a : α} : a ∈ m ↔ m.contains a := Iff.rfl
@[simp] theorem contains_iff_mem {a : α} : m.contains a ↔ a ∈ m := Iff.rfl
theorem contains_eq_false_iff_not_mem {k : α} : m.contains k = false ↔ ¬k ∈ m := by
  rw [← Bool.not_eq_true]
  simp only [contains_iff_mem]
theorem contains_congr [EquivBEq α] [LawfulHashable α] {a b : α} (hab : a == b) :
    m.contains a = m.contains b := by
  simp_to_model [contains] using List.containsKey_congr hab
theorem mem_congr [EquivBEq α] [LawfulHashable α] {a b : α} (hab : a == b) : a ∈ m ↔ b ∈ m := by
  simp [← contains_iff_mem, contains_congr hab]
@[simp] theorem contains_insert [EquivBEq α] [LawfulHashable α] {k a : α} {v : β} :
    (m.insert k v).contains a = (k == a || m.contains a) := by
  simp_to_model [insert, contains] using List.containsKey_insertEntry
@[simp] theorem mem_insert [EquivBEq α] [LawfulHashable α] {k a : α} {v : β} :
    a ∈ m.insert k v ↔ k == a ∨ a ∈ m := by
  simp [← contains_iff_mem, contains_insert]
theorem mem_insert_self [EquivBEq α] [LawfulHashable α] {k : α} {v : β} : k ∈ m.insert k v := by
  simp
@[simp] theorem contains_erase [EquivBEq α] [LawfulHashable α] {k a : α} :
    (m.erase k).contains a = (!(k == a) && m.contains a) := by
  simp_to_model [erase, contains] using List.containsKey_eraseKey
@[simp] theorem mem_erase [EquivBEq α] [LawfulHashable α] {k a : α} :
    a ∈ m.erase k ↔ (k == a) = false ∧ a ∈ m := by
  simp [← contains_iff_mem, contains_erase]
-- [S]
theorem mem_of_mem_erase [EquivBEq α] [LawfulHashable α] {k a : α} : a ∈ m.erase k → a ∈ m := by
  simp
theorem contains_eq_isSome_getElem? [EquivBEq α] [LawfulHashable α] {a : α} :
    m.contains a = m[a]?.isSome := by
  simp_to_model [getElem?, contains] using List.containsKey_eq_isSome_getValue?
theorem mem_iff_isSome_getElem? [EquivBEq α] [LawfulHashable α] {a : α} :
    a ∈ m ↔ m[a]?.isSome := by
  simp [← contains_iff_mem, contains_eq_isSome_getElem?]
-- [S]
@[simp] theorem isSome_getElem?_eq_contains [EquivBEq α] [LawfulHashable α] {a : α} :
    m[a]?.isSome = m.contains a :=
  contains_eq_isSome_getElem?.symm
-- [S]
@[simp] theorem singleton_eq_insert {p : α × β} :
    Singleton.singleton p = (∅ : HashMap α β).insert p.1 p.2 :=
  rfl
-- [S]
@[simp] theorem getElem_insert_self [EquivBEq α] [LawfulHashable α] {k : α} {v : β} :
    (m.insert k v)[k]'mem_insert_self = v := by
  simp_to_model [insert, getElem] using List.getValue_insertEntry_self
-- [S]
theorem getElem?_eq_some_getElem [EquivBEq α] [LawfulHashable α] {a : α} (h' : a ∈ m) :
    m[a]? = some (m[a]'h') := by
  simp_to_model [getElem, getElem?] using List.getValue?_eq_some_getValue
-- [S]
@[simp] theorem getElem!_insert_self [EquivBEq α] [LawfulHashable α] [Inhabited β] {k : α} {v : β} :
    (m.insert k v)[k]! = v := by
  simp_to_model [insert, getElem!] using List.getValue!_insertEntry_self
-- [S]
theorem getKeyD_eq_fallback_of_contains_eq_false [EquivBEq α] [LawfulHashable α] {a : α}
    {fallback : α} : m.contains a = false → m.getKeyD a fallback = fallback := by
  simp_to_model [contains, getKeyD] using List.getKeyD_eq_fallback
-- [S]
theorem contains_insertIfNew_self [EquivBEq α] [LawfulHashable α] {k : α} {v : β} :
    (m.insertIfNew k v).contains k := by
  simp_to_model [insertIfNew, contains] using List.containsKey_insertEntryIfNew_self
-- [S]
theorem contains_of_contains_insertIfNew [EquivBEq α] [LawfulHashable α] {k a : α} {v : β} :
    (m.insertIfNew k v).contains a → (k == a) = false → m.contains a := by
  simp_to_model [insertIfNew, contains] using List.containsKey_of_containsKey_insertEntryIfNew
-- [S]  (Layer-1 obligation in our scheme: Std proves it from the implementation)
@[simp] theorem getThenInsertIfNew?_snd {k : α} {v : β} :
    (getThenInsertIfNew? m k v).2 = m.insertIfNew k v :=
  Model.getThenInsertIfNew?_snd m

-- the any/all cluster (siblings of the sampled `all_eq_true_iff_forall_mem_getElem`)
theorem any_toList {p : α → β → Bool} : m.toList.any (fun x => p x.1 x.2) = m.any p := by
  -- EDIT: Std's 9-line proof unfolds `Raw.any`'s `forIn`; with `any` in the model it is short
  simp_to_model [toList, any]; simp [List.any_map, Function.comp_def]
theorem all_toList {p : α → β → Bool} : m.toList.all (fun x => p x.1 x.2) = m.all p := by
  -- EDIT: as `any_toList`
  simp_to_model [toList, all]; simp [List.all_map, Function.comp_def]
theorem all_eq_not_any_not {p : (a : α) → β → Bool} : m.all p = ! m.any (fun a b => ! p a b) := by
  rw [← all_toList, ← any_toList, List.all_eq_not_any_not]
theorem mem_toList_iff_getKey?_eq_some_and_getElem?_eq_some [EquivBEq α] [LawfulHashable α]
    {k : α} {v : β} : (k, v) ∈ m.toList ↔ m.getKey? k = some k ∧ m[k]? = some v := by
  simp_to_model [toList, getKey?, getElem?]
    using List.mem_map_toProd_iff_getKey?_eq_some_and_getValue?_eq_some
theorem getKey?_eq_some_iff [EquivBEq α] [LawfulHashable α] {k k' : α} :
    m.getKey? k = some k' ↔ ∃ h : k ∈ m, m.getKey k h = k' := by
  simp_to_model [mem, getKey?, getKey] using List.getKey?_eq_some_iff'
theorem getElem?_eq_some_iff [EquivBEq α] [LawfulHashable α] {k : α} {v : β} :
    m[k]? = some v ↔ ∃ h : k ∈ m, m[k] = v := by
  simp_to_model [mem, getElem?, getElem] using List.getValue?_eq_some_iff
theorem mem_of_getKey?_eq_some [EquivBEq α] [LawfulHashable α] {k k' : α} :
    m.getKey? k = some k' → k' ∈ m := by
  simp_to_model [getKey?, mem] using List.containsKey_of_getKey?_eq_some
theorem getElem_congr [EquivBEq α] [LawfulHashable α] {a b : α} (hab : a == b) {h'} :
    m[a]'h' = m[b]'((mem_congr hab).1 h') := by
  simp_to_model [getElem] using List.getValue_congr
theorem getKey_beq [EquivBEq α] [LawfulHashable α] {k : α} (h : k ∈ m) : m.getKey k h == k := by
  simp_to_model [getKey] using List.getKey_beq
theorem getKey_congr [EquivBEq α] [LawfulHashable α] {k₁ k₂ : α} (h : k₁ == k₂)
    (h₁ : k₁ ∈ m) : m.getKey k₁ h₁ = m.getKey k₂ ((mem_congr h).mp h₁) := by
  simp_to_model [getKey] using List.getKey_congr
theorem any_eq_false_iff_forall_mem_getKey_getElem [LawfulHashable α] [EquivBEq α]
    {p : α → β → Bool} :
    m.any p = false ↔ ∀ (a : α) (h : a ∈ m), p (m.getKey a h) (m[a]'h) = false := by
  -- Std's Raw₀ text, with the Raw₀ siblings renamed to the HashMap ones and `_ h` dropped
  simp only [← any_toList, List.any_eq_false,
    mem_toList_iff_getKey?_eq_some_and_getElem?_eq_some, getKey?_eq_some_iff,
    getElem?_eq_some_iff, Bool.not_eq_true, and_imp, forall_exists_index, Prod.forall]
  constructor
  · intro h' k hk
    have hk' : m.getKey k hk ∈ m := by
      apply mem_of_getKey?_eq_some
      rw [getKey?_eq_some_iff (k := k)]
      exists hk
    apply h' _ _ hk' _ hk' (getElem_congr (getKey_beq hk))
    apply getKey_congr (getKey_beq _)
  · intro h' a b ha ha' ha₂ hb
    rw [← ha', ← hb]
    apply h'
theorem all_eq_true_iff_forall_mem_getKey_getElem [EquivBEq α] [LawfulHashable α]
    {p : (a : α) → β → Bool} :
    m.all p = true ↔ ∀ (a : α) (h : a ∈ m), p (m.getKey a h) (m[a]'h) := by
  simp [all_eq_not_any_not, any_eq_false_iff_forall_mem_getKey_getElem]
@[simp] theorem getKey_eq [LawfulBEq α] {k : α} (h : k ∈ m) : m.getKey k h = k := by
  simp_to_model [getKey] using List.getKey_eq
-- [S]
theorem all_eq_true_iff_forall_mem_getElem [LawfulBEq α] {p : α → β → Bool} :
    m.all p = true ↔ ∀ (a : α) (h : a ∈ m), p a (m[a]'h) := by
  simp [all_eq_true_iff_forall_mem_getKey_getElem, getKey_eq]

-- insertMany
theorem insertMany_ind {ρ : Type w} [ForIn Id ρ (α × β)] {motive : HashMap α β → Prop}
    (m : HashMap α β) {l : ρ} (init : motive m) (insert : ∀ m a b, motive m → motive (m.insert a b)) :
    motive (m.insertMany l) :=
  Model.insertMany_ind m init insert
-- [S]
theorem mem_insertMany_of_mem [EquivBEq α] [LawfulHashable α] {ρ : Type w} [ForIn Id ρ (α × β)]
    {l : ρ} {k : α} : k ∈ m → k ∈ m.insertMany l := by
  -- EDIT: Std's Raw₀ proof threads `WF` through `insertMany_ind`; bundled, it is 2 lines
  intro h
  exact insertMany_ind (motive := fun m => k ∈ m) m h fun m a b h => mem_insert.2 (Or.inr h)
-- [S]
theorem size_le_size_insertMany_list [EquivBEq α] [LawfulHashable α] {l : List (α × β)} :
    m.size ≤ (insertMany m l).size := by
  simp_to_model [insertMany, size] using List.length_le_length_insertListConst

-- union / inter / diff
theorem mem_of_mem_union_of_not_mem_left [EquivBEq α] [LawfulHashable α] {k : α} :
    k ∈ m₁ ∪ m₂ → ¬k ∈ m₁ → k ∈ m₂ := by
  -- Std: DHashMap-level `rw ... at h₂` + `Raw₀.contains_of_contains_union_of_contains_eq_false_left`
  simp_to_model [union, mem] using List.contains_of_contains_insertList_of_contains_eq_false_left
-- [S]
theorem getElem?_union_of_not_mem_right [EquivBEq α] [LawfulHashable α] {k : α}
    (not_mem : ¬k ∈ m₂) : (m₁ ∪ m₂)[k]? = m₁[k]? := by
  revert not_mem
  simp_to_model [union, getElem?, mem]
  intro contains_eq_false
  apply getValue?_insertList_of_contains_eq_false_right contains_eq_false
theorem getKey_union_of_not_mem_left [EquivBEq α] [LawfulHashable α] {k : α} (not_mem : ¬k ∈ m₁)
    {h'} : (m₁ ∪ m₂).getKey k h' = m₂.getKey k (mem_of_mem_union_of_not_mem_left h' not_mem) := by
  revert not_mem
  simp_to_model [union, mem, getKey] using getKey_insertList_of_contains_eq_false_left
-- [S]
@[simp] theorem contains_inter [EquivBEq α] [LawfulHashable α] {k : α} :
    (m₁ ∩ m₂).contains k = (m₁.contains k && m₂.contains k) := by
  simp_to_model [contains, inter] using List.containsKey_filter_containsKey
-- [S]
theorem not_mem_inter_of_not_mem_right [EquivBEq α] [LawfulHashable α] {k : α} (not_mem : k ∉ m₂) :
    k ∉ m₁ ∩ m₂ := by
  revert not_mem
  simp_to_model [inter, mem] using containsKey_filter_containsKey_eq_false_of_containsKey_eq_false_right
-- [S]
theorem getD_inter [EquivBEq α] [LawfulHashable α] {k : α} {fallback : β} :
    (m₁ ∩ m₂).getD k fallback = if k ∈ m₂ then m₁.getD k fallback else fallback := by
  simp_to_model [inter, getD, mem] using List.getValueD_filter_containsKey
-- [S]
theorem size_inter_le_size_right [EquivBEq α] [LawfulHashable α] : (m₁ ∩ m₂).size ≤ m₂.size := by
  simp_to_model [inter, size, contains] using List.length_filter_containsKey_le
-- [S]
theorem getKey?_diff_of_not_mem_left [EquivBEq α] [LawfulHashable α] {k : α} (not_mem : k ∉ m₁) :
    (m₁ \ m₂).getKey? k = none := by
  revert not_mem
  simp_to_model [mem, getKey?, diff]
    using List.getKey?_filter_not_contains_map_fst_of_containsKey_eq_false_left
theorem not_mem_diff_of_not_mem_left [EquivBEq α] [LawfulHashable α] {k : α} (not_mem : k ∉ m₁) :
    k ∉ m₁ \ m₂ := by
  revert not_mem
  simp_to_model [diff, mem] using List.containsKey_filter_not_contains_map_fst_eq_false_left

-- insertManyIfNewUnit / unitOfList
@[simp] theorem contains_insertManyIfNewUnit_list [EquivBEq α] [LawfulHashable α] {m : HashMap α Unit}
    {l : List α} {k : α} : (insertManyIfNewUnit m l).contains k = (m.contains k || l.contains k) := by
  simp_to_model [insertManyIfNewUnit, contains] using List.containsKey_insertListIfNewUnit
-- [S]
@[simp] theorem mem_insertManyIfNewUnit_list [EquivBEq α] [LawfulHashable α] {m : HashMap α Unit}
    {l : List α} {k : α} : k ∈ insertManyIfNewUnit m l ↔ k ∈ m ∨ l.contains k := by
  simp [← contains_iff_mem]
-- [S]
theorem getKeyD_insertManyIfNewUnit_list_of_not_mem_of_mem [EquivBEq α] [LawfulHashable α]
    {m : HashMap α Unit} {l : List α} {k k' fallback : α} (k_beq : k == k') (not_mem : ¬ k ∈ m)
    (distinct : l.Pairwise (fun a b => (a == b) = false)) (mem : k ∈ l) :
    getKeyD (insertManyIfNewUnit m l) k' fallback = k := by
  revert not_mem distinct mem
  simp_to_model [insertManyIfNewUnit, mem, getKeyD]
    using List.getKeyD_insertListIfNewUnit_of_contains_eq_false_of_mem k_beq
theorem getKey!_insertManyIfNewUnit_list_of_not_mem_of_contains_eq_false [EquivBEq α]
    [LawfulHashable α] [Inhabited α] {m : HashMap α Unit} {l : List α} {k : α} (not_mem : ¬ k ∈ m)
    (contains_eq_false : l.contains k = false) :
    getKey! (insertManyIfNewUnit m l) k = default := by
  revert not_mem contains_eq_false
  simp_to_model [insertManyIfNewUnit, mem, getKey!]
    using List.getKey!_insertListIfNewUnit_of_contains_eq_false_of_contains_eq_false
theorem getKey!_insertManyIfNewUnit_list_of_not_mem_of_mem [EquivBEq α] [LawfulHashable α]
    [Inhabited α] {m : HashMap α Unit} {l : List α} {k k' : α} (k_beq : k == k')
    (not_mem : ¬ k ∈ m) (distinct : l.Pairwise (fun a b => (a == b) = false)) (mem : k ∈ l) :
    getKey! (insertManyIfNewUnit m l) k' = k := by
  revert not_mem distinct mem
  simp_to_model [insertManyIfNewUnit, mem, getKey!]
    using List.getKey!_insertListIfNewUnit_of_contains_eq_false_of_mem k_beq
-- [S]
@[simp] theorem getElem_unitOfList {l : List α} {k : α} {h} : (unitOfList l)[k] = () := by
  simp
theorem unitOfArray_eq_unitOfList (a : Array α) : unitOfArray a = unitOfList a.toList :=
  Model.unitOfArray_eq_unitOfList a

-- alter / modify
-- [S]
theorem isEmpty_alter_eq_isEmpty_erase [EquivBEq α] [LawfulHashable α] {k : α}
    {f : Option β → Option β} :
    (alter m k f).isEmpty = ((m.erase k).isEmpty && (f m[k]?).isNone) := by
  simp_to_model [alter, erase, isEmpty, getElem?]
    using List.Const.isEmpty_alterKey_eq_isEmpty_eraseKey
-- [S]
theorem getElem?_alter [EquivBEq α] [LawfulHashable α] {k k' : α} {f : Option β → Option β} :
    (alter m k f)[k']? = if k == k' then f m[k]? else m[k']? := by
  simp_to_model [alter, getElem?] using List.Const.getValue?_alterKey
-- [S]
@[simp] theorem getElem?_alter_self [EquivBEq α] [LawfulHashable α] {k : α}
    {f : Option β → Option β} : (alter m k f)[k]? = f m[k]? := by
  simp [getElem?_alter]
-- [S]
theorem getKey!_alter [EquivBEq α] [LawfulHashable α] [Inhabited α] {k k' : α}
    {f : Option β → Option β} : (alter m k f).getKey! k' =
      if k == k' then if (f m[k]?).isSome then k else default else m.getKey! k' := by
  simp_to_model [alter, getElem?, getKey!] using List.Const.getKey!_alterKey
-- [S]
theorem getElem!_modify [EquivBEq α] [LawfulHashable α] {k k' : α} [Inhabited β] {f : β → β} :
    (modify m k f)[k']! = if k == k' then m[k]?.map f |>.get! else m[k']! := by
  simp_to_model [modify, getElem?, getElem!] using List.Const.getValue!_modifyKey

-- Equiv
-- [S]
theorem Equiv.getKeyD_eq [EquivBEq α] [LawfulHashable α] {k fallback : α} (h : m₁ ~m m₂) :
    m₁.getKeyD k fallback = m₂.getKeyD k fallback := by
  -- Std: `h.1.getKeyD_eq` → `Raw₀.getKeyD_eq_of_equiv`
  simp_to_model [getKeyD] using List.getKeyD_of_perm _ h.1
theorem Equiv.contains_eq [EquivBEq α] [LawfulHashable α] {k : α} (h : m₁ ~m m₂) :
    m₁.contains k = m₂.contains k := by
  simp_to_model [contains] using List.containsKey_of_perm h.1
theorem Equiv.mem_iff [EquivBEq α] [LawfulHashable α] {k : α} (h : m₁ ~m m₂) : k ∈ m₁ ↔ k ∈ m₂ := by
  simpa only [mem_iff_contains, Bool.coe_iff_coe] using h.contains_eq
theorem Equiv.of_forall_contains_unit_eq [LawfulBEq α] {m₁ m₂ : HashMap α Unit}
    (h : ∀ k, m₁.contains k = m₂.contains k) : m₁ ~m m₂ := by
  revert h
  simp_to_model [contains, Equiv] using List.containsKey_ext
-- [S]
theorem insertManyIfNewUnit_list_equiv_foldl {m : HashMap α Unit} {l : List α} :
    insertManyIfNewUnit m l ~m l.foldl (init := m) fun acc a => acc.insertIfNew a () := by
  -- Std's Raw₀ text (`insertManyIfNewUnit_list_equiv_foldl`), minus its `Subtype.val` detour
  rw [Model.insertManyIfNewUnit_list_eq_foldl]
  simp_to_model [Equiv] using List.Perm.refl

-- filterMap / filter / map
-- [S]
theorem mem_filterMap [EquivBEq α] [LawfulHashable α] {f : α → β → Option γ} {k : α} :
    k ∈ m.filterMap f ↔ ∃ h, (f (m.getKey k h) m[k]).isSome := by
  simp_to_model [filterMap, mem, getKey, getElem] using List.Const.containsKey_filterMap_iff
-- [S]
theorem isEmpty_filter_eq_false_iff [EquivBEq α] [LawfulHashable α] {f : α → β → Bool} :
    (m.filter f).isEmpty = false ↔ ∃ (k : α) (h : k ∈ m), f (m.getKey k h) m[k] = true := by
  simp_to_model [filter, isEmpty, mem, getKey, getElem] using List.Const.isEmpty_filter_eq_false
@[simp] theorem contains_map [EquivBEq α] [LawfulHashable α] {f : α → β → γ} {k : α} :
    (m.map f).contains k = m.contains k := by
  simp_to_model [map, contains] using List.containsKey_map
theorem mem_of_mem_map [EquivBEq α] [LawfulHashable α] {f : α → β → γ} {k : α} :
    k ∈ m.map f → k ∈ m := by
  simp [← contains_iff_mem]
-- [S]
@[simp (low)] theorem getElem?_map' [EquivBEq α] [LawfulHashable α] {f : α → β → γ} {k : α} :
    (m.map f)[k]? = m[k]?.pmap (fun v h' => f (m.getKey k h') v)
      (fun _ h' => mem_iff_isSome_getElem?.mpr (Option.isSome_of_eq_some h')) := by
  simp_to_model [map, getElem?, mem, getKey] using Const.getValue?_map
theorem getElem_map' [EquivBEq α] [LawfulHashable α] {f : α → β → γ} {k : α} {h'} :
    (m.map f)[k]'(h') = f (m.getKey k (mem_of_mem_map h')) (m[k]'(mem_of_mem_map h')) := by
  simp_to_model [map, getKey, getElem, mem] using List.getValue_map
-- [S]
@[simp] theorem getElem_map [LawfulBEq α] {f : α → β → γ} {k : α} {h'} :
    (m.map f)[k]'(h') = f k (m[k]'(mem_of_mem_map h')) := by
  simp [getElem_map', getKey_eq]
-- [S]
theorem getElem!_map_of_getKey?_eq_some [EquivBEq α] [LawfulHashable α] [Inhabited γ]
    {f : α → β → γ} {k k' : α} (h : m.getKey? k = some k') :
    (m.map f)[k]! = (m[k]?.map (f k')).get! := by
  revert h
  simp_to_model [map, getElem!, getElem?, getKey?] using Const.getValue!_map_of_getKey?_eq_some

-- the rest of the HashSet sample's HashMap siblings
theorem isEmpty_iff_forall_contains [EquivBEq α] [LawfulHashable α] :
    m.isEmpty = true ↔ ∀ a, m.contains a = false := by
  simp_to_model [isEmpty, contains] using List.isEmpty_iff_forall_containsKey
theorem isEmpty_iff_forall_not_mem [EquivBEq α] [LawfulHashable α] :
    m.isEmpty = true ↔ ∀ a, ¬a ∈ m := by
  simpa [← contains_iff_mem] using isEmpty_iff_forall_contains
@[simp] theorem size_emptyWithCapacity {c} : (emptyWithCapacity c : HashMap α β).size = 0 := by
  simp_to_model [size]; simp [Model.toListModel_emptyWithCapacity]
@[simp] theorem size_empty : (∅ : HashMap α β).size = 0 := size_emptyWithCapacity
theorem size_erase [EquivBEq α] [LawfulHashable α] {k : α} :
    (m.erase k).size = if k ∈ m then m.size - 1 else m.size := by
  simp_to_model [erase, size, mem] using List.length_eraseKey
theorem getKey?_eq_some_getKey [EquivBEq α] [LawfulHashable α] {a : α} (h : a ∈ m) :
    m.getKey? a = some (m.getKey a h) := by
  simp_to_model [getKey?, getKey] using List.getKey?_eq_some_getKey
theorem getKey?_eq_some_getKey!_of_contains [EquivBEq α] [LawfulHashable α] [Inhabited α] {a : α} :
    m.contains a = true → m.getKey? a = some (m.getKey! a) := by
  simp_to_model [contains, getKey?, getKey!] using List.getKey?_eq_some_getKey!
theorem getKey?_eq_some_getKey! [EquivBEq α] [LawfulHashable α] [Inhabited α] {a : α} :
    a ∈ m → m.getKey? a = some (m.getKey! a) := by
  simpa [← contains_iff_mem] using getKey?_eq_some_getKey!_of_contains
theorem fold_eq_foldl_keys {f : δ → α → δ} {init : δ} :
    m.fold (fun d a _ => f d a) init = m.keys.foldl f init := by
  simp_to_model [fold, keys] using List.foldl_eq_foldl_keys
theorem any_eq_false_iff_forall_mem_getElem [LawfulBEq α] {p : α → β → Bool} :
    m.any p = false ↔ ∀ (a : α) (h : a ∈ m), p a (m[a]'h) = false := by
  simp [any_eq_false_iff_forall_mem_getKey_getElem, getKey_eq]


namespace AtStar
theorem getKey?_diff_of_not_mem_left [EquivBEq α] [LawfulHashable α] {k : α} (not_mem : k ∉ m₁) :
    (m₁ \ m₂).getKey? k = none := by
  simp_to_model [mem, getKey?, diff] at * using List.getKey?_filter_not_contains_map_fst_of_containsKey_eq_false_left
theorem not_mem_inter_of_not_mem_right [EquivBEq α] [LawfulHashable α] {k : α} (not_mem : k ∉ m₂) :
    k ∉ m₁ ∩ m₂ := by
  simp_to_model [inter, mem] at * using containsKey_filter_containsKey_eq_false_of_containsKey_eq_false_right
theorem getKeyD_insertManyIfNewUnit_list_of_not_mem_of_mem [EquivBEq α] [LawfulHashable α]
    {m : HashMap α Unit} {l : List α} {k k' fallback : α} (k_beq : k == k') (not_mem : ¬ k ∈ m)
    (distinct : l.Pairwise (fun a b => (a == b) = false)) (mem : k ∈ l) :
    getKeyD (insertManyIfNewUnit m l) k' fallback = k := by
  simp_to_model [insertManyIfNewUnit, mem, getKeyD] at *
    using List.getKeyD_insertListIfNewUnit_of_contains_eq_false_of_mem
theorem getElem!_map_of_getKey?_eq_some [EquivBEq α] [LawfulHashable α] [Inhabited γ]
    {f : α → β → γ} {k k' : α} (h : m.getKey? k = some k') :
    (m.map f)[k]! = (m[k]?.map (f k')).get! := by
  simp_to_model [map, getElem!, getElem?, getKey?] at * using Const.getValue!_map_of_getKey?_eq_some
theorem getKey_union_of_not_mem_left [EquivBEq α] [LawfulHashable α] {k : α} (not_mem : ¬k ∈ m₁)
    {h'} : (m₁ ∪ m₂).getKey k h' = m₂.getKey k (mem_of_mem_union_of_not_mem_left h' not_mem) := by
  simp_to_model [union, mem, getKey] at * using getKey_insertList_of_contains_eq_false_left
end AtStar
end HashMap

/-! ## HashSet: Std's wrapper; every proof below is Std's text verbatim -/

structure HashSet (α : Type u) [BEq α] [Hashable α] where
  inner : HashMap α Unit

namespace HashSet

variable {α : Type u} {δ : Type w} [BEq α] [Hashable α] {m m₁ m₂ : HashSet α}

instance : EmptyCollection (HashSet α) := ⟨⟨∅⟩⟩
instance : Membership α (HashSet α) where mem m a := a ∈ m.inner
instance {m : HashSet α} {a : α} : Decidable (a ∈ m) := inferInstanceAs (Decidable (a ∈ m.inner))
def contains (m : HashSet α) (a : α) : Bool := m.inner.contains a
def erase (m : HashSet α) (a : α) : HashSet α := ⟨m.inner.erase a⟩
def size (m : HashSet α) : Nat := m.inner.size
def isEmpty (m : HashSet α) : Bool := m.inner.isEmpty
def get? (m : HashSet α) (a : α) : Option α := m.inner.getKey? a
def get (m : HashSet α) (a : α) (h : a ∈ m) : α := m.inner.getKey a h
def get! [Inhabited α] (m : HashSet α) (a : α) : α := m.inner.getKey! a
def getD (m : HashSet α) (a : α) (fallback : α) : α := m.inner.getKeyD a fallback
def fold (f : δ → α → δ) (init : δ) (m : HashSet α) : δ := m.inner.fold (fun d a _ => f d a) init
def toList (m : HashSet α) : List α := m.inner.keys
def any (m : HashSet α) (p : α → Bool) : Bool := m.inner.any fun a _ => p a
def insertMany {ρ : Type w} [ForIn Id ρ α] (m : HashSet α) (l : ρ) : HashSet α :=
  ⟨m.inner.insertManyIfNewUnit l⟩
def ofList (l : List α) : HashSet α := ⟨HashMap.unitOfList l⟩
def ofArray (l : Array α) : HashSet α := ⟨HashMap.unitOfArray l⟩
instance : Union (HashSet α) := ⟨fun m₁ m₂ => ⟨m₁.inner ∪ m₂.inner⟩⟩
instance : SDiff (HashSet α) := ⟨fun m₁ m₂ => ⟨m₁.inner \ m₂.inner⟩⟩
structure Equiv (m₁ m₂ : HashSet α) : Prop where
  inner : m₁.1.Equiv m₂.1
scoped infixl:50 " ~m " => Equiv

private theorem ext {m m' : HashSet α} : m.inner = m'.inner → m = m' := by
  cases m; cases m'; rintro rfl; rfl

theorem mem_congr [EquivBEq α] [LawfulHashable α] {a b : α} (hab : a == b) : a ∈ m ↔ b ∈ m :=
  HashMap.mem_congr hab
theorem mem_of_mem_union_of_not_mem_left [EquivBEq α] [LawfulHashable α] {k : α} :
    k ∈ m₁ ∪ m₂ → ¬k ∈ m₁ → k ∈ m₂ :=
  @HashMap.mem_of_mem_union_of_not_mem_left _ _ _ _ m₁.inner m₂.inner _ _ k

-- [S] ×16
theorem isEmpty_iff_forall_not_mem [EquivBEq α] [LawfulHashable α] :
    m.isEmpty = true ↔ ∀ a, ¬a ∈ m :=
  HashMap.isEmpty_iff_forall_not_mem
@[simp] theorem size_empty : (∅ : HashSet α).size = 0 :=
  HashMap.size_empty
theorem size_erase [EquivBEq α] [LawfulHashable α] {k : α} :
    (m.erase k).size = if k ∈ m then m.size - 1 else m.size :=
  HashMap.size_erase
theorem get?_eq_some_get [EquivBEq α] [LawfulHashable α] {a : α} (h' : a ∈ m) :
    m.get? a = some (m.get a h') :=
  HashMap.getKey?_eq_some_getKey h'
theorem get_congr [EquivBEq α] [LawfulHashable α] {k₁ k₂ : α} (h : k₁ == k₂)
    (h₁ : k₁ ∈ m) : m.get k₁ h₁ = m.get k₂ ((mem_congr h).mp h₁) :=
  HashMap.getKey_congr h h₁
theorem get?_eq_some_get! [EquivBEq α] [LawfulHashable α] [Inhabited α] {a : α} :
    a ∈ m → m.get? a = some (m.get! a) :=
  HashMap.getKey?_eq_some_getKey!
theorem fold_eq_foldl_toList {f : δ → α → δ} {init : δ} :
    m.fold f init = m.toList.foldl f init :=
  HashMap.fold_eq_foldl_keys
theorem any_eq_false_iff_forall_mem [LawfulBEq α] {p : α → Bool} :
    m.any p = false ↔ ∀ (a : α), a ∈ m → p a = false := by
  simpa using! @HashMap.any_eq_false_iff_forall_mem_getElem _ _ _ _ _ _ (fun a b => p a)
theorem get!_insertMany_list_of_not_mem_of_contains_eq_false
    [EquivBEq α] [LawfulHashable α] [Inhabited α] {l : List α} {k : α}
    (not_mem : ¬ k ∈ m) (contains_eq_false : l.contains k = false) :
    get! (insertMany m l) k = default :=
  HashMap.getKey!_insertManyIfNewUnit_list_of_not_mem_of_contains_eq_false
    not_mem contains_eq_false
theorem get!_insertMany_list_of_not_mem_of_mem [EquivBEq α] [LawfulHashable α]
    [Inhabited α] {l : List α} {k k' : α} (k_beq : k == k')
    (not_mem : ¬ k ∈ m)
    (distinct : l.Pairwise (fun a b => (a == b) = false)) (mem : k ∈ l) :
    get! (insertMany m l) k' = k :=
  HashMap.getKey!_insertManyIfNewUnit_list_of_not_mem_of_mem
    k_beq not_mem distinct mem
theorem getD_insertMany_list_of_not_mem_of_mem [EquivBEq α] [LawfulHashable α]
    {l : List α} {k k' fallback : α} (k_beq : k == k')
    (not_mem : ¬ k ∈ m)
    (distinct : l.Pairwise (fun a b => (a == b) = false)) (mem : k ∈ l)  :
    getD (insertMany m l) k' fallback = k :=
  HashMap.getKeyD_insertManyIfNewUnit_list_of_not_mem_of_mem
    k_beq not_mem distinct mem
theorem get_union_of_not_mem_left [EquivBEq α] [LawfulHashable α]
    {k : α} (not_mem : ¬k ∈ m₁) {h'} :
    (m₁ ∪ m₂).get k h' = m₂.get k (mem_of_mem_union_of_not_mem_left h' not_mem) :=
  @HashMap.getKey_union_of_not_mem_left _ _ _ _ m₁.inner m₂.inner _ _  k not_mem h'
theorem not_mem_diff_of_not_mem_left [EquivBEq α] [LawfulHashable α] {k : α}
    (not_mem : k ∉ m₁) :
    k ∉ m₁ \ m₂ :=
  @HashMap.not_mem_diff_of_not_mem_left _ _ _ _ m₁.inner m₂.inner _ _ k not_mem
theorem ofArray_eq_ofList (a : Array α) :
    ofArray a = ofList a.toList := by
  apply ext
  apply HashMap.unitOfArray_eq_unitOfList
theorem Equiv.mem_iff [EquivBEq α] [LawfulHashable α] {k : α} (h : m₁ ~m m₂) : k ∈ m₁ ↔ k ∈ m₂ :=
  h.1.mem_iff
theorem Equiv.of_forall_contains_eq [LawfulBEq α] (h : ∀ k, m₁.contains k = m₂.contains k) :
    m₁ ~m m₂ :=
  ⟨.of_forall_contains_unit_eq h⟩

end HashSet

end Mock
