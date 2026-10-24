module

public import OAMap.Core.Table

/-!
# Derived queries and traversals of the core

The one-line definitions `get?`, `get`, `getD`, `get!`, `getKey?`, `getKey`, `getKeyD`,
`getKey!`, `isEmpty`, `fold`, `forM`, `toList`, `keys`, `values`, `toArray`, `keysArray`,
`valuesArray`, `all` and `any` over the core primitives, and their Table-level model lemmas,
including the Table-level twins of Std's non-bulk `ext DHashMap.X` equalities
(`docs/ARCHITECTURE.md` §4.1, `docs/proofs.md` §4).

Layout-free: this file uses only the 45 contract names of `OAMap.Core.Table` (§3), so it is the
same for every core (checked by `test/OAMapTest/SealCheck.lean`). Rules (§2.3):

* The section is `public` but not `@[expose]`d, so the HashMap layer sees the statements and
  cannot unfold the definitions.
* No lemma is proved by a bare `rfl`: they are proved by `unfold` followed by rewriting with the
  contract lemmas, so none becomes a definitional (`dsimp`) lemma (`proofs.md` §9.8).
* Hypotheses: a lemma is **U** (no hypotheses on `BEq`/`Hashable`) when it follows from the U
  contract lemmas alone, and **L** (`[EquivBEq α] [LawfulHashable α]`) when it needs `lookup_eq`
  or `lookupMem_eq`. The twins of Std's `ext DHashMap.X` equalities take all their arguments
  implicitly, as Std's do, so that `ext Core.Table.X` elaborates.

Owner: GEN, Wave 1.
-/

public section

universe u v w w'

open Std.Internal.List

namespace OAMap.Core.Table

/-! ## Definitions -/

section Defs

variable {α : Type u} {β : Type v} [BEq α] [Hashable α]

/-- The value stored for `a`, if any. -/
@[inline] def get? (t : Table α β) (a : α) : Option β :=
  t.lookup a (fun _ v => some v) (fun _ => none)

/-- The value stored for `a`, which is known to be present. -/
@[inline] def get (t : Table α β) (a : α) (h : t.contains a = true) : β :=
  t.lookupMem a h (fun _ v => v)

/-- The value stored for `a`, or `fallback` if `a` is absent. -/
@[inline] def getD (t : Table α β) (a : α) (fallback : β) : β :=
  t.lookup a (fun _ v => v) (fun _ => fallback)

/-- The value stored for `a`; panics if `a` is absent. -/
@[inline] def get! [Inhabited β] (t : Table α β) (a : α) : β :=
  t.lookup a (fun _ v => v) (fun _ => panic! "key is not present in hash table")

/-- The stored key that is `==` to `a`, if any. -/
@[inline] def getKey? (t : Table α β) (a : α) : Option α :=
  t.lookup a (fun k _ => some k) (fun _ => none)

/-- The stored key that is `==` to `a`, which is known to be present. -/
@[inline] def getKey (t : Table α β) (a : α) (h : t.contains a = true) : α :=
  t.lookupMem a h (fun k _ => k)

/-- The stored key that is `==` to `a`, or `fallback` if `a` is absent. -/
@[inline] def getKeyD (t : Table α β) (a fallback : α) : α :=
  t.lookup a (fun k _ => k) (fun _ => fallback)

/-- The stored key that is `==` to `a`; panics if `a` is absent. -/
@[inline] def getKey! [Inhabited α] (t : Table α β) (a : α) : α :=
  t.lookup a (fun k _ => k) (fun _ => panic! "key is not present in hash table")

/-- Whether the table has no entries. -/
@[inline] def isEmpty (t : Table α β) : Bool :=
  t.size == 0

/-- Left fold over the entries, in model order. -/
@[inline] def fold {δ : Type w} (f : δ → α → β → δ) (init : δ) (t : Table α β) : δ :=
  Id.run (t.foldM (pure <| f · · ·) init)

/-- Runs `f` on every entry, in model order. -/
@[inline] def forM {m : Type w → Type w'} [Monad m] (f : α → β → m PUnit) (t : Table α β) :
    m PUnit :=
  t.foldM (fun _ k v => f k v) ⟨⟩

/-- The entries as a list of pairs, in model order (built by consing from the back). -/
@[inline] def toList (t : Table α β) : List (α × β) :=
  t.foldRev (fun acc k v => (k, v) :: acc) []

/-- The keys, in model order. -/
@[inline] def keys (t : Table α β) : List α :=
  t.foldRev (fun acc k _ => k :: acc) []

/-- The values, in model order. -/
@[inline] def values (t : Table α β) : List β :=
  t.foldRev (fun acc _ v => v :: acc) []

/-- The entries as an array of pairs, in model order. -/
@[inline] def toArray (t : Table α β) : Array (α × β) :=
  t.fold (fun acc k v => acc.push (k, v)) (.emptyWithCapacity t.size)

/-- The keys as an array, in model order. -/
@[inline] def keysArray (t : Table α β) : Array α :=
  t.fold (fun acc k _ => acc.push k) (.emptyWithCapacity t.size)

/-- The values as an array, in model order. -/
@[inline] def valuesArray (t : Table α β) : Array β :=
  t.fold (fun acc _ v => acc.push v) (.emptyWithCapacity t.size)

/-- Whether every entry satisfies `p`; stops at the first entry that does not. -/
@[inline] def all (t : Table α β) (p : α → β → Bool) : Bool :=
  Id.run (t.forIn (fun k v _ => if p k v then pure (.yield true) else pure (.done false)) true)

/-- Whether some entry satisfies `p`; stops at the first entry that does. -/
@[inline] def any (t : Table α β) (p : α → β → Bool) : Bool :=
  Id.run (t.forIn (fun k v _ => if p k v then pure (.done true) else pure (.yield false)) false)

end Defs

/-! ## Lemmas -/

section Lemmas

variable {α : Type u} {β : Type v} {_ : BEq α} {_ : Hashable α}

/-- `panic!` is `default` in the logic. -/
private theorem panic_eq_default {γ : Sort w} [Inhabited γ] {modName declName : String}
    {line col : Nat} {msg : String} :
    panicWithPosWithDecl modName declName line col msg = (default : γ) := by
  unfold panicWithPosWithDecl panic panicCore
  exact Eq.refl _

/-! ### Queries (L) -/

theorem contains_eq_containsKey [EquivBEq α] [LawfulHashable α] (t : Table α β) (a : α) :
    t.contains a = containsKey a t.toListModel := by
  rw [contains_eq_lookup, lookup_eq, containsKey_eq_isSome_getEntry?]
  cases getEntry? a t.toListModel <;> exact Eq.refl _

theorem get?_eq_getValue? [EquivBEq α] [LawfulHashable α] (t : Table α β) (a : α) :
    t.get? a = getValue? a t.toListModel := by
  unfold get?
  rw [lookup_eq, getValue?_eq_getEntry?]
  cases getEntry? a t.toListModel <;> exact Eq.refl _

theorem get_eq_getValue [EquivBEq α] [LawfulHashable α] (t : Table α β) (a : α)
    (h : t.contains a = true) :
    t.get a h = getValue a t.toListModel ((contains_eq_containsKey t a).symm.trans h) := by
  have hc : containsKey a t.toListModel = true := (contains_eq_containsKey t a).symm.trans h
  have hv := getValue?_eq_some_getValue hc
  rw [getValue?_eq_getEntry?] at hv
  cases he : getEntry? a t.toListModel with
  | none => rw [he] at hv; cases hv
  | some e =>
    rw [he] at hv
    unfold get
    rw [lookupMem_eq t a h _ he]
    exact Option.some.inj hv

theorem getD_eq_getValueD [EquivBEq α] [LawfulHashable α] (t : Table α β) (a : α)
    (fallback : β) : t.getD a fallback = getValueD a t.toListModel fallback := by
  unfold getD
  rw [lookup_eq, getValueD_eq_getValue?, getValue?_eq_getEntry?]
  cases getEntry? a t.toListModel <;> exact Eq.refl _

theorem get!_eq_getValue! [EquivBEq α] [LawfulHashable α] [Inhabited β] (t : Table α β)
    (a : α) : t.get! a = getValue! a t.toListModel := by
  unfold get!
  rw [lookup_eq, getValue!_eq_getValue?, getValue?_eq_getEntry?]
  cases getEntry? a t.toListModel with
  | none => exact panic_eq_default.trans Option.get!_none.symm
  | some e => exact Eq.refl _

theorem getKey?_eq_getKey? [EquivBEq α] [LawfulHashable α] (t : Table α β) (a : α) :
    t.getKey? a = Std.Internal.List.getKey? a t.toListModel := by
  unfold getKey?
  rw [lookup_eq, Std.Internal.List.getKey?_eq_getEntry?]
  cases getEntry? a t.toListModel <;> exact Eq.refl _

theorem getKey_eq_getKey [EquivBEq α] [LawfulHashable α] (t : Table α β) (a : α)
    (h : t.contains a = true) :
    t.getKey a h =
      Std.Internal.List.getKey a t.toListModel ((contains_eq_containsKey t a).symm.trans h) := by
  have hc : containsKey a t.toListModel = true := (contains_eq_containsKey t a).symm.trans h
  have hk := Std.Internal.List.getKey?_eq_some_getKey hc
  rw [Std.Internal.List.getKey?_eq_getEntry?] at hk
  cases he : getEntry? a t.toListModel with
  | none => rw [he] at hk; cases hk
  | some e =>
    rw [he] at hk
    unfold getKey
    rw [lookupMem_eq t a h _ he]
    exact Option.some.inj hk

theorem getKeyD_eq_getKeyD [EquivBEq α] [LawfulHashable α] (t : Table α β) (a fallback : α) :
    t.getKeyD a fallback = Std.Internal.List.getKeyD a t.toListModel fallback := by
  unfold getKeyD
  rw [lookup_eq, Std.Internal.List.getKeyD_eq_getKey?, Std.Internal.List.getKey?_eq_getEntry?]
  cases getEntry? a t.toListModel <;> exact Eq.refl _

theorem getKey!_eq_getKey! [EquivBEq α] [LawfulHashable α] [Inhabited α] (t : Table α β)
    (a : α) : t.getKey! a = Std.Internal.List.getKey! a t.toListModel := by
  unfold getKey!
  rw [lookup_eq, Std.Internal.List.getKey!_eq_getKey?, Std.Internal.List.getKey?_eq_getEntry?]
  cases getEntry? a t.toListModel with
  | none => exact panic_eq_default.trans Option.get!_none.symm
  | some e => exact Eq.refl _

/-! ### Size and emptiness (U) -/

theorem isEmpty_eq_size_eq_zero (t : Table α β) : t.isEmpty = (t.size == 0) := by
  unfold isEmpty
  exact Eq.refl _

theorem isEmpty_eq_isEmpty (t : Table α β) : t.isEmpty = t.toListModel.isEmpty := by
  unfold isEmpty
  rw [size_eq_length]
  cases t.toListModel <;> exact Eq.refl _

/-! ### Queries on the empty table (U) -/

theorem size_emptyWithCapacity {c : Nat} : (emptyWithCapacity c : Table α β).size = 0 := by
  rw [size_eq_length, toListModel_emptyWithCapacity]
  exact Eq.refl _

theorem isEmpty_emptyWithCapacity {c : Nat} :
    (emptyWithCapacity c : Table α β).isEmpty = true := by
  rw [isEmpty_eq_isEmpty, toListModel_emptyWithCapacity]
  exact Eq.refl _

theorem toList_emptyWithCapacity {c : Nat} : (emptyWithCapacity c : Table α β).toList = [] := by
  unfold toList
  rw [foldRev_eq_foldr_toListModel, toListModel_emptyWithCapacity, List.foldr_nil]

theorem keys_emptyWithCapacity {c : Nat} : (emptyWithCapacity c : Table α β).keys = [] := by
  unfold keys
  rw [foldRev_eq_foldr_toListModel, toListModel_emptyWithCapacity, List.foldr_nil]

theorem values_emptyWithCapacity {c : Nat} : (emptyWithCapacity c : Table α β).values = [] := by
  unfold values
  rw [foldRev_eq_foldr_toListModel, toListModel_emptyWithCapacity, List.foldr_nil]

theorem contains_emptyWithCapacity {c : Nat} {a : α} :
    (emptyWithCapacity c : Table α β).contains a = false := by
  rw [contains_eq_lookup, lookup_emptyWithCapacity]

theorem get?_emptyWithCapacity {c : Nat} {a : α} :
    (emptyWithCapacity c : Table α β).get? a = none := by
  unfold get?
  rw [lookup_emptyWithCapacity]

theorem getD_emptyWithCapacity {c : Nat} {a : α} {fallback : β} :
    (emptyWithCapacity c : Table α β).getD a fallback = fallback := by
  unfold getD
  rw [lookup_emptyWithCapacity]

theorem get!_emptyWithCapacity [Inhabited β] {c : Nat} {a : α} :
    (emptyWithCapacity c : Table α β).get! a = default := by
  unfold get!
  rw [lookup_emptyWithCapacity]
  exact panic_eq_default

theorem getKey?_emptyWithCapacity {c : Nat} {a : α} :
    (emptyWithCapacity c : Table α β).getKey? a = none := by
  unfold getKey?
  rw [lookup_emptyWithCapacity]

theorem getKeyD_emptyWithCapacity {c : Nat} {a fallback : α} :
    (emptyWithCapacity c : Table α β).getKeyD a fallback = fallback := by
  unfold getKeyD
  rw [lookup_emptyWithCapacity]

theorem getKey!_emptyWithCapacity [Inhabited α] {c : Nat} {a : α} :
    (emptyWithCapacity c : Table α β).getKey! a = default := by
  unfold getKey!
  rw [lookup_emptyWithCapacity]
  exact panic_eq_default

/-! ### Traversals (U) -/

theorem fold_eq_foldl_toListModel {δ : Type w} (t : Table α β) (f : δ → α → β → δ)
    (init : δ) : t.fold f init = t.toListModel.foldl (fun a b => f a b.1 b.2) init := by
  unfold fold
  rw [foldM_eq_foldlM_toListModel, List.idRun_foldlM]
  exact Eq.refl _

theorem forM_eq_forM_toListModel {m : Type w → Type w'} [Monad m] [LawfulMonad m]
    (t : Table α β) (f : α → β → m PUnit) :
    t.forM f = t.toListModel.forM (fun a => f a.1 a.2) := by
  unfold forM
  rw [foldM_eq_foldlM_toListModel]
  induction t.toListModel with
  | nil => exact Eq.refl _
  | cons hd tl ih =>
    rw [List.foldlM_cons]
    exact congrArg (f hd.1 hd.2 >>= ·) (funext fun _ => ih)

theorem toList_eq_toListModel_map (t : Table α β) :
    t.toList = t.toListModel.map fun x => (x.1, x.2) := by
  unfold toList
  rw [foldRev_eq_foldr_toListModel, List.map_eq_foldr]

theorem keys_eq_keys_toListModel (t : Table α β) :
    t.keys = Std.Internal.List.keys t.toListModel := by
  unfold keys
  rw [foldRev_eq_foldr_toListModel, keys_eq_map, List.map_eq_foldr]

theorem values_eq_values_toListModel (t : Table α β) :
    t.values = Std.Internal.List.values t.toListModel := by
  unfold values
  rw [foldRev_eq_foldr_toListModel, values_eq_map, List.map_eq_foldr]

theorem toArray_eq_toArray_map_toListModel (t : Table α β) :
    t.toArray = (t.toListModel.map fun x => (x.1, x.2)).toArray := by
  unfold toArray
  rw [fold_eq_foldl_toListModel, Array.emptyWithCapacity_eq, List.foldl_push_eq_append,
    Array.empty_append]

theorem keysArray_eq_toArray_keys_toListModel (t : Table α β) :
    t.keysArray = (Std.Internal.List.keys t.toListModel).toArray := by
  unfold keysArray
  rw [fold_eq_foldl_toListModel, Array.emptyWithCapacity_eq, List.foldl_push_eq_append,
    Array.empty_append, keys_eq_map]

theorem valuesArray_eq_toArray_values_toListModel (t : Table α β) :
    t.valuesArray = (Std.Internal.List.values t.toListModel).toArray := by
  unfold valuesArray
  rw [fold_eq_foldl_toListModel, Array.emptyWithCapacity_eq, List.foldl_push_eq_append,
    Array.empty_append, values_eq_map]

theorem all_eq_all_toListModel (t : Table α β) (p : α → β → Bool) :
    t.all p = t.toListModel.all fun x => p x.1 x.2 := by
  unfold all
  rw [forIn_eq_forIn_toListModel]
  induction t.toListModel with
  | nil => exact Eq.refl _
  | cons hd tl ih =>
    rw [List.forIn_cons, List.all_cons]
    cases p hd.1 hd.2
    · exact Eq.refl _
    · exact ih

theorem any_eq_any_toListModel (t : Table α β) (p : α → β → Bool) :
    t.any p = t.toListModel.any fun x => p x.1 x.2 := by
  unfold any
  rw [forIn_eq_forIn_toListModel]
  induction t.toListModel with
  | nil => exact Eq.refl _
  | cons hd tl ih =>
    rw [List.forIn_cons, List.any_cons]
    cases p hd.1 hd.2
    · exact ih
    · exact Eq.refl _

/-! ### Twins of Std's non-bulk `ext DHashMap.X` equalities (U, implicit arguments) -/

theorem erase_empty {a : α} :
    (emptyWithCapacity 8 : Table α β).erase a = emptyWithCapacity 8 :=
  erase_emptyWithCapacity

theorem containsThenInsert_fst {t : Table α β} {a : α} {b : β} :
    (t.containsThenInsert a b).1 = t.contains a := by
  rw [containsThenInsert_eq]

theorem containsThenInsert_snd {t : Table α β} {a : α} {b : β} :
    (t.containsThenInsert a b).2 = t.insert a b := by
  rw [containsThenInsert_eq]

theorem containsThenInsertIfNew_fst {t : Table α β} {a : α} {b : β} :
    (t.containsThenInsertIfNew a b).1 = t.contains a := by
  rw [containsThenInsertIfNew_eq]

theorem containsThenInsertIfNew_snd {t : Table α β} {a : α} {b : β} :
    (t.containsThenInsertIfNew a b).2 = t.insertIfNew a b := by
  rw [containsThenInsertIfNew_eq]

theorem getThenInsertIfNew?_fst {t : Table α β} {a : α} {b : β} :
    (t.getThenInsertIfNew? a b).1 = t.get? a := by
  rw [getThenInsertIfNew?_eq]
  unfold get?
  exact Eq.refl _

theorem getThenInsertIfNew?_snd {t : Table α β} {a : α} {b : β} :
    (t.getThenInsertIfNew? a b).2 = t.insertIfNew a b := by
  rw [getThenInsertIfNew?_eq]

theorem map_fst_toArray_eq_keysArray {t : Table α β} :
    t.toArray.map Prod.fst = t.keysArray := by
  rw [toArray_eq_toArray_map_toListModel, keysArray_eq_toArray_keys_toListModel, List.map_toArray,
    List.map_map, keys_eq_map]
  exact Eq.refl _

end Lemmas

end OAMap.Core.Table
