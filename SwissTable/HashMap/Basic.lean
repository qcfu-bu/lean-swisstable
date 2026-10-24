/-
Copyright (c) 2024 Lean FRO, LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Markus Himmel
-/
module

public import SwissTable.Core.Bulk

@[expose] public section

set_option linter.missingDocs true
set_option autoImplicit false

/-!
# Hash maps

This module develops the type `SwissTable.HashMap` of hash maps, a drop-in replacement for
`Std.HashMap`: the same operations, with Std's names, binders, attributes and semantics.

The operations `map` and `filterMap` on `SwissTable.HashMap` are defined in the module
`SwissTable.HashMap.AdditionalOperations`.

Lemmas about the operations on `SwissTable.HashMap` are available in the
module `SwissTable.HashMap.Lemmas`.

Implementation notes (`docs/ARCHITECTURE.md` §4.3). This file is Std's
`Std/Data/HashMap/Basic.lean`, generated from Std's text so that binders, attributes, declaration
order and auto-generated instance names are Std's; only the bodies differ. A map is a one-field
wrapper of the sealed core table `SwissTable.Core.Table` (§3), and every operation is a one-line
call to a core, `SwissTable.Core.Derived` or `SwissTable.Core.Bulk` function. Docstrings that Std
inherits from `DHashMap` are copied as literal text. The file also defines
`SwissTable.Model.toListModel`, the entry list that `Equiv` and all lemmas are stated against.
`Array.groupByKey` and `List.groupByKey` stay Std's (they return `Std.HashMap`).

Owner: API, Wave 1.
-/

universe u v w w'

variable {α : Type u} {β : Type v} {_ : BEq α} {_ : Hashable α}

namespace SwissTable

/--
Hash maps.

This is a drop-in replacement for `Std.HashMap`, with the same operations, lemmas and semantics.
The data of the hash map is a hash table (`SwissTable.Core.Table`) whose layout is an implementation
detail: no lemma depends on it, and every lemma is stated in terms of the operations, exactly as
for `Std.HashMap`.

Users should make sure that the hash map is used linearly to avoid expensive copies.

The hash map uses `==` (provided by the `BEq` typeclass) to compare keys and `hash` (provided by
the `Hashable` typeclass) to hash them. To ensure that the operations behave as expected, `==`
should be an equivalence relation and `a == b` should imply `hash a = hash b` (see also the
`EquivBEq` and `LawfulHashable` typeclasses). Both of these conditions are automatic if the BEq
instance is lawful, i.e., if `a == b` implies `a = b`.

These hash maps contain a bundled well-formedness invariant, which means that they cannot
be used in nested inductive types.
-/
structure HashMap (α : Type u) (β : Type v) [BEq α] [Hashable α] where
  /-- Internal implementation detail of the hash map -/
  inner : SwissTable.Core.Table α β

namespace HashMap

/-- The entries of a map in iteration order: the model that `Equiv` and all lemmas are stated
against (ARCHITECTURE.md §2.3). The core's `Table.toListModel` below it stays sealed. -/
def _root_.SwissTable.Model.toListModel (m : HashMap α β) : List ((_ : α) × β) :=
  m.inner.toListModel

/--
Creates a new empty hash map. The optional parameter `capacity` can be supplied to presize the
map so that it can hold the given number of mappings without reallocating. It is also possible to
use the empty collection notations `∅` and `{}` to create an empty hash map with the default
capacity.
-/
@[cbv_opaque, inline] def emptyWithCapacity [BEq α] [Hashable α] (capacity := 8) :
    HashMap α β :=
  ⟨Core.Table.emptyWithCapacity capacity⟩

instance [BEq α] [Hashable α] : EmptyCollection (HashMap α β) where
  emptyCollection := emptyWithCapacity

instance [BEq α] [Hashable α] : Inhabited (HashMap α β) where
  default := ∅

/--
Marks a hash map as linear, which is a no-op logically.

At runtime the bucket array backing the map is first made unique, copying it if the reference is not
already unique, and then marked. If the environment variable `LEAN_ABORT_ON_NONLINEAR` is set,
every non-linear use from that point on causes a panic instead of a silent copy.

To debug where the non-linearity is coming from you can set a breakpoint on `lean_internal_panic`.
-/
@[never_extract, inline] def markLinear (m : HashMap α β) : HashMap α β :=
  ⟨m.inner.markLinear⟩

@[simp, grind =] theorem markLinear_eq {m : HashMap α β} : m.markLinear = m := rfl

/--
Two hash maps are equivalent in the sense of `Equiv` iff
all the keys and values are equal.
-/
structure Equiv (m₁ m₂ : HashMap α β) where
  /-- Internal implementation detail of the hash map -/
  inner : (Model.toListModel m₁).Perm (Model.toListModel m₂)

@[inherit_doc] scoped infixl:50 " ~m " => Equiv

/--
Inserts the given mapping into the map. If there is already a mapping for the given key, then both
key and value will be replaced.

Note: this replacement behavior is true for `HashMap`, `DHashMap`, `HashMap.Raw` and `DHashMap.Raw`.
The `insert` function on `HashSet` and `HashSet.Raw` behaves differently: it will return the set
unchanged if a matching key is already present.
-/
@[cbv_opaque, inline] def insert (m : HashMap α β) (a : α)
    (b : β) : HashMap α β :=
  ⟨m.inner.insert a b⟩

instance : Singleton (α × β) (HashMap α β) := ⟨fun ⟨a, b⟩ => (∅ : HashMap α β).insert a b⟩

instance : Insert (α × β) (HashMap α β) := ⟨fun ⟨a, b⟩ s => s.insert a b⟩

instance : LawfulSingleton (α × β) (HashMap α β) := ⟨fun _ => rfl⟩

/--
If there is no mapping for the given key, inserts the given mapping into the map. Otherwise,
returns the map unaltered.
-/
@[inline] def insertIfNew (m : HashMap α β)
    (a : α) (b : β) : HashMap α β :=
  ⟨m.inner.insertIfNew a b⟩

/--
Checks whether a key is present in a map, and unconditionally inserts a value for the key.

Equivalent to (but potentially faster than) calling `contains` followed by `insert`.
-/
@[inline] def containsThenInsert
    (m : HashMap α β) (a : α) (b : β) : Bool × HashMap α β :=
  let ⟨replaced, r⟩ := m.inner.containsThenInsert a b
  ⟨replaced, ⟨r⟩⟩

/--
Checks whether a key is present in a map and inserts a value for the key if it was not found.

If the returned `Bool` is `true`, then the returned map is unaltered. If the `Bool` is `false`, then
the returned map has a new value inserted.

Equivalent to (but potentially faster than) calling `contains` followed by `insertIfNew`.
-/
@[inline] def containsThenInsertIfNew
    (m : HashMap α β) (a : α) (b : β) : Bool × HashMap α β :=
  let ⟨replaced, r⟩ := m.inner.containsThenInsertIfNew a b
  ⟨replaced, ⟨r⟩⟩

/--
Checks whether a key is present in a map, returning the associated value, and inserts a value for
the key if it was not found.

If the returned value is `some v`, then the returned map is unaltered. If it is `none`, then the
returned map has a new value inserted.

Equivalent to (but potentially faster than) calling `get?` followed by `insertIfNew`.
-/
@[inline] def getThenInsertIfNew? (m : HashMap α β) (a : α) (b : β) :
    Option β × HashMap α β :=
  let ⟨previous, r⟩ := m.inner.getThenInsertIfNew? a b
  ⟨previous, ⟨r⟩⟩

/--
The notation `m[a]?` is preferred over calling this function directly.

Tries to retrieve the mapping for the given key, returning `none` if no such mapping is present.
-/
@[inline] def get? (m : HashMap α β) (a : α) : Option β :=
  m.inner.get? a

/--
Returns `true` if there is a mapping for the given key. There is also a `Prop`-valued version
of this: `a ∈ m` is equivalent to `m.contains a = true`.

Observe that this is different behavior than for lists: for lists, `∈` uses `=` and `contains` uses
`==` for comparisons, while for hash maps, both use `==`.
-/
@[inline] def contains (m : HashMap α β)
    (a : α) : Bool :=
  m.inner.contains a

instance [BEq α] [Hashable α] : Membership α (HashMap α β) where
  mem m a := m.inner.contains a = true

instance [BEq α] [Hashable α] {m : HashMap α β} {a : α} : Decidable (a ∈ m) :=
  inferInstanceAs (Decidable (m.inner.contains a = true))

/--
The notation `m[a]` or `m[a]'h` is preferred over calling this function directly.

Retrieves the mapping for the given key. Ensures that such a mapping exists by requiring a proof of
`a ∈ m`.
-/
@[inline] def get (m : HashMap α β) (a : α) (h : a ∈ m) : β :=
  m.inner.get a h

/--
Tries to retrieve the mapping for the given key, returning `fallback` if no such mapping is present.
-/
@[inline] def getD (m : HashMap α β) (a : α)
    (fallback : β) : β :=
  m.inner.getD a fallback

/--
The notation `m[a]!` is preferred over calling this function directly.

Tries to retrieve the mapping for the given key, panicking if no such mapping is present.
-/
@[inline] def get! [Inhabited β] (m : HashMap α β) (a : α) : β :=
  m.inner.get! a

instance [BEq α] [Hashable α] : GetElem? (HashMap α β) α β (fun m a => a ∈ m) where
  getElem m a h := m.get a h
  getElem? m a := m.get? a
  getElem! m a := m.get! a

/--
Checks if a mapping for the given key exists and returns the key if it does, otherwise `none`.
The result in the `some` case is guaranteed to be pointer equal to the key in the map.
-/
@[inline] def getKey? (m : HashMap α β) (a : α) : Option α :=
  m.inner.getKey? a

/--
Retrieves the key from the mapping that matches `a`. Ensures that such a mapping exists by
requiring a proof of `a ∈ m`. The result is guaranteed to be pointer equal to the key in the map.
-/
@[inline] def getKey (m : HashMap α β) (a : α) (h : a ∈ m) : α :=
  m.inner.getKey a h

/--
Checks if a mapping for the given key exists and returns the key if it does, otherwise `fallback`.
If a mapping exists the result is guaranteed to be pointer equal to the key in the map.
-/
@[inline] def getKeyD (m : HashMap α β) (a : α) (fallback : α) : α :=
  m.inner.getKeyD a fallback

/--
Checks if a mapping for the given key exists and returns the key if it does, otherwise panics.
If no panic occurs the result is guaranteed to be pointer equal to the key in the map.
-/
@[inline] def getKey! [Inhabited α] (m : HashMap α β) (a : α) : α :=
  m.inner.getKey! a

/--
Removes the mapping for the given key if it exists. 
-/
@[cbv_opaque, inline] def erase (m : HashMap α β) (a : α) :
    HashMap α β :=
  ⟨m.inner.erase a⟩

/--
The number of mappings present in the hash map 
-/
@[inline] def size (m : HashMap α β) : Nat :=
  m.inner.size

/--
Returns `true` if the hash map contains no mappings.

Note that if your `BEq` instance is not reflexive or your `Hashable` instance is not
lawful, then it is possible that this function returns `false` even though is not possible
to get anything out of the hash map.
-/
@[inline] def isEmpty (m : HashMap α β) : Bool :=
  m.inner.isEmpty

/--
Returns a list of all keys present in the hash map in some order. 
-/
@[inline] def keys (m : HashMap α β) : List α :=
  m.inner.keys

/--
Creates a hash map from a list of mappings. If the same key appears multiple times, the last
occurrence takes precedence. 
-/
@[inline] def ofList [BEq α] [Hashable α] (l : List (α × β)) :
    HashMap α β :=
  ⟨Core.Table.ofList l⟩

/--
Creates a hash map from a list of keys, associating the value `()` with each key.

This is mainly useful to implement `HashSet.ofList`, so if you are considering using this,
`HashSet` or `HashSet.Raw` might be a better fit for you. 
-/
@[inline] def unitOfList [BEq α] [Hashable α] (l : List α) :
    HashMap α Unit :=
  ⟨Core.Table.unitOfList l⟩

/--
Creates a hash map from an array of mappings. If the same key appears multiple times, the last
occurrence takes precedence. 
-/
@[inline] def ofArray [BEq α] [Hashable α] (a : Array (α × β)) :
    HashMap α β :=
  ⟨Core.Table.ofArray a⟩

/--
Transforms the hash map into a list of mappings in some order. 
-/
@[inline] def toList (m : HashMap α β) :
    List (α × β) :=
  m.inner.toList

/--
Monadically computes a value by folding the given function over the mappings in the hash
map in some order.
-/
@[inline] def foldM {m : Type w → Type w'}
    [Monad m] {γ : Type w} (f : γ → α → β → m γ) (init : γ) (b : HashMap α β) : m γ :=
  b.inner.foldM f init

/--
Folds the given function over the mappings in the hash map in some order. 
-/
@[inline] def fold {γ : Type w}
    (f : γ → α → β → γ) (init : γ) (b : HashMap α β) : γ :=
  b.inner.fold f init

/--
Carries out a monadic action on each mapping in the hash map in some order. 
-/
@[inline] def forM {m : Type w → Type w'} [Monad m]
    (f : (a : α) → β → m PUnit) (b : HashMap α β) : m PUnit :=
  b.inner.forM f

/--
Support for the `for` loop construct in `do` blocks. 
-/
@[inline] def forIn {m : Type w → Type w'} [Monad m]
    {γ : Type w} (f : (a : α) → β → γ → m (ForInStep γ)) (init : γ) (b : HashMap α β) : m γ :=
  b.inner.forIn f init

instance [BEq α] [Hashable α] {m : Type w → Type w'} [Monad m] : ForM m (HashMap α β) (α × β) where
  forM m f := m.forM (fun a b => f (a, b))

instance [BEq α] [Hashable α] {m : Type w → Type w'} [Monad m] : ForIn m (HashMap α β) (α × β) where
  forIn m init f := m.forIn (fun a b acc => f (a, b) acc) init

/--
Removes all mappings of the hash map for which the given function returns `false`. 
-/
@[cbv_opaque, inline] def filter (f : α → β → Bool)
    (m : HashMap α β) : HashMap α β :=
  ⟨m.inner.filter f⟩

/--
Modifies in place the value associated with a given key.

This function ensures that the value is used linearly.
-/
@[inline] def modify (m : HashMap α β) (a : α) (f : β → β) :
    HashMap α β :=
  ⟨m.inner.modify a f⟩

/--
Modifies in place the value associated with a given key,
allowing creating new values and deleting values via an `Option` valued replacement function.

This function ensures that the value is used linearly.
-/
@[inline] def alter (m : HashMap α β) (a : α)
    (f : Option β → Option β) : HashMap α β :=
  ⟨m.inner.alter a f⟩

/--
Inserts multiple mappings into the hash map by iterating over the given collection and calling
`insert`. If the same key appears multiple times, the last occurrence takes precedence.

Note: this precedence behavior is true for `HashMap`, `DHashMap`, `HashMap.Raw` and `DHashMap.Raw`.
The `insertMany` function on `HashSet` and `HashSet.Raw` behaves differently: it will prefer the first
appearance.
-/
@[inline] def insertMany {ρ : Type w}
    [ForIn Id ρ (α × β)] (m : HashMap α β) (l : ρ) : HashMap α β :=
  ⟨(m.inner.insertMany l).1⟩

/--
Inserts multiple keys with the value `()` into the hash map by iterating over the given collection
and calling `insertIfNew`. If the same key appears multiple times, the first occurrence takes
precedence.

This is mainly useful to implement `HashSet.insertMany`, so if you are considering using this,
`HashSet` or `HashSet.Raw` might be a better fit for you.
-/
@[inline] def insertManyIfNewUnit
    {ρ : Type w} [ForIn Id ρ α] (m : HashMap α Unit) (l : ρ) : HashMap α Unit :=
  ⟨(m.inner.insertManyIfNewUnit l).1⟩

/--
Transforms the hash map into an array of mappings in some order. 
-/
@[inline] def toArray (m : HashMap α β) :
    Array (α × β) :=
  m.inner.toArray

/--
Returns an array of all keys present in the hash map in some order. 
-/
@[inline] def keysArray (m : HashMap α β) :
    Array α :=
  m.inner.keysArray

/--
Checks if all elements satisfy the predicate, short-circuiting if a predicate fails. 
-/
@[inline] def all (m : HashMap α β) (p : α → β → Bool) : Bool :=
  m.inner.all p

/--
Checks if any element satisfies the predicate, short-circuiting if a predicate succeeds. 
-/
@[inline] def any (m : HashMap α β) (p : α → β → Bool) : Bool :=
  m.inner.any p
/--
Computes the union of the given hash maps. If a key appears in both maps, the entry contained in
the second argument will appear in the result.

This function always merges the smaller map into the larger map, so the expected runtime is
`O(min(m₁.size, m₂.size))`.
-/
@[inline] def union [BEq α] [Hashable α] (m₁ m₂ : HashMap α β) : HashMap α β :=
  ⟨m₁.inner.union m₂.inner⟩

instance [BEq α] [Hashable α] : Union (HashMap α β) := ⟨union⟩

/--
Computes the intersection of the given hash maps. The result will only contain entries from the first map.

This function always iterates through the smaller map, so the expected runtime is
`O(min(m₁.size, m₂.size))`.
-/
@[inline] def inter [BEq α] [Hashable α] (m₁ m₂ : HashMap α β) : HashMap α β :=
  ⟨m₁.inner.inter m₂.inner⟩

instance [BEq α] [Hashable α] : Inter (HashMap α β) := ⟨inter⟩

/--
Compares two hash maps using Boolean equality on keys and values.

Returns `true` if the maps contain the same key-value pairs, `false` otherwise.
-/
def beq {β : Type v} [BEq α] [BEq β] (m₁ m₂ : HashMap α β) : Bool :=
  m₁.inner.beq m₂.inner

instance [BEq α] [BEq β] : BEq (HashMap α β) := ⟨beq⟩

/--
Computes the difference of the given hash maps.

This function always iterates through the smaller map, so the expected runtime is
`O(min(m₁.size, m₂.size))`.
-/
@[inline] def diff [BEq α] [Hashable α] (m₁ m₂ : HashMap α β) : HashMap α β :=
  ⟨m₁.inner.diff m₂.inner⟩

instance [BEq α] [Hashable α] : SDiff (HashMap α β) := ⟨diff⟩

section Unverified

/-! We currently do not provide lemmas for the functions below. -/

/--
Partition a hash map into two hash map based on a predicate. 
-/
@[inline] def partition (f : α → β → Bool)
    (m : HashMap α β) : HashMap α β × HashMap α β :=
  let ⟨l, r⟩ := m.inner.partition f
  ⟨⟨l⟩, ⟨r⟩⟩

/--
Returns a list of all values present in the hash map in some order. 
-/
@[inline] def values (m : HashMap α β) : List β :=
  m.inner.values

/--
Returns an array of all values present in the hash map in some order. 
-/
@[inline] def valuesArray (m : HashMap α β) :
    Array β :=
  m.inner.valuesArray

/--
Creates a hash map from an array of keys, associating the value `()` with each key.

This is mainly useful to implement `HashSet.ofArray`, so if you are considering using this,
`HashSet` or `HashSet.Raw` might be a better fit for you. 
-/
@[inline] def unitOfArray [BEq α] [Hashable α] (l : Array α) :
    HashMap α Unit :=
  ⟨Core.Table.unitOfArray l⟩

/--
Returns the number of buckets in the internal representation of the hash map. This function may be
useful for things like monitoring system health, but it should be considered an internal
implementation detail.
-/
@[inline] def Internal.numBuckets
    (m : HashMap α β) : Nat :=
  m.inner.numBuckets

instance [BEq α] [Hashable α] [Repr α] [Repr β] : Repr (HashMap α β) where
  reprPrec m prec := Repr.addAppParen ("SwissTable.HashMap.ofList " ++ reprArg m.toList) prec

end Unverified

end SwissTable.HashMap
