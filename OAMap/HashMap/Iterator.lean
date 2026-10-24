/-
Copyright (c) 2025 Lean FRO, LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Paul Reichert
-/
module

public import OAMap.HashMap.Basic
public import Std.Data.Iterators.Producers.Array

@[expose] public section

/-!
# Iterators on `HashMap`

`iter`, `keysIter` and `valuesIter`, with the declarations of Std's
`Std/Data/HashMap/Iterator.lean` (`docs/ARCHITECTURE.md` §8).

Implementation notes. Std's iterators walk its bucket array lazily, and their elaborated types
mention its `AssocList` buckets. These are array iterators over `toArray`, `keysArray` and
`valuesArray`, so they enumerate the same sequence as `toList`, `keys` and `values`, are `Finite`
and `Productive` through the instances of `Std.Iterators.Types.ArrayIterator`, and cost one array
of the map's size when created. The source text of the declarations (name, binders, attributes)
is Std's, including the single universe of `keysIter` and `valuesIter`; `tools/srccheck.py`
checks it, because the parity checker cannot compare the elaborated state types. Std's
`inherit_doc Raw.iter` is replaced by its literal text, as there is no `Raw`, so all three
docstrings are `Raw.iter`'s, as on Std.

The section is `@[expose]`d so that `OAMap.HashMap.IteratorLemmas` can unfold the definitions
without `import all`.

Owner: ITER, Wave 3.
-/

universe u v

namespace OAMap.HashMap

/--
Returns a finite iterator over the entries of a hash map.
The iterator yields the elements of the map in order and then terminates.

**Termination properties:**

* `Finite` instance: always
* `Productive` instance: always
-/
@[inline]
public def iter {α : Type u} {β : Type v} [BEq α] [Hashable α] (m : HashMap α β) :=
  (m.toArray.iter : Std.Iter (α × β))

/--
Returns a finite iterator over the entries of a hash map.
The iterator yields the elements of the map in order and then terminates.

**Termination properties:**

* `Finite` instance: always
* `Productive` instance: always
-/
@[inline]
public def keysIter {α : Type u} {β : Type u} [BEq α] [Hashable α] (m : HashMap α β) :=
  (m.keysArray.iter : Std.Iter α)

/--
Returns a finite iterator over the entries of a hash map.
The iterator yields the elements of the map in order and then terminates.

**Termination properties:**

* `Finite` instance: always
* `Productive` instance: always
-/
@[inline]
public def valuesIter {α : Type u} {β : Type u} [BEq α] [Hashable α] (m : HashMap α β) :=
  (m.valuesArray.iter : Std.Iter β)

end OAMap.HashMap
