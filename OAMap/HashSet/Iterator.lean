/-
Copyright (c) 2025 Lean FRO, LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Paul Reichert
-/
module

public import OAMap.HashSet.Basic
public import OAMap.HashMap.Iterator
public import Init.Data.Iterators.Combinators.FilterMap

@[expose] public section

/-!
# Iterators on `HashSet`

`HashSet.iter`, with the declaration of Std's `Std/Data/HashSet/Iterator.lean`
(`docs/ARCHITECTURE.md` §8): as on Std, the iterator of the underlying map with the first
component of each entry. Its source text is Std's (`tools/srccheck.py`), except that the map is
`m.inner` (an `OAMap.HashMap α Unit`) where Std's is `m.inner.inner` (a `DHashMap`), and Std's
`inherit_doc Raw.iter` is replaced by its literal text.

The section is `@[expose]`d so that `OAMap.HashSet.IteratorLemmas` can unfold the definition
without `import all`.

Owner: ITER, Wave 3.
-/

universe u

namespace OAMap.HashSet

/--
Returns a finite iterator over the elements of a hash set.
The iterator yields the elements of the set in order and then terminates.

**Termination properties:**

* `Finite` instance: always
* `Productive` instance: always
-/
@[inline]
public def iter {α : Type u} [BEq α] [Hashable α] (m : HashSet α) :=
  (m.inner.iter.map fun e => e.1 : Std.Iter α)

end OAMap.HashSet
