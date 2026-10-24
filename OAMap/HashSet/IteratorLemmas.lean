/-
Copyright (c) 2025 Lean FRO, LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Paul Reichert
-/
module

public import OAMap.HashSet.Iterator
public import OAMap.HashSet.Lemmas
public import OAMap.HashMap.IteratorLemmas
import Init.Data.Iterators.Lemmas.Combinators.FilterMap
import Init.Data.Iterators.Lemmas.Consumers.Collect

/-!
# Iterator lemmas for `HashSet`

The three `toList`/`toListRev`/`toArray` lemmas of `HashSet.iter`, with the statements, binders
and attributes of Std's `Std/Data/HashSet/IteratorLemmas.lean` (`docs/ARCHITECTURE.md` §8;
`tools/srccheck.py` checks their source text).

`m.iter` maps `Prod.fst` over the entry iterator of `m.inner`, so `toList_iter` is
`Iter.toList_map` and `HashMap.toList_iter`, followed by the model form of `keys`
(`OAMap.Model`); the other two follow from it as in Std.

Owner: ITER, Wave 3.
-/

universe u

namespace OAMap.HashSet

variable {α : Type u} [BEq α] [Hashable α] {m : HashSet α}

@[simp]
public theorem toList_iter [EquivBEq α] [LawfulHashable α] :
    m.iter.toList = m.toList := by
  rw [iter, Std.Iter.toList_map, HashMap.toList_iter, toList, Model.toList_eq_toListModel_map,
    Model.keys_eq_keys_toListModel, Std.Internal.List.keys_eq_map, List.map_map]
  rfl

@[simp]
public theorem toListRev_iter [EquivBEq α] [LawfulHashable α] :
    m.iter.toListRev = m.toList.reverse := by
  simp [Std.Iter.toListRev_eq, toList_iter]

@[simp]
public theorem toArray_iter [EquivBEq α] [LawfulHashable α] :
    m.iter.toArray = m.toArray := by
  simp [← Std.Iter.toArray_toList, toList_iter]

end OAMap.HashSet
