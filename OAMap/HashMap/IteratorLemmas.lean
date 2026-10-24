/-
Copyright (c) 2025 Lean FRO, LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Paul Reichert
-/
module

public import OAMap.HashMap.Iterator
public import OAMap.HashMap.Lemmas
public import Std.Data.Iterators.Lemmas.Producers.Array
import Init.Data.Iterators.Lemmas.Consumers.Collect

/-!
# Iterator lemmas for `HashMap`

The nine `toList`/`toListRev`/`toArray` lemmas of `iter`, `keysIter` and `valuesIter`, with the
statements, binders and attributes of Std's `Std/Data/HashMap/IteratorLemmas.lean`
(`docs/ARCHITECTURE.md` §8; `tools/srccheck.py` checks their source text).

The iterators are array iterators (`OAMap.HashMap.Iterator`), so each `toList` lemma is
`Array.toList_iter` followed by the model form of `toArray`, `keysArray` or `valuesArray`
(`OAMap.Model`); the `toListRev` and `toArray` lemmas are Std's proofs from those, or
`Array.toArray_iter`. None needs `EquivBEq` or `LawfulHashable`, although `toList_keysIter` and its
siblings take them, as Std's do.

Owner: ITER, Wave 3.
-/

universe u v

namespace OAMap.HashMap

section EntriesIter

variable {α : Type u} {β : Type v} [BEq α] [Hashable α] {m : HashMap α β}

@[simp]
public theorem toList_iter :
    m.iter.toList = m.toList := by
  rw [iter, Array.toList_iter, Model.toArray_eq_toArray_map_toListModel, List.toList_toArray,
    Model.toList_eq_toListModel_map]

@[simp]
public theorem toListRev_iter :
    m.iter.toListRev = m.toList.reverse := by
  simp [Std.Iter.toListRev_eq, toList_iter]

@[simp]
public theorem toArray_iter :
    m.iter.toArray = m.toArray := by
  rw [iter, Array.toArray_iter]

end EntriesIter

section KeysIter

variable {α : Type u} {β : Type u} [BEq α] [Hashable α] {m : HashMap α β}

@[simp]
public theorem toList_keysIter [EquivBEq α] [LawfulHashable α] :
    m.keysIter.toList = m.keys := by
  rw [keysIter, Array.toList_iter, Model.keysArray_eq_toArray_keys_toListModel,
    List.toList_toArray, Model.keys_eq_keys_toListModel]

@[simp]
public theorem toListRev_keysIter [EquivBEq α] [LawfulHashable α] :
    m.keysIter.toListRev = m.keys.reverse := by
  simp [Std.Iter.toListRev_eq, toList_keysIter]

@[simp]
public theorem toArray_keysIter [EquivBEq α] [LawfulHashable α] :
    m.keysIter.toArray = m.keysArray := by
  rw [keysIter, Array.toArray_iter]

end KeysIter

section ValuesIter

variable {α : Type u} {β : Type u} [BEq α] [Hashable α] {m : HashMap α β}

@[simp]
public theorem toList_valuesIter_eq_toList_map_snd :
    m.valuesIter.toList = m.toList.map Prod.snd := by
  rw [valuesIter, Array.toList_iter, Model.valuesArray_eq_toArray_values_toListModel,
    List.toList_toArray, Model.toList_eq_toListModel_map, List.map_map,
    Std.Internal.List.values_eq_map]
  rfl

@[simp]
public theorem toListRev_valuesIter :
    m.valuesIter.toListRev = (m.toList.map Prod.snd).reverse := by
  simp [Std.Iter.toListRev_eq, toList_valuesIter_eq_toList_map_snd]

@[simp]
public theorem toArray_valuesIter :
    m.valuesIter.toArray = (m.toList.map Prod.snd).toArray := by
  simp [← Std.Iter.toArray_toList, toList_valuesIter_eq_toList_map_snd]

end ValuesIter

end OAMap.HashMap
