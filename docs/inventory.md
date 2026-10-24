# Std.HashMap / Std.HashSet inventory (Lean v4.35.0)

Generated from the live environment by `dump.lean`, a Lean meta-program run after `import Lean` and `import Std`. It walks every constant whose name starts with `Std.HashMap.` or `Std.HashSet.`, excluding `*.Raw.*` and compiler or elaborator auxiliaries, and prints signatures, simp status, deprecation, inline and reducibility as JSON. `build_inventory.py` then cross-references the Std sources for attributes, source statements, sections and topics, and `write_md.py` adds notes and renders this file. The machine-readable version is `inventory.json` (key `decls`; each entry has `sig` (ppSignature), `sig_proofs`, `type_fullnames`, `src_statement`, `attrs`, `env_attrs`, `scope`, `topic`, `subheading`, `consts`, `consts_external` and `doc`).

Statements below are the elaborated signatures (Lean's `ppSignature`) with the name and universe list dropped. The common implicit prefix `{α : Type u} {β : Type v} {x✝ : BEq α} {x✝¹ : Hashable α}` (HashMap) or `{α : Type u} {x✝ : BEq α} {x✝¹ : Hashable α}` (HashSet) is shortened to `…`. Any other binder order is printed in full. `x✝` binders are Std's anonymous `{_ : BEq α}` implicits. `⋯` hides a proof; the JSON has `sig_proofs` and the source form in `src_statement`.

## Counts

| family | category | count |
|---|---|---|
| Std.HashMap | auto_generated | 2 |
| Std.HashMap | definition | 51 |
| Std.HashMap | instance | 19 |
| Std.HashMap | notation | 1 |
| Std.HashMap | structure_generated | 11 |
| Std.HashMap | theorem | 688 |
| Std.HashMap | type | 2 |
| Std.HashSet | auto_generated | 1 |
| Std.HashSet | definition | 30 |
| Std.HashSet | instance | 16 |
| Std.HashSet | notation | 1 |
| Std.HashSet | structure_generated | 11 |
| Std.HashSet | theorem | 323 |
| Std.HashSet | type | 2 |

Excluded: Raw (Std.HashMap.Raw.*): 789, Raw (Std.HashSet.Raw.*): 394, aux (_simp_N, match_N, _proof_N, eq_N, casesOn/recOn/noConfusion, _sizeOf, macro/unexpander): 89, Raw aux: 82.

### Theorems per section/topic

| file | group (topic / section) | theorems | instances |
|---|---|---|---|
| HashMap.Basic | (top level) | 1 | 0 |
| HashMap.Lemmas | isEmpty / contains / mem basics (empty, congr, isEmpty characterisations) | 18 | 0 |
| HashMap.Lemmas | insert: notation, contains, mem | 8 | 0 |
| HashMap.Lemmas | size; toList/keys/values of empty; size of insert | 12 | 0 |
| HashMap.Lemmas | erase: isEmpty, contains, mem, size | 10 | 0 |
| HashMap.Lemmas | containsThenInsert / containsThenInsertIfNew | 4 | 0 |
| HashMap.Lemmas | get/get?/get! vs m[k] notation; getElem? (m[k]?) | 21 | 0 |
| HashMap.Lemmas | getElem (m[k]'h) [also toList_insert_perm, keys_insertIfNew_perm] | 9 | 0 |
| HashMap.Lemmas | getElem! (m[k]!) | 17 | 0 |
| HashMap.Lemmas | getD | 15 | 0 |
| HashMap.Lemmas | getKey? | 19 | 0 |
| HashMap.Lemmas | getKey | 9 | 0 |
| HashMap.Lemmas | getKey! | 16 | 0 |
| HashMap.Lemmas | getKeyD | 17 | 0 |
| HashMap.Lemmas | insertIfNew | 20 | 0 |
| HashMap.Lemmas | getThenInsertIfNew? | 2 | 0 |
| HashMap.Lemmas | LawfulGetElem instance | 0 | 1 |
| HashMap.Lemmas | keys / keysArray | 15 | 0 |
| HashMap.Lemmas | toList / toArray | 20 | 0 |
| HashMap.Lemmas | monadic: fold / foldM / forM / forIn | 19 | 1 |
| HashMap.Lemmas | all / any | 14 | 0 |
| HashMap.Lemmas | insertMany | 32 | 0 |
| HashMap.Lemmas | BEq vs Equiv | 4 | 0 |
| HashMap.Lemmas | Union | 41 | 0 |
| HashMap.Lemmas | Inter | 43 | 0 |
| HashMap.Lemmas | Diff | 39 | 0 |
| HashMap.Lemmas | insertManyIfNewUnit (HashMap α Unit) | 29 | 0 |
| HashMap.Lemmas | ofList / ofArray | 24 | 0 |
| HashMap.Lemmas | unitOfList / unitOfArray (HashMap α Unit) | 21 | 0 |
| HashMap.Lemmas | alter | 32 | 0 |
| HashMap.Lemmas | modify | 20 | 0 |
| HashMap.Lemmas | namespace Equiv (Equiv.* lemmas) | 38 | 1 |
| HashMap.Lemmas | Equiv characterisations (section Equiv) | 11 | 0 |
| HashMap.Lemmas | filterMap | 24 | 0 |
| HashMap.Lemmas | filter | 29 | 0 |
| HashMap.Lemmas | map | 26 | 0 |
| HashMap.IteratorLemmas | section EntriesIter | 3 | 0 |
| HashMap.IteratorLemmas | section KeysIter | 3 | 0 |
| HashMap.IteratorLemmas | section ValuesIter | 3 | 0 |
| HashSet.Lemmas | isEmpty / contains / mem basics (empty, congr, isEmpty characterisations) | 18 | 0 |
| HashSet.Lemmas | insert: notation, contains, mem | 11 | 0 |
| HashSet.Lemmas | size; toList of empty; size of insert | 8 | 0 |
| HashSet.Lemmas | erase: isEmpty, contains, mem, size | 10 | 0 |
| HashSet.Lemmas | get? | 18 | 0 |
| HashSet.Lemmas | get [also toList_insert_perm] | 9 | 0 |
| HashSet.Lemmas | get! | 15 | 0 |
| HashSet.Lemmas | getD | 16 | 0 |
| HashSet.Lemmas | containsThenInsert | 2 | 0 |
| HashSet.Lemmas | toList / toArray | 14 | 0 |
| HashSet.Lemmas | monadic: fold / foldM / forM / forIn | 11 | 1 |
| HashSet.Lemmas | all / any | 12 | 0 |
| HashSet.Lemmas | insertMany | 26 | 0 |
| HashSet.Lemmas | BEq vs Equiv | 4 | 0 |
| HashSet.Lemmas | Union | 27 | 0 |
| HashSet.Lemmas | Inter | 30 | 0 |
| HashSet.Lemmas | Diff | 26 | 0 |
| HashSet.Lemmas | ofList / ofArray | 17 | 0 |
| HashSet.Lemmas | namespace Equiv (Equiv.* lemmas) | 24 | 1 |
| HashSet.Lemmas | Equiv characterisations (section Equiv) | 9 | 0 |
| HashSet.Lemmas | filter | 13 | 0 |
| HashSet.IteratorLemmas | (top level) | 3 | 0 |

## Drop-in notes (surprises)

- **iter-state-type**: HashMap.iter/keysIter/valuesIter and HashSet.iter have no written return type; the elaborated type is `@Std.Iter σ (α × β)` where the implicit state σ is `Std.Iterators.Types.Map (Flatten (Map (ArrayIterator (Std.DHashMap.Internal.AssocList α _)) …))` built over `Std.DHashMap.Internal.AssocList.AssocListIterator`. So the elaborated statements of the 12 iterator lemmas (toList_iter, toListRev_iter, toArray_iter, *_keysIter, *_valuesIter, HashSet.*_iter) mention DHashMap bucket internals and the Iterator instances on them. A drop-in can reproduce the source statements (`m.iter.toList = m.toList`), which re-elaborate against its own state type. It cannot reproduce the elaborated terms, so user code that writes the state type out breaks. The consumers only need `[Iterator σ Id β]` for toList/toListRev/toArray. `for x in m.iter` and `Iter.toHashSet` also need IteratorLoop, and the docs promise Finite and Productive. No HashMap-specific iterator instances exist. Std gets Iterator/Finite/IteratorLoop from the generic Std.Iterators.Types.{Map, Flatten, ArrayIterator} instances plus three on Std.DHashMap.Internal.AssocList.AssocListIterator: instIteratorAssocListIteratorIdSigma, instFiniteAssocListIteratorIdSigma and instIteratorLoopAssocListIteratorIdSigmaOfMonad.
- **iter-universe**: keysIter and valuesIter force `{α β : Type u}` (same universe); iter does not.
- **inner-field**: The public structure field `HashMap.inner : DHashMap α (fun _ => β)` (with its constructor `HashMap.mk`, `rec`, `mk.inj`, `mk.injEq` and `mk.sizeOf_spec`) and `Equiv.inner : m₁.inner.Equiv m₂.inner` (so `Equiv.mk` too) name DHashMap and DHashMap.Equiv. HashSet.inner is `HashMap α Unit`, and HashSet.Equiv.inner is `m₁.inner.Equiv m₂.inner`, which is HashMap.Equiv. A drop-in cannot reproduce the HashMap ones. Only code that uses `m.inner`, `m.1`, `⟨d⟩` or `⟨h⟩ : Equiv` breaks, and no lemma statement in Lemmas.lean mentions `inner`.
- **no-dhashmap-in-lemmas**: None of the 678 HashMap/Lemmas.lean or 320 HashSet/Lemmas.lean theorem statements mentions Std.DHashMap, Raw, Std.Internal.List or any other internal. Their non-HashMap vocabulary is core only: List (Perm, Pairwise, Nodup, findSomeRev?, attach/unattach, filter, map, foldl/foldlM, contains, …), Array, Option (pfilter, pbind, pmap, get, …), BEq/EquivBEq/LawfulHashable/LawfulBEq/ReflBEq, GetElem?/Membership/Union/Inter/SDiff/Singleton/Insert/EmptyCollection, ForIn/ForM, and `ForIn.toList` (Init.Control.Id). The only Std.Internal mention is the class `Std.Internal.PureForIn` in two instances.
- **pure-forin**: The Lemmas files register `instance : Std.Internal.PureForIn m' (HashMap α β) (α × β)` and `… (HashSet α) α` (needing [Monad m'] [LawfulMonad m']). They rest on `forIn_toList : ForIn.toList c = c.toList`. PureForIn is consumed by Std.WP (the mvcgen spec lemmas for `for` loops), so a drop-in has to provide the same instance or mvcgen loses its loop specs over the map.
- **lawful-getelem**: `LawfulGetElem (HashMap α β) α β (fun m a => a ∈ m)` lives in Lemmas.lean and requires [EquivBEq α] [LawfulHashable α]. HashSet has no GetElem instance.
- **binder-style**: Std uses `variable {_ : BEq α} {_ : Hashable α}`, so most operations and nearly all lemmas take BEq/Hashable as anonymous implicit binders (`{x✝ : BEq α}`), not instance-implicit ones. Some definitions instead take `[BEq α] [Hashable α]`: emptyWithCapacity, ofList, ofArray, unitOfList, unitOfArray, union, inter, diff, filterMap, map, iter*, HashSet.get/getD/get!. `beq` takes `{x✝ : Hashable α} … [BEq α] [BEq β]`. Binder order also varies between sections: in Union, Inter and Diff, β comes after the BEq/Hashable binders. `sig` records the exact order and kinds for `@`-explicit and named-argument use.
- **cbv**: Lean 4.35's `cbv` evaluator is wired in. 10 definitions are `@[cbv_opaque]` (HashMap emptyWithCapacity/insert/erase/filter/filterMap/map and HashSet emptyWithCapacity/insert/erase/filter), and 58 lemmas are `@[cbv_eval]` rewrite rules (contains/get?/getElem?/getElem!/getD of emptyWithCapacity/insert/erase, insertMany_nil/cons, ofList_eq_insertMany_empty, ofArray_eq_ofList, the primed filter/filterMap lemmas, the map lemmas, getKey*_filter_key). A drop-in should carry the same attributes for `cbv` and `decide +cbv` behaviour to match.
- **late-simp**: `contains_eq_false_iff_not_mem` gets `simp` only through `attribute [simp] …` on the last line of each Lemmas file. grind_pattern commands supply e-matching patterns for size_le_size_insertMany, size_insertMany_list_le, size_ofList_le, size_filterMap_le_size and size_filter_le_size (HashMap), and for size_le_size_insertMany, size_insertMany_list_le, size_ofList_le and size_filter_le_size (HashSet).
- **deprecated**: One deprecated alias must exist for drop-in: `HashMap.union_insert_right_equiv_union_insert` → `union_insert_right_equiv_insert_union` (since 2025-11-03).
- **aux-in-statements**: Four statements elaborate to terms that contain their own auxiliary constants: getKey_insert (`_proof_1` from `by simpa`), getElem?_insertMany_list (`match_1`), getElem_filterMap' (`_proof_1`) and keys_filter (`match_1`). These are regenerated automatically when the same source text is elaborated. They are recorded so a JSON-driven statement generator does not try to name them.
- **unverified**: Some definitions sit in an `Unverified` section with no or almost no lemmas. HashMap: partition (0), values (2, both about empty), valuesArray (0), unitOfArray (1: unitOfArray_eq_unitOfList), ofArray (1: ofArray_eq_ofList), Internal.numBuckets (0), Repr (0) and beq (only through instBEq, 4). HashSet: partition (0), ofArray (1), Internal.numBuckets (0), Repr (0) and beq (through instBEq, 4). `Internal.numBuckets` is a public def whose value depends on the representation.
- **structural-equalities**: 45 lemmas (28 HashMap, 17 HashSet) are propositional equalities between maps or sets themselves, not `~m`. They constrain the implementation beyond the entry-list model. (a) ofList_nil : ofList [] = ∅ (that is, emptyWithCapacity 8), ofList_singleton, ofList_cons, ofList_eq_insertMany_empty, ofArray_eq_ofList, unitOfList_* , unitOfArray_eq_unitOfList, insertMany_nil/_cons/_append/_list_singleton and insertManyIfNewUnit_nil/_cons/_list_singleton force insertMany/ofList/ofArray/unitOfList (on lists) to be literally a left fold of insert/insertIfNew starting from the given map or from ∅. Pre-reserving capacity or bulk-building would break them unless the table layout is history-independent. (b) erase_empty and erase_emptyWithCapacity: erasing from an empty map returns the identical structure. (c) containsThenInsert_snd, containsThenInsertIfNew_snd and getThenInsertIfNew?_snd: the fused operations return exactly the structure insert/insertIfNew would. (d) insert_eq_insert, singleton_eq_insert, union_eq, inter_eq, diff_eq and markLinear_eq hold by definition. The JSON lists them via `eq_type_head` ∈ {Std.HashMap, Std.HashSet}.
- **order-coherence**: toList order is unspecified (insert only up to List.Perm: toList_insert_perm), but every traversal must agree with it exactly. The equalities that require this: map_fst_toList_eq_keys, toArray_toList and toList_toArray, toArray_keys and toList_keysArray, map_fst_toArray_eq_keysArray, fold_eq_foldl_toList and foldM_eq_foldlM_toList (plus the _keys, _toArray and _keysArray variants), forM_eq_forM_toList, forIn_eq_forIn_toList, any_toList and all_toList, toList_iter, toList_keysIter and toList_valuesIter_eq_toList_map_snd. values is unconstrained apart from emptiness.
- **hashset-ofList-doc**: The HashSet.ofList docstring says "the last element in the collection will be present", but the lemmas pin down first-occurrence-wins: ofList_eq_insertMany_empty, insertMany_cons with HashSet.insert = insertIfNew, and HashMap.unitOfList_eq_insertManyIfNewUnit_empty. The get?_ofList lemmas avoid the issue with distinctness hypotheses. A drop-in has to follow the lemmas, which are equalities.
- **semantics**: These semantics show up in the statements. HashMap.insert replaces both the stored key and the value (getKey_insert returns the new k). insertIfNew keeps the old entry. HashSet.insert is `insertIfNew a ()`, so it keeps the old key. HashMap.insertMany and ofList: the last occurrence wins (getElem?_insertMany_list uses findSomeRev?). HashSet.insertMany: the first occurrence wins. HashSet.ofList = HashMap.unitOfList: per its docstring the last element is kept, yet the unitOfList lemmas are stated as `getKey?_unitOfList_of_mem` with `List.Pairwise`/distinctness hypotheses. union is right-biased (the entry from m₂ wins), and inter keeps the entries of m₁. Equiv is extensional equality on the entry model and is what all union/inter/diff and Equiv.* lemmas use. Decidable (m₁ ~m m₂) needs LawfulBEq α and LawfulBEq β.
- **repr-name**: The Repr instances print `Std.HashMap.ofList [...]` / `Std.HashSet.ofList [...]` as a literal string, and the docstrings of Array.groupByKey and List.groupByKey show that output. A drop-in's #eval output will differ unless it prints the same prefix.
- **external-api**: Some Std API outside the two namespaces returns or consumes Std.HashMap/HashSet: `Array.groupByKey` and `List.groupByKey` (Std.Data.HashMap.Basic, returning Std.HashMap α (Array β) or (List β)), `Std.Iter.toHashSet`, `Std.Iter.Total.toHashSet`, `Std.IterM.toHashSet`, `Std.IterM.Total.toHashSet` and the theorem `Std.IterM.toHashSet_eq_fold` (Std.Data.Iterators.Consumers.{Set,Monadic.Set} and Lemmas). Users who switch would need OAMap counterparts of these. The rest of Std that mentions HashMap (Std.Sat.AIG, BVDecide LRAT, Http, Async) is internal use, not API. No instance in Lean or Std outside the two namespaces mentions HashMap or HashSet (checked over all 207,958 constants of `import Lean, Std`).
- **module-system**: Basic.lean and Lemmas.lean are `@[expose] public section`, so importers can unfold definition bodies (rfl/decide proofs through e.g. `instGetElem?Mem`, `insert_eq_insert` and `LawfulSingleton` are proved by rfl). The non-exported module-local theorems toList_inner and keys_inner (IteratorLemmas) and the private `ext` (Lemmas) are not visible and so not part of the API.
- **congr-simp**: `get.congr_simp` and `getKey.congr_simp` (HashMap) and `get.congr_simp` (HashSet) are reserved congruence lemmas realised on demand by simp. A drop-in gets them for free.
- **notation**: `~m` is `scoped infixl:50 " ~m " => Equiv` in both Std.HashMap and Std.HashSet, so it is only available after `open Std.HashMap` / `open Std.HashSet`. The source statements use it.

## Std.HashMap

### Types, structure-generated constants, notation

- `Std.HashMap.ctorIdx` (structure_generated, def): `{α : Type u} {β : Type v} {inst✝ : BEq α} {inst✝¹ : Hashable α} : Std.HashMap α β → Nat`
- `Std.HashMap.mk.inj` (structure_generated, theorem): `{α : Type u} {β : Type v} {inst✝ : BEq α} {inst✝¹ : Hashable α} {inner inner✝ : Std.DHashMap α fun x => β} : { inner := inner } = { inner := inner✝ } → inner = inner✝`
- `Std.HashMap.mk.injEq` (structure_generated, theorem): `{α : Type u} {β : Type v} [BEq α] [Hashable α] (inner inner✝ : Std.DHashMap α fun x => β) : ({ inner := inner } = { inner := inner✝ }) = (inner = inner✝)`
- `Std.HashMap.mk.sizeOf_spec` (structure_generated, theorem): `{α : Type u} {β : Type v} [BEq α] [Hashable α] [SizeOf α] [SizeOf β] (inner : Std.DHashMap α fun x => β) : sizeOf { inner := inner } = 1 + sizeOf inner`
- `Std.HashMap.noConfusionType` (structure_generated, def): `(P : Sort u_1) {α : Type u} {β : Type v} [BEq α] [Hashable α] (t : Std.HashMap α β) {α' : Type u} {β' : Type v} [BEq α'] [Hashable α'] (t' : Std.HashMap α' β') : Sort u_1`
- `Std.HashMap` (type, structure): `(α : Type u) (β : Type v) [BEq α] [Hashable α] : Type (max u v)`
- `Std.HashMap.rec` (structure_generated, recursor): `{α : Type u} {β : Type v} [BEq α] [Hashable α] {motive : Std.HashMap α β → Sort u_1} (mk : (inner : Std.DHashMap α fun x => β) → motive { inner := inner }) (t : Std.HashMap α β) : motive t`
- `Std.HashMap.mk` (structure_generated, ctor): `{α : Type u} {β : Type v} [BEq α] [Hashable α] (inner : Std.DHashMap α fun x => β) : Std.HashMap α β`
- `Std.HashMap.inner` (structure_generated, projection): `{α : Type u} {β : Type v} [BEq α] [Hashable α] (self : Std.HashMap α β) : Std.DHashMap α fun x => β`
- `Std.HashMap.Equiv` (type, structure): `… (m₁ m₂ : Std.HashMap α β) : Prop`
- `Std.HashMap.Equiv.rec` (structure_generated, recursor): `… {m₁ m₂ : Std.HashMap α β} {motive : m₁.Equiv m₂ → Sort u_1} (mk : (inner : m₁.inner.Equiv m₂.inner) → motive ⋯) (t : m₁.Equiv m₂) : motive t`
- `Std.HashMap.Equiv.mk` (structure_generated, ctor): `… {m₁ m₂ : Std.HashMap α β} (inner : m₁.inner.Equiv m₂.inner) : m₁.Equiv m₂`
- `Std.HashMap.Equiv.inner` (structure_generated, theorem): `… {m₁ m₂ : Std.HashMap α β} (self : m₁.Equiv m₂) : m₁.inner.Equiv m₂.inner`
- `Std.HashMap.«term_~m_»` (notation, def): `: TrailingParserDescr`
- `Std.HashMap.get.congr_simp` (auto_generated, theorem): `… (m m✝ : Std.HashMap α β) (e_m : m = m✝) (a a✝ : α) (e_a : a = a✝) (h : a ∈ m) : m.get a h = m✝.get a✝ ⋯`
- `Std.HashMap.getKey.congr_simp` (auto_generated, theorem): `… (m m✝ : Std.HashMap α β) (e_m : m = m✝) (a a✝ : α) (e_a : a = a✝) (h : a ∈ m) : m.getKey a h = m✝.getKey a✝ ⋯`

### Definitions

- **emptyWithCapacity** (Basic, l.70) [cbv_opaque, inline] (lemmas mentioning it: 18)  
  `{α : Type u} {β : Type v} [BEq α] [Hashable α] (capacity : Nat := 8) : Std.HashMap α β`  
  _Creates a new empty hash map_
- **markLinear** (Basic, l.80) [never_extract, inline] (lemmas mentioning it: 1)  
  `… (m : Std.HashMap α β) : Std.HashMap α β`  
  _Marks a hash map as linear, which is a no-op logically_
- **insert** (Basic, l.92) [cbv_opaque, inline] (lemmas mentioning it: 42)  
  `… (m : Std.HashMap α β) (a : α) (b : β) : Std.HashMap α β`  
  _Inserts the given mapping into the map_
- **insertIfNew** (Basic, l.102) [inline] (lemmas mentioning it: 31)  
  `… (m : Std.HashMap α β) (a : α) (b : β) : Std.HashMap α β`  
  _If there is no mapping for the given key, inserts the given mapping into the map_
- **containsThenInsert** (Basic, l.106) [inline] (lemmas mentioning it: 2)  
  `… (m : Std.HashMap α β) (a : α) (b : β) : Bool × Std.HashMap α β`  
  _Checks whether a key is present in a map, and unconditionally inserts a value for the key_
- **containsThenInsertIfNew** (Basic, l.111) [inline] (lemmas mentioning it: 2)  
  `… (m : Std.HashMap α β) (a : α) (b : β) : Bool × Std.HashMap α β`  
  _Checks whether a key is present in a map and inserts a value for the key if it was not found_
- **getThenInsertIfNew?** (Basic, l.116) [inline] (lemmas mentioning it: 2)  
  `… (m : Std.HashMap α β) (a : α) (b : β) : Option β × Std.HashMap α β`  
  _Checks whether a key is present in a map, returning the associated value, and inserts a value for the key if it was not found_
- **get?** (Basic, l.130) [inline] (lemmas mentioning it: 4)  
  `… (m : Std.HashMap α β) (a : α) : Option β`  
  _The notation `m[a]?` is preferred over calling this function directly_
- **contains** (Basic, l.138) [inline] (lemmas mentioning it: 61)  
  `… (m : Std.HashMap α β) (a : α) : Bool`  
  _Returns `true` if there is a mapping for the given key_
- **get** (Basic, l.148) [inline] (lemmas mentioning it: 1)  
  `… (m : Std.HashMap α β) (a : α) (h : a ∈ m) : β`  
  _The notation `m[a]` or `m[a]'h` is preferred over calling this function directly_
- **getD** (Basic, l.157) [inline] (lemmas mentioning it: 48)  
  `… (m : Std.HashMap α β) (a : α) (fallback : β) : β`  
  _Tries to retrieve the mapping for the given key, returning `fallback` if no such mapping is present._
- **get!** (Basic, l.161) [inline] (lemmas mentioning it: 4)  
  `… [Inhabited β] (m : Std.HashMap α β) (a : α) : β`  
  _The notation `m[a]!` is preferred over calling this function directly_
- **getKey?** (Basic, l.174) [inline] (lemmas mentioning it: 78)  
  `… (m : Std.HashMap α β) (a : α) : Option α`  
  _Checks if a mapping for the given key exists and returns the key if it does, otherwise `none`_
- **getKey** (Basic, l.177) [inline] (lemmas mentioning it: 59)  
  `… (m : Std.HashMap α β) (a : α) (h : a ∈ m) : α`  
  _Retrieves the key from the mapping that matches `a`_
- **getKeyD** (Basic, l.180) [inline] (lemmas mentioning it: 48)  
  `… (m : Std.HashMap α β) (a fallback : α) : α`  
  _Checks if a mapping for the given key exists and returns the key if it does, otherwise `fallback`_
- **getKey!** (Basic, l.183) [inline] (lemmas mentioning it: 47)  
  `… [Inhabited α] (m : Std.HashMap α β) (a : α) : α`  
  _Checks if a mapping for the given key exists and returns the key if it does, otherwise panics_
- **erase** (Basic, l.186) [cbv_opaque, inline] (lemmas mentioning it: 28)  
  `… (m : Std.HashMap α β) (a : α) : Std.HashMap α β`  
  _Removes the mapping for the given key if it exists._
- **size** (Basic, l.190) [inline] (lemmas mentioning it: 56)  
  `… (m : Std.HashMap α β) : Nat`  
  _The number of mappings present in the hash map_
- **isEmpty** (Basic, l.193) [inline] (lemmas mentioning it: 48)  
  `… (m : Std.HashMap α β) : Bool`  
  _Returns `true` if the hash map contains no mappings_
- **keys** (Basic, l.196) [inline] (lemmas mentioning it: 27)  
  `… (m : Std.HashMap α β) : List α`  
  _Returns a list of all keys present in the hash map in some order._
- **ofList** (Basic, l.199) [inline] (lemmas mentioning it: 25)  
  `{α : Type u} {β : Type v} [BEq α] [Hashable α] (l : List (α × β)) : Std.HashMap α β`  
  _Creates a hash map from a list of mappings_
- **unitOfList** (Basic, l.203) [inline] (lemmas mentioning it: 22)  
  `{α : Type u} [BEq α] [Hashable α] (l : List α) : Std.HashMap α Unit`  
  _Creates a hash map from a list of keys, associating the value `()` with each key_
- **ofArray** (Basic, l.207) [inline] (lemmas mentioning it: 1)  
  `{α : Type u} {β : Type v} [BEq α] [Hashable α] (a : Array (α × β)) : Std.HashMap α β`  
  _Creates a hash map from an array of mappings_
- **toList** (Basic, l.211) [inline] (lemmas mentioning it: 33)  
  `… (m : Std.HashMap α β) : List (α × β)`  
  _Transforms the hash map into a list of mappings in some order._
- **foldM** (Basic, l.215) [inline] (lemmas mentioning it: 4)  
  `… {m : Type w → Type w'} [Monad m] {γ : Type w} (f : γ → α → β → m γ) (init : γ) (b : Std.HashMap α β) : m γ`  
  _Monadically computes a value by folding the given function over the mappings in the hash map in some order._
- **fold** (Basic, l.219) [inline] (lemmas mentioning it: 4)  
  `… {γ : Type w} (f : γ → α → β → γ) (init : γ) (b : Std.HashMap α β) : γ`  
  _Folds the given function over the mappings in the hash map in some order._
- **forM** (Basic, l.223) [inline] (lemmas mentioning it: 3)  
  `… {m : Type w → Type w'} [Monad m] (f : α → β → m PUnit) (b : Std.HashMap α β) : m PUnit`  
  _Carries out a monadic action on each mapping in the hash map in some order._
- **forIn** (Basic, l.227) [inline] (lemmas mentioning it: 3)  
  `… {m : Type w → Type w'} [Monad m] {γ : Type w} (f : α → β → γ → m (ForInStep γ)) (init : γ) (b : Std.HashMap α β) : m γ`  
  _Support for the `for` loop construct in `do` blocks._
- **filter** (Basic, l.237) [cbv_opaque, inline] (lemmas mentioning it: 30)  
  `… (f : α → β → Bool) (m : Std.HashMap α β) : Std.HashMap α β`  
  _Removes all mappings of the hash map for which the given function returns `false`._
- **modify** (Basic, l.241) [inline] (lemmas mentioning it: 21)  
  `… (m : Std.HashMap α β) (a : α) (f : β → β) : Std.HashMap α β`  
  _Modifies in place the value associated with a given key_
- **alter** (Basic, l.245) [inline] (lemmas mentioning it: 33)  
  `… (m : Std.HashMap α β) (a : α) (f : Option β → Option β) : Std.HashMap α β`  
  _Modifies in place the value associated with a given key, allowing creating new values and deleting values via an `Option` valued replacement function_
- **insertMany** (Basic, l.249) [inline] (lemmas mentioning it: 36)  
  `… {ρ : Type w} [ForIn Id ρ (α × β)] (m : Std.HashMap α β) (l : ρ) : Std.HashMap α β`  
  _Inserts multiple mappings into the hash map by iterating over the given collection and calling `insert`_
- **insertManyIfNewUnit** (Basic, l.253) [inline] (lemmas mentioning it: 33)  
  `… {ρ : Type w} [ForIn Id ρ α] (m : Std.HashMap α Unit) (l : ρ) : Std.HashMap α Unit`  
  _Inserts multiple keys with the value `()` into the hash map by iterating over the given collection and calling `insertIfNew`_
- **toArray** (Basic, l.257) [inline] (lemmas mentioning it: 15)  
  `… (m : Std.HashMap α β) : Array (α × β)`  
  _Transforms the hash map into an array of mappings in some order._
- **keysArray** (Basic, l.261) [inline] (lemmas mentioning it: 14)  
  `… (m : Std.HashMap α β) : Array α`  
  _Returns an array of all keys present in the hash map in some order._
- **all** (Basic, l.265) [inline] (lemmas mentioning it: 8)  
  `… (m : Std.HashMap α β) (p : α → β → Bool) : Bool`  
  _Checks if all elements satisfy the predicate, short-circuiting if a predicate fails._
- **any** (Basic, l.268) [inline] (lemmas mentioning it: 8)  
  `… (m : Std.HashMap α β) (p : α → β → Bool) : Bool`  
  _Checks if any element satisfies the predicate, short-circuiting if a predicate succeeds._
- **union** (Basic, l.270) [inline] (lemmas mentioning it: 1)  
  `{α : Type u} {β : Type v} [BEq α] [Hashable α] (m₁ m₂ : Std.HashMap α β) : Std.HashMap α β`  
  _Computes the union of the given hash maps_
- **inter** (Basic, l.282) [inline] (lemmas mentioning it: 1)  
  `{α : Type u} {β : Type v} [BEq α] [Hashable α] (m₁ m₂ : Std.HashMap α β) : Std.HashMap α β`  
  _Computes the intersection of the given hash maps_
- **beq** (Basic, l.287) (lemmas mentioning it: 0)  
  `{α : Type u} {x✝ : Hashable α} {β : Type v} [BEq α] [BEq β] (m₁ m₂ : Std.HashMap α β) : Bool`  
  _Compares two hash maps using Boolean equality on keys and values_
- **diff** (Basic, l.292) [inline] (lemmas mentioning it: 1)  
  `{α : Type u} {β : Type v} [BEq α] [Hashable α] (m₁ m₂ : Std.HashMap α β) : Std.HashMap α β`  
  _Computes the difference of the given hash maps_
- **partition** (Basic, l.301) [inline] (lemmas mentioning it: 0)  
  `… (f : α → β → Bool) (m : Std.HashMap α β) : Std.HashMap α β × Std.HashMap α β`  
  _Partition a hash map into two hash map based on a predicate._
- **values** (Basic, l.306) [inline] (lemmas mentioning it: 2)  
  `… (m : Std.HashMap α β) : List β`  
  _Returns a list of all values present in the hash map in some order._
- **valuesArray** (Basic, l.309) [inline] (lemmas mentioning it: 0)  
  `… (m : Std.HashMap α β) : Array β`  
  _Returns an array of all values present in the hash map in some order._
- **unitOfArray** (Basic, l.313) [inline] (lemmas mentioning it: 1)  
  `{α : Type u} [BEq α] [Hashable α] (l : Array α) : Std.HashMap α Unit`  
  _Creates a hash map from an array of keys, associating the value `()` with each key_
- **Internal.numBuckets** (Basic, l.317) [inline] (lemmas mentioning it: 0)  
  `… (m : Std.HashMap α β) : Nat`  
  _Returns the number of buckets in the internal representation of the hash map_
- **filterMap** (AdditionalOperations, l.44) [cbv_opaque, inline] (lemmas mentioning it: 27)  
  `{α : Type u} {β : Type v} {γ : Type w} [BEq α] [Hashable α] (f : α → β → Option γ) (m : Std.HashMap α β) : Std.HashMap α γ`  
  _Updates the values of the hash map by applying the given function to all mappings, keeping only those mappings where the function returns `some` value._
- **map** (AdditionalOperations, l.48) [cbv_opaque, inline] (lemmas mentioning it: 27)  
  `{α : Type u} {β : Type v} {γ : Type w} [BEq α] [Hashable α] (f : α → β → γ) (m : Std.HashMap α β) : Std.HashMap α γ`  
  _Updates the values of the hash map by applying the given function to all mappings._
- **iter** (Iterator, l.67) [inline] (lemmas mentioning it: 3)  
  `{α : Type u} {β : Type v} [BEq α] [Hashable α] (m : Std.HashMap α β) : Std.Iter (α × β)`  
  _Returns a finite iterator over the entries of a hash map_
- **keysIter** (Iterator, l.71) [inline] (lemmas mentioning it: 3)  
  `{α β : Type u} [BEq α] [Hashable α] (m : Std.HashMap α β) : Std.Iter α`  
  _Returns a finite iterator over the entries of a hash map_
- **valuesIter** (Iterator, l.75) [inline] (lemmas mentioning it: 3)  
  `{α β : Type u} [BEq α] [Hashable α] (m : Std.HashMap α β) : Std.Iter β`  
  _Returns a finite iterator over the entries of a hash map_

### Instances

- **instEmptyCollection**: class `EmptyCollection` (Basic, l.74); `{α : Type u} {β : Type v} [BEq α] [Hashable α] : EmptyCollection (Std.HashMap α β)`
- **instInhabited**: class `Inhabited` (Basic, l.77); `{α : Type u} {β : Type v} [BEq α] [Hashable α] : Inhabited (Std.HashMap α β)`
- **instSingletonProd**: class `Singleton` (Basic, l.96); `… : Singleton (α × β) (Std.HashMap α β)`
- **instInsertProd**: class `Insert` (Basic, l.98); `… : Insert (α × β) (Std.HashMap α β)`
- **instLawfulSingletonProd**: class `LawfulSingleton` (Basic, l.100); `… : LawfulSingleton (α × β) (Std.HashMap α β)`
- **instMembership**: class `Membership` (Basic, l.142); `{α : Type u} {β : Type v} [BEq α] [Hashable α] : Membership α (Std.HashMap α β)`
- **instDecidableMem**: class `Decidable` (Basic, l.145); `{α : Type u} {β : Type v} [BEq α] [Hashable α] {m : Std.HashMap α β} {a : α} : Decidable (a ∈ m)`
- **instGetElem?Mem**: class `GetElem?` (Basic, l.169); `{α : Type u} {β : Type v} [BEq α] [Hashable α] : GetElem? (Std.HashMap α β) α β fun m a => a ∈ m`
- **instForMProdOfMonad**: class `ForM` (Basic, l.231); `{α : Type u} {β : Type v} [BEq α] [Hashable α] {m : Type w → Type w'} [Monad m] : ForM m (Std.HashMap α β) (α × β)`
- **instForInProdOfMonad**: class `ForIn` (Basic, l.234); `{α : Type u} {β : Type v} [BEq α] [Hashable α] {m : Type w → Type w'} [Monad m] : ForIn m (Std.HashMap α β) (α × β)`
- **instUnion**: class `Union` (Basic, l.280); `{α : Type u} {β : Type v} [BEq α] [Hashable α] : Union (Std.HashMap α β)`
- **instInter**: class `Inter` (Basic, l.285); `{α : Type u} {β : Type v} [BEq α] [Hashable α] : Inter (Std.HashMap α β)`
- **instBEq**: class `BEq` (Basic, l.290); `{α : Type u} {β : Type v} {x✝ : Hashable α} [BEq α] [BEq β] : BEq (Std.HashMap α β)`
- **instSDiff**: class `SDiff` (Basic, l.295); `{α : Type u} {β : Type v} [BEq α] [Hashable α] : SDiff (Std.HashMap α β)`
- **instRepr**: class `Repr` (Basic, l.321); `{α : Type u} {β : Type v} [BEq α] [Hashable α] [Repr α] [Repr β] : Repr (Std.HashMap α β)`
- **instDecidableEquivOfLawfulBEq**: class `Decidable` (DecidableEquiv, l.20); `{α : Type u} {β : Type v} [BEq α] [LawfulBEq α] [Hashable α] [BEq β] [LawfulBEq β] (m₁ m₂ : Std.HashMap α β) : Decidable (m₁.Equiv m₂)`
- **instLawfulGetElemMemOfEquivBEqOfLawfulHashable**: class `LawfulGetElem` (Lemmas, l.852); `… [EquivBEq α] [LawfulHashable α] : LawfulGetElem (Std.HashMap α β) α β fun m a => a ∈ m`
- **instPureForInProdOfLawfulMonad**: class `Std.Internal.PureForIn` (Lemmas, l.1071); `… {m' : Type w → Type w'} [Monad m'] [LawfulMonad m'] : Std.Internal.PureForIn m' (Std.HashMap α β) (α × β)`
- **Equiv.instTrans**: class `Trans` (Lemmas, l.2891); `… : Trans Std.HashMap.Equiv Std.HashMap.Equiv Std.HashMap.Equiv`

### Theorems by section

#### HashMap.Basic: (top level) (1)

_scope: (top level)_

- **markLinear_eq** [simp, grind =]: `… {m : Std.HashMap α β} : m.markLinear = m`

#### HashMap.Lemmas: isEmpty / contains / mem basics (empty, congr, isEmpty characterisations) (18)

_scope: section@34_

- **isEmpty_emptyWithCapacity** [simp, grind =]: `… {c : Nat} : (Std.HashMap.emptyWithCapacity c).isEmpty = true`
- **isEmpty_empty** [simp, grind =]: `… : ∅.isEmpty = true`
- **isEmpty_insert** [simp, grind =]: `… {m : Std.HashMap α β} [EquivBEq α] [LawfulHashable α] {k : α} {v : β} : (m.insert k v).isEmpty = false`
- **mem_iff_contains**: `… {m : Std.HashMap α β} {a : α} : a ∈ m ↔ m.contains a = true`
- **contains_iff_mem** [simp, grind _=_]: `… {m : Std.HashMap α β} {a : α} : m.contains a = true ↔ a ∈ m`
- **contains_eq_false_iff_not_mem** [attribute [simp] (l.3581)]: `… {m : Std.HashMap α β} {k : α} : m.contains k = false ↔ ¬k ∈ m`
- **contains_congr**: `… {m : Std.HashMap α β} [EquivBEq α] [LawfulHashable α] {a b : α} (hab : (a == b) = true) : m.contains a = m.contains b`
- **mem_congr**: `… {m : Std.HashMap α β} [EquivBEq α] [LawfulHashable α] {a b : α} (hab : (a == b) = true) : a ∈ m ↔ b ∈ m`
- **contains_emptyWithCapacity** [simp, grind =, cbv_eval]: `… {a : α} {c : Nat} : (Std.HashMap.emptyWithCapacity c).contains a = false`
- **not_mem_emptyWithCapacity** [simp, grind ←]: `… {a : α} {c : Nat} : ¬a ∈ Std.HashMap.emptyWithCapacity c`
- **contains_empty** [simp, grind =]: `… {a : α} : ∅.contains a = false`
- **not_mem_empty** [simp]: `… {a : α} : ¬a ∈ ∅`
- **contains_of_isEmpty**: `… {m : Std.HashMap α β} [EquivBEq α] [LawfulHashable α] {a : α} : m.isEmpty = true → m.contains a = false`
- **not_mem_of_isEmpty**: `… {m : Std.HashMap α β} [EquivBEq α] [LawfulHashable α] {a : α} : m.isEmpty = true → ¬a ∈ m`
- **isEmpty_eq_false_iff_exists_contains_eq_true**: `… {m : Std.HashMap α β} [EquivBEq α] [LawfulHashable α] : m.isEmpty = false ↔ ∃ a, m.contains a = true`
- **isEmpty_eq_false_iff_exists_mem**: `… {m : Std.HashMap α β} [EquivBEq α] [LawfulHashable α] : m.isEmpty = false ↔ ∃ a, a ∈ m`
- **isEmpty_iff_forall_contains**: `… {m : Std.HashMap α β} [EquivBEq α] [LawfulHashable α] : m.isEmpty = true ↔ ∀ (a : α), m.contains a = false`
- **isEmpty_iff_forall_not_mem**: `… {m : Std.HashMap α β} [EquivBEq α] [LawfulHashable α] : m.isEmpty = true ↔ ∀ (a : α), ¬a ∈ m`

#### HashMap.Lemmas: insert: notation, contains, mem (8)

_scope: section@34_

- **insert_eq_insert** [simp]: `… {m : Std.HashMap α β} {p : α × β} : insert p m = m.insert p.fst p.snd`
- **singleton_eq_insert** [simp]: `… {p : α × β} : {p} = ∅.insert p.fst p.snd`
- **contains_insert** [simp, grind =, cbv_eval]: `… {m : Std.HashMap α β} [EquivBEq α] [LawfulHashable α] {k a : α} {v : β} : (m.insert k v).contains a = (k == a || m.contains a)`
- **mem_insert** [simp, grind =]: `… {m : Std.HashMap α β} [EquivBEq α] [LawfulHashable α] {k a : α} {v : β} : a ∈ m.insert k v ↔ (k == a) = true ∨ a ∈ m`
- **contains_of_contains_insert**: `… {m : Std.HashMap α β} [EquivBEq α] [LawfulHashable α] {k a : α} {v : β} : (m.insert k v).contains a = true → (k == a) = false → m.contains a = true`
- **mem_of_mem_insert**: `… {m : Std.HashMap α β} [EquivBEq α] [LawfulHashable α] {k a : α} {v : β} : a ∈ m.insert k v → (k == a) = false → a ∈ m`
- **contains_insert_self**: `… {m : Std.HashMap α β} [EquivBEq α] [LawfulHashable α] {k : α} {v : β} : (m.insert k v).contains k = true`
- **mem_insert_self**: `… {m : Std.HashMap α β} [EquivBEq α] [LawfulHashable α] {k : α} {v : β} : k ∈ m.insert k v`

#### HashMap.Lemmas: size; toList/keys/values of empty; size of insert (12)

_scope: section@34_

- **size_emptyWithCapacity** [simp, grind =]: `… {c : Nat} : (Std.HashMap.emptyWithCapacity c).size = 0`
- **size_empty** [simp, grind =]: `… : ∅.size = 0`
- **isEmpty_eq_size_eq_zero**: `… {m : Std.HashMap α β} : m.isEmpty = (m.size == 0)`
- **toList_emptyWithCapacity** [simp]: `… {c : Nat} : (Std.HashMap.emptyWithCapacity c).toList = []`
- **toList_empty** [simp]: `… : ∅.toList = []`
- **keys_emptyWithCapacity** [simp]: `… {c : Nat} : (Std.HashMap.emptyWithCapacity c).keys = []`
- **keys_empty** [simp]: `… : ∅.keys = []`
- **values_emptyWithCapacity** [simp]: `… {c : Nat} {β : Type v} : (Std.HashMap.emptyWithCapacity c).values = []`
- **values_empty** [simp]: `… {β : Type v} : ∅.values = []`
- **size_insert** [grind =]: `… {m : Std.HashMap α β} [EquivBEq α] [LawfulHashable α] {k : α} {v : β} : (m.insert k v).size = if k ∈ m then m.size else m.size + 1`
- **size_le_size_insert**: `… {m : Std.HashMap α β} [EquivBEq α] [LawfulHashable α] {k : α} {v : β} : m.size ≤ (m.insert k v).size`
- **size_insert_le**: `… {m : Std.HashMap α β} [EquivBEq α] [LawfulHashable α] {k : α} {v : β} : (m.insert k v).size ≤ m.size + 1`

#### HashMap.Lemmas: erase: isEmpty, contains, mem, size (10)

_scope: section@34_

- **erase_emptyWithCapacity** [simp, grind =, cbv_eval]: `… {a : α} {c : Nat} : (Std.HashMap.emptyWithCapacity c).erase a = Std.HashMap.emptyWithCapacity c`
- **erase_empty** [simp, grind =]: `… {a : α} : ∅.erase a = ∅`
- **isEmpty_erase** [simp, grind =]: `… {m : Std.HashMap α β} [EquivBEq α] [LawfulHashable α] {k : α} : (m.erase k).isEmpty = (m.isEmpty || m.size == 1 && m.contains k)`
- **contains_erase** [simp, grind =, cbv_eval]: `… {m : Std.HashMap α β} [EquivBEq α] [LawfulHashable α] {k a : α} : (m.erase k).contains a = (!k == a && m.contains a)`
- **mem_erase** [simp, grind =]: `… {m : Std.HashMap α β} [EquivBEq α] [LawfulHashable α] {k a : α} : a ∈ m.erase k ↔ (k == a) = false ∧ a ∈ m`
- **contains_of_contains_erase**: `… {m : Std.HashMap α β} [EquivBEq α] [LawfulHashable α] {k a : α} : (m.erase k).contains a = true → m.contains a = true`
- **mem_of_mem_erase**: `… {m : Std.HashMap α β} [EquivBEq α] [LawfulHashable α] {k a : α} : a ∈ m.erase k → a ∈ m`
- **size_erase** [grind =]: `… {m : Std.HashMap α β} [EquivBEq α] [LawfulHashable α] {k : α} : (m.erase k).size = if k ∈ m then m.size - 1 else m.size`
- **size_erase_le**: `… {m : Std.HashMap α β} [EquivBEq α] [LawfulHashable α] {k : α} : (m.erase k).size ≤ m.size`
- **size_le_size_erase**: `… {m : Std.HashMap α β} [EquivBEq α] [LawfulHashable α] {k : α} : m.size ≤ (m.erase k).size + 1`

#### HashMap.Lemmas: containsThenInsert / containsThenInsertIfNew (4)

_scope: section@34_

- **containsThenInsert_fst** [simp, grind =]: `… {m : Std.HashMap α β} {k : α} {v : β} : (m.containsThenInsert k v).fst = m.contains k`
- **containsThenInsert_snd** [simp, grind =]: `… {m : Std.HashMap α β} {k : α} {v : β} : (m.containsThenInsert k v).snd = m.insert k v`
- **containsThenInsertIfNew_fst** [simp, grind =]: `… {m : Std.HashMap α β} {k : α} {v : β} : (m.containsThenInsertIfNew k v).fst = m.contains k`
- **containsThenInsertIfNew_snd** [simp, grind =]: `… {m : Std.HashMap α β} {k : α} {v : β} : (m.containsThenInsertIfNew k v).snd = m.insertIfNew k v`

#### HashMap.Lemmas: get/get?/get! vs m[k] notation; getElem? (m[k]?) (21)

_scope: section@34_

- **get_eq_getElem** [simp, grind =]: `… {m : Std.HashMap α β} {a : α} {h : a ∈ m} : m.get a h = m[a]`
- **get?_eq_getElem?** [simp, grind =]: `… {m : Std.HashMap α β} {a : α} : m.get? a = m[a]?`
- **get!_eq_getElem!** [simp, grind =]: `… {m : Std.HashMap α β} [Inhabited β] {a : α} : m.get! a = m[a]!`
- **getElem?_emptyWithCapacity** [simp, grind =, cbv_eval]: `… {a : α} {c : Nat} : (Std.HashMap.emptyWithCapacity c)[a]? = none`
- **getElem?_empty** [simp]: `… {a : α} : ∅[a]? = none`
- **getElem?_of_isEmpty**: `… {m : Std.HashMap α β} [EquivBEq α] [LawfulHashable α] {a : α} : m.isEmpty = true → m[a]? = none`
- **getElem?_insert** [grind =, cbv_eval]: `… {m : Std.HashMap α β} [EquivBEq α] [LawfulHashable α] {k a : α} {v : β} : (m.insert k v)[a]? = if (k == a) = true then some v else m[a]?`
- **getElem?_insert_self** [simp]: `… {m : Std.HashMap α β} [EquivBEq α] [LawfulHashable α] {k : α} {v : β} : (m.insert k v)[k]? = some v`
- **get?_emptyWithCapacity** [cbv_eval]: `… {a : α} {c : Nat} : (Std.HashMap.emptyWithCapacity c).get? a = none`
- **get?_insert** [cbv_eval]: `… {m : Std.HashMap α β} [EquivBEq α] [LawfulHashable α] {k a : α} {v : β} : (m.insert k v).get? a = if (k == a) = true then some v else m.get? a`
- **contains_eq_isSome_getElem?**: `… {m : Std.HashMap α β} [EquivBEq α] [LawfulHashable α] {a : α} : m.contains a = m[a]?.isSome`
- **isSome_getElem?_eq_contains** [simp]: `… {m : Std.HashMap α β} [EquivBEq α] [LawfulHashable α] {a : α} : m[a]?.isSome = m.contains a`
- **mem_iff_isSome_getElem?**: `… {m : Std.HashMap α β} [EquivBEq α] [LawfulHashable α] {a : α} : a ∈ m ↔ m[a]?.isSome = true`
- **isSome_getElem?_iff_mem** [simp]: `… {m : Std.HashMap α β} [EquivBEq α] [LawfulHashable α] {a : α} : m[a]?.isSome = true ↔ a ∈ m`
- **getElem?_eq_some_iff**: `… {m : Std.HashMap α β} [EquivBEq α] [LawfulHashable α] {k : α} {v : β} : m[k]? = some v ↔ ∃ h, m[k] = v`
- **getElem?_eq_none_of_contains_eq_false**: `… {m : Std.HashMap α β} [EquivBEq α] [LawfulHashable α] {a : α} : m.contains a = false → m[a]? = none`
- **getElem?_eq_none**: `… {m : Std.HashMap α β} [EquivBEq α] [LawfulHashable α] {a : α} : ¬a ∈ m → m[a]? = none`
- **getElem?_erase** [grind =, cbv_eval]: `… {m : Std.HashMap α β} [EquivBEq α] [LawfulHashable α] {k a : α} : (m.erase k)[a]? = if (k == a) = true then none else m[a]?`
- **getElem?_erase_self** [simp]: `… {m : Std.HashMap α β} [EquivBEq α] [LawfulHashable α] {k : α} : (m.erase k)[k]? = none`
- **get?_erase** [cbv_eval]: `… {m : Std.HashMap α β} [EquivBEq α] [LawfulHashable α] {k a : α} : (m.erase k).get? a = if (k == a) = true then none else m.get? a`
- **getElem?_congr**: `… {m : Std.HashMap α β} [EquivBEq α] [LawfulHashable α] {a b : α} (hab : (a == b) = true) : m[a]? = m[b]?`

#### HashMap.Lemmas: getElem (m[k]'h) [also toList_insert_perm, keys_insertIfNew_perm] (9)

_scope: section@34_

- **getElem_insert** [grind =]: `… {m : Std.HashMap α β} [EquivBEq α] [LawfulHashable α] {k a : α} {v : β} {h₁ : a ∈ m.insert k v} : (m.insert k v)[a] = if h₂ : (k == a) = true then v else m[a]`
- **toList_insert_perm**: `… {m : Std.HashMap α β} [EquivBEq α] [LawfulHashable α] {k : α} {v : β} : (m.insert k v).toList.Perm ((k, v) :: List.filter (fun x => decide ¬(k == x.fst) = true) m.toList)`
- **keys_insertIfNew_perm**: `… {m : Std.HashMap α β} [EquivBEq α] [LawfulHashable α] {k : α} {v : β} : (m.insertIfNew k v).keys.Perm (if k ∈ m then m.keys else k :: m.keys)`
- **getElem_insert_self** [simp]: `… {m : Std.HashMap α β} [EquivBEq α] [LawfulHashable α] {k : α} {v : β} : (m.insert k v)[k] = v`
- **getElem_erase** [simp, grind =]: `… {m : Std.HashMap α β} [EquivBEq α] [LawfulHashable α] {k a : α} {h' : a ∈ m.erase k} : (m.erase k)[a] = m[a]`
- **getElem?_eq_some_getElem**: `… {m : Std.HashMap α β} [EquivBEq α] [LawfulHashable α] {a : α} (h' : a ∈ m) : m[a]? = some m[a]`
- **getElem_eq_get_getElem?**: `… {m : Std.HashMap α β} [EquivBEq α] [LawfulHashable α] {a : α} {h : a ∈ m} : m[a] = m[a]?.get ⋯`
- **get_getElem?** [grind =]: `… {m : Std.HashMap α β} [EquivBEq α] [LawfulHashable α] {a : α} {h : m[a]?.isSome = true} : m[a]?.get h = m[a]`
- **getElem_congr**: `… {m : Std.HashMap α β} [EquivBEq α] [LawfulHashable α] {a b : α} (hab : (a == b) = true) {h' : a ∈ m} : m[a] = m[b]`

#### HashMap.Lemmas: getElem! (m[k]!) (17)

_scope: section@34_

- **getElem!_emptyWithCapacity** [simp, grind =, cbv_eval]: `… [Inhabited β] {a : α} {c : Nat} : (Std.HashMap.emptyWithCapacity c)[a]! = default`
- **getElem!_empty** [simp, grind =]: `… [Inhabited β] {a : α} : ∅[a]! = default`
- **getElem!_of_isEmpty**: `… {m : Std.HashMap α β} [EquivBEq α] [LawfulHashable α] [Inhabited β] {a : α} : m.isEmpty = true → m[a]! = default`
- **getElem!_insert** [grind =, cbv_eval]: `… {m : Std.HashMap α β} [EquivBEq α] [LawfulHashable α] [Inhabited β] {k a : α} {v : β} : (m.insert k v)[a]! = if (k == a) = true then v else m[a]!`
- **get!_emptyWithCapacity** [cbv_eval]: `… [Inhabited β] {a : α} {c : Nat} : (Std.HashMap.emptyWithCapacity c).get! a = default`
- **get!_insert** [cbv_eval]: `… {m : Std.HashMap α β} [EquivBEq α] [LawfulHashable α] [Inhabited β] {k a : α} {v : β} : (m.insert k v).get! a = if (k == a) = true then v else m.get! a`
- **getElem!_insert_self** [simp]: `… {m : Std.HashMap α β} [EquivBEq α] [LawfulHashable α] [Inhabited β] {k : α} {v : β} : (m.insert k v)[k]! = v`
- **getElem!_eq_default_of_contains_eq_false**: `… {m : Std.HashMap α β} [EquivBEq α] [LawfulHashable α] [Inhabited β] {a : α} : m.contains a = false → m[a]! = default`
- **getElem!_eq_default**: `… {m : Std.HashMap α β} [EquivBEq α] [LawfulHashable α] [Inhabited β] {a : α} : ¬a ∈ m → m[a]! = default`
- **getElem!_erase** [grind =, cbv_eval]: `… {m : Std.HashMap α β} [EquivBEq α] [LawfulHashable α] [Inhabited β] {k a : α} : (m.erase k)[a]! = if (k == a) = true then default else m[a]!`
- **getElem!_erase_self** [simp]: `… {m : Std.HashMap α β} [EquivBEq α] [LawfulHashable α] [Inhabited β] {k : α} : (m.erase k)[k]! = default`
- **get!_erase** [cbv_eval]: `… {m : Std.HashMap α β} [EquivBEq α] [LawfulHashable α] [Inhabited β] {k a : α} : (m.erase k).get! a = if (k == a) = true then default else m.get! a`
- **getElem?_eq_some_getElem!_of_contains**: `… {m : Std.HashMap α β} [EquivBEq α] [LawfulHashable α] [Inhabited β] {a : α} : m.contains a = true → m[a]? = some m[a]!`
- **getElem?_eq_some_getElem!**: `… {m : Std.HashMap α β} [EquivBEq α] [LawfulHashable α] [Inhabited β] {a : α} : a ∈ m → m[a]? = some m[a]!`
- **getElem!_eq_get!_getElem?**: `… {m : Std.HashMap α β} [EquivBEq α] [LawfulHashable α] [Inhabited β] {a : α} : m[a]! = m[a]?.get!`
- **getElem_eq_getElem!**: `… {m : Std.HashMap α β} [EquivBEq α] [LawfulHashable α] [Inhabited β] {a : α} {h' : a ∈ m} : m[a] = m[a]!`
- **getElem!_congr**: `… {m : Std.HashMap α β} [EquivBEq α] [LawfulHashable α] [Inhabited β] {a b : α} (hab : (a == b) = true) : m[a]! = m[b]!`

#### HashMap.Lemmas: getD (15)

_scope: section@34_

- **getD_emptyWithCapacity** [simp, grind =, cbv_eval]: `… {a : α} {fallback : β} {c : Nat} : (Std.HashMap.emptyWithCapacity c).getD a fallback = fallback`
- **getD_empty** [simp, grind =]: `… {a : α} {fallback : β} : ∅.getD a fallback = fallback`
- **getD_of_isEmpty**: `… {m : Std.HashMap α β} [EquivBEq α] [LawfulHashable α] {a : α} {fallback : β} : m.isEmpty = true → m.getD a fallback = fallback`
- **getD_insert** [grind =, cbv_eval]: `… {m : Std.HashMap α β} [EquivBEq α] [LawfulHashable α] {k a : α} {fallback v : β} : (m.insert k v).getD a fallback = if (k == a) = true then v else m.getD a fallback`
- **getD_insert_self** [simp]: `… {m : Std.HashMap α β} [EquivBEq α] [LawfulHashable α] {k : α} {fallback v : β} : (m.insert k v).getD k fallback = v`
- **getD_eq_fallback_of_contains_eq_false**: `… {m : Std.HashMap α β} [EquivBEq α] [LawfulHashable α] {a : α} {fallback : β} : m.contains a = false → m.getD a fallback = fallback`
- **getD_eq_fallback**: `… {m : Std.HashMap α β} [EquivBEq α] [LawfulHashable α] {a : α} {fallback : β} : ¬a ∈ m → m.getD a fallback = fallback`
- **getD_erase** [grind =, cbv_eval]: `… {m : Std.HashMap α β} [EquivBEq α] [LawfulHashable α] {k a : α} {fallback : β} : (m.erase k).getD a fallback = if (k == a) = true then fallback else m.getD a fallback`
- **getD_erase_self** [simp]: `… {m : Std.HashMap α β} [EquivBEq α] [LawfulHashable α] {k : α} {fallback : β} : (m.erase k).getD k fallback = fallback`
- **getElem?_eq_some_getD_of_contains**: `… {m : Std.HashMap α β} [EquivBEq α] [LawfulHashable α] {a : α} {fallback : β} : m.contains a = true → m[a]? = some (m.getD a fallback)`
- **getElem?_eq_some_getD**: `… {m : Std.HashMap α β} [EquivBEq α] [LawfulHashable α] {a : α} {fallback : β} : a ∈ m → m[a]? = some (m.getD a fallback)`
- **getD_eq_getD_getElem?**: `… {m : Std.HashMap α β} [EquivBEq α] [LawfulHashable α] {a : α} {fallback : β} : m.getD a fallback = m[a]?.getD fallback`
- **getElem_eq_getD**: `… {m : Std.HashMap α β} [EquivBEq α] [LawfulHashable α] {a : α} {fallback : β} {h' : a ∈ m} : m[a] = m.getD a fallback`
- **getElem!_eq_getD_default**: `… {m : Std.HashMap α β} [EquivBEq α] [LawfulHashable α] [Inhabited β] {a : α} : m[a]! = m.getD a default`
- **getD_congr**: `… {m : Std.HashMap α β} [EquivBEq α] [LawfulHashable α] {a b : α} {fallback : β} (hab : (a == b) = true) : m.getD a fallback = m.getD b fallback`

#### HashMap.Lemmas: getKey? (19)

_scope: section@34_

- **getKey?_emptyWithCapacity** [simp, grind =]: `… {a : α} {c : Nat} : (Std.HashMap.emptyWithCapacity c).getKey? a = none`
- **getKey?_empty** [simp, grind =]: `… {a : α} : ∅.getKey? a = none`
- **getKey?_of_isEmpty**: `… {m : Std.HashMap α β} [EquivBEq α] [LawfulHashable α] {a : α} : m.isEmpty = true → m.getKey? a = none`
- **getKey?_insert** [grind =]: `… {m : Std.HashMap α β} [EquivBEq α] [LawfulHashable α] {k a : α} {v : β} : (m.insert k v).getKey? a = if (k == a) = true then some k else m.getKey? a`
- **getKey?_insert_self** [simp]: `… {m : Std.HashMap α β} [EquivBEq α] [LawfulHashable α] {k : α} {v : β} : (m.insert k v).getKey? k = some k`
- **contains_eq_isSome_getKey?**: `… {m : Std.HashMap α β} [EquivBEq α] [LawfulHashable α] {a : α} : m.contains a = (m.getKey? a).isSome`
- **isSome_getKey?_eq_contains** [simp, grind =]: `… {m : Std.HashMap α β} [EquivBEq α] [LawfulHashable α] {a : α} : (m.getKey? a).isSome = m.contains a`
- **mem_iff_isSome_getKey?**: `… {m : Std.HashMap α β} [EquivBEq α] [LawfulHashable α] {a : α} : a ∈ m ↔ (m.getKey? a).isSome = true`
- **isSome_getKey?_iff_mem** [simp]: `… {m : Std.HashMap α β} [EquivBEq α] [LawfulHashable α] {a : α} : (m.getKey? a).isSome = true ↔ a ∈ m`
- **mem_of_getKey?_eq_some**: `… {m : Std.HashMap α β} [EquivBEq α] [LawfulHashable α] {k k' : α} (h : m.getKey? k = some k') : k' ∈ m`
- **getKey?_eq_some_iff**: `… {m : Std.HashMap α β} [EquivBEq α] [LawfulHashable α] {k k' : α} : m.getKey? k = some k' ↔ ∃ h, m.getKey k h = k'`
- **getKey?_eq_none_of_contains_eq_false**: `… {m : Std.HashMap α β} [EquivBEq α] [LawfulHashable α] {a : α} : m.contains a = false → m.getKey? a = none`
- **getKey?_eq_none**: `… {m : Std.HashMap α β} [EquivBEq α] [LawfulHashable α] {a : α} : ¬a ∈ m → m.getKey? a = none`
- **getKey?_erase** [grind =]: `… {m : Std.HashMap α β} [EquivBEq α] [LawfulHashable α] {k a : α} : (m.erase k).getKey? a = if (k == a) = true then none else m.getKey? a`
- **getKey?_erase_self** [simp]: `… {m : Std.HashMap α β} [EquivBEq α] [LawfulHashable α] {k : α} : (m.erase k).getKey? k = none`
- **getKey?_beq**: `… {m : Std.HashMap α β} [EquivBEq α] [LawfulHashable α] {k : α} : Option.all (fun x => x == k) (m.getKey? k) = true`
- **getKey?_congr**: `… {m : Std.HashMap α β} [EquivBEq α] [LawfulHashable α] {k k' : α} (h : (k == k') = true) : m.getKey? k = m.getKey? k'`
- **getKey?_eq_some_of_contains**: `… {m : Std.HashMap α β} [LawfulBEq α] {k : α} (h : m.contains k = true) : m.getKey? k = some k`
- **getKey?_eq_some**: `… {m : Std.HashMap α β} [LawfulBEq α] {k : α} (h : k ∈ m) : m.getKey? k = some k`

#### HashMap.Lemmas: getKey (9)

_scope: section@34_

- **getKey_insert** [grind =]: `… {m : Std.HashMap α β} [EquivBEq α] [LawfulHashable α] {k a : α} {v : β} {h₁ : a ∈ m.insert k v} : (m.insert k v).getKey a h₁ = if h₂ : (k == a) = true then k else m.getKey a ⋯`
- **getKey_insert_self** [simp]: `… {m : Std.HashMap α β} [EquivBEq α] [LawfulHashable α] {k : α} {v : β} : (m.insert k v).getKey k ⋯ = k`
- **getKey_erase** [simp, grind =]: `… {m : Std.HashMap α β} [EquivBEq α] [LawfulHashable α] {k a : α} {h' : a ∈ m.erase k} : (m.erase k).getKey a h' = m.getKey a ⋯`
- **getKey?_eq_some_getKey**: `… {m : Std.HashMap α β} [EquivBEq α] [LawfulHashable α] {a : α} (h : a ∈ m) : m.getKey? a = some (m.getKey a h)`
- **getKey_eq_get_getKey?**: `… {m : Std.HashMap α β} [EquivBEq α] [LawfulHashable α] {a : α} {h : a ∈ m} : m.getKey a h = (m.getKey? a).get ⋯`
- **get_getKey?** [simp, grind =]: `… {m : Std.HashMap α β} [EquivBEq α] [LawfulHashable α] {a : α} {h : (m.getKey? a).isSome = true} : (m.getKey? a).get h = m.getKey a ⋯`
- **getKey_beq**: `… {m : Std.HashMap α β} [EquivBEq α] [LawfulHashable α] {k : α} (h : k ∈ m) : (m.getKey k h == k) = true`
- **getKey_congr**: `… {m : Std.HashMap α β} [EquivBEq α] [LawfulHashable α] {k₁ k₂ : α} (h : (k₁ == k₂) = true) (h₁ : k₁ ∈ m) : m.getKey k₁ h₁ = m.getKey k₂ ⋯`
- **getKey_eq** [simp, grind =]: `… {m : Std.HashMap α β} [LawfulBEq α] {k : α} (h : k ∈ m) : m.getKey k h = k`

#### HashMap.Lemmas: getKey! (16)

_scope: section@34_

- **getKey!_emptyWithCapacity** [simp, grind =]: `… [Inhabited α] {a : α} {c : Nat} : (Std.HashMap.emptyWithCapacity c).getKey! a = default`
- **getKey!_empty** [simp, grind =]: `… [Inhabited α] {a : α} : ∅.getKey! a = default`
- **getKey!_of_isEmpty**: `… {m : Std.HashMap α β} [EquivBEq α] [LawfulHashable α] [Inhabited α] {a : α} : m.isEmpty = true → m.getKey! a = default`
- **getKey!_insert** [grind =]: `… {m : Std.HashMap α β} [EquivBEq α] [LawfulHashable α] [Inhabited α] {k a : α} {v : β} : (m.insert k v).getKey! a = if (k == a) = true then k else m.getKey! a`
- **getKey!_insert_self** [simp]: `… {m : Std.HashMap α β} [EquivBEq α] [LawfulHashable α] [Inhabited α] {k : α} {v : β} : (m.insert k v).getKey! k = k`
- **getKey!_eq_default_of_contains_eq_false**: `… {m : Std.HashMap α β} [EquivBEq α] [LawfulHashable α] [Inhabited α] {a : α} : m.contains a = false → m.getKey! a = default`
- **getKey!_eq_default**: `… {m : Std.HashMap α β} [EquivBEq α] [LawfulHashable α] [Inhabited α] {a : α} : ¬a ∈ m → m.getKey! a = default`
- **getKey!_erase** [grind =]: `… {m : Std.HashMap α β} [EquivBEq α] [LawfulHashable α] [Inhabited α] {k a : α} : (m.erase k).getKey! a = if (k == a) = true then default else m.getKey! a`
- **getKey!_erase_self** [simp]: `… {m : Std.HashMap α β} [EquivBEq α] [LawfulHashable α] [Inhabited α] {k : α} : (m.erase k).getKey! k = default`
- **getKey?_eq_some_getKey!_of_contains**: `… {m : Std.HashMap α β} [EquivBEq α] [LawfulHashable α] [Inhabited α] {a : α} : m.contains a = true → m.getKey? a = some (m.getKey! a)`
- **getKey?_eq_some_getKey!**: `… {m : Std.HashMap α β} [EquivBEq α] [LawfulHashable α] [Inhabited α] {a : α} : a ∈ m → m.getKey? a = some (m.getKey! a)`
- **getKey!_eq_get!_getKey?**: `… {m : Std.HashMap α β} [EquivBEq α] [LawfulHashable α] [Inhabited α] {a : α} : m.getKey! a = (m.getKey? a).get!`
- **getKey_eq_getKey!**: `… {m : Std.HashMap α β} [EquivBEq α] [LawfulHashable α] [Inhabited α] {a : α} {h' : a ∈ m} : m.getKey a h' = m.getKey! a`
- **getKey!_congr**: `… {m : Std.HashMap α β} [EquivBEq α] [LawfulHashable α] [Inhabited α] {k k' : α} (h : (k == k') = true) : m.getKey! k = m.getKey! k'`
- **getKey!_eq_of_contains**: `… {m : Std.HashMap α β} [LawfulBEq α] [Inhabited α] {k : α} (h : m.contains k = true) : m.getKey! k = k`
- **getKey!_eq_of_mem**: `… {m : Std.HashMap α β} [LawfulBEq α] [Inhabited α] {k : α} (h : k ∈ m) : m.getKey! k = k`

#### HashMap.Lemmas: getKeyD (17)

_scope: section@34_

- **getKeyD_emptyWithCapacity** [simp, grind =]: `… {a fallback : α} {c : Nat} : (Std.HashMap.emptyWithCapacity c).getKeyD a fallback = fallback`
- **getKeyD_empty** [simp, grind =]: `… {a fallback : α} : ∅.getKeyD a fallback = fallback`
- **getKeyD_of_isEmpty**: `… {m : Std.HashMap α β} [EquivBEq α] [LawfulHashable α] {a fallback : α} : m.isEmpty = true → m.getKeyD a fallback = fallback`
- **getKeyD_insert** [grind =]: `… {m : Std.HashMap α β} [EquivBEq α] [LawfulHashable α] {k a fallback : α} {v : β} : (m.insert k v).getKeyD a fallback = if (k == a) = true then k else m.getKeyD a fallback`
- **getKeyD_insert_self** [simp]: `… {m : Std.HashMap α β} [EquivBEq α] [LawfulHashable α] {k fallback : α} {v : β} : (m.insert k v).getKeyD k fallback = k`
- **getKeyD_eq_fallback_of_contains_eq_false**: `… {m : Std.HashMap α β} [EquivBEq α] [LawfulHashable α] {a fallback : α} : m.contains a = false → m.getKeyD a fallback = fallback`
- **getKeyD_eq_fallback**: `… {m : Std.HashMap α β} [EquivBEq α] [LawfulHashable α] {a fallback : α} : ¬a ∈ m → m.getKeyD a fallback = fallback`
- **getKeyD_erase** [grind =]: `… {m : Std.HashMap α β} [EquivBEq α] [LawfulHashable α] {k a fallback : α} : (m.erase k).getKeyD a fallback = if (k == a) = true then fallback else m.getKeyD a fallback`
- **getKeyD_erase_self** [simp]: `… {m : Std.HashMap α β} [EquivBEq α] [LawfulHashable α] {k fallback : α} : (m.erase k).getKeyD k fallback = fallback`
- **getKey?_eq_some_getKeyD_of_contains**: `… {m : Std.HashMap α β} [EquivBEq α] [LawfulHashable α] {a fallback : α} : m.contains a = true → m.getKey? a = some (m.getKeyD a fallback)`
- **getKey?_eq_some_getKeyD**: `… {m : Std.HashMap α β} [EquivBEq α] [LawfulHashable α] {a fallback : α} : a ∈ m → m.getKey? a = some (m.getKeyD a fallback)`
- **getKeyD_eq_getD_getKey?**: `… {m : Std.HashMap α β} [EquivBEq α] [LawfulHashable α] {a fallback : α} : m.getKeyD a fallback = (m.getKey? a).getD fallback`
- **getKey_eq_getKeyD**: `… {m : Std.HashMap α β} [EquivBEq α] [LawfulHashable α] {a fallback : α} {h' : a ∈ m} : m.getKey a h' = m.getKeyD a fallback`
- **getKey!_eq_getKeyD_default**: `… {m : Std.HashMap α β} [EquivBEq α] [LawfulHashable α] [Inhabited α] {a : α} : m.getKey! a = m.getKeyD a default`
- **getKeyD_congr**: `… {m : Std.HashMap α β} [EquivBEq α] [LawfulHashable α] {k k' fallback : α} (h : (k == k') = true) : m.getKeyD k fallback = m.getKeyD k' fallback`
- **getKeyD_eq_of_contains**: `… {m : Std.HashMap α β} [LawfulBEq α] {k fallback : α} (h : m.contains k = true) : m.getKeyD k fallback = k`
- **getKeyD_eq_of_mem**: `… {m : Std.HashMap α β} [LawfulBEq α] {k fallback : α} (h : k ∈ m) : m.getKeyD k fallback = k`

#### HashMap.Lemmas: insertIfNew (20)

_scope: section@34_

- **isEmpty_insertIfNew** [simp, grind =]: `… {m : Std.HashMap α β} [EquivBEq α] [LawfulHashable α] {k : α} {v : β} : (m.insertIfNew k v).isEmpty = false`
- **contains_insertIfNew** [simp, grind =]: `… {m : Std.HashMap α β} [EquivBEq α] [LawfulHashable α] {k a : α} {v : β} : (m.insertIfNew k v).contains a = (k == a || m.contains a)`
- **mem_insertIfNew** [simp, grind =]: `… {m : Std.HashMap α β} [EquivBEq α] [LawfulHashable α] {k a : α} {v : β} : a ∈ m.insertIfNew k v ↔ (k == a) = true ∨ a ∈ m`
- **contains_insertIfNew_self**: `… {m : Std.HashMap α β} [EquivBEq α] [LawfulHashable α] {k : α} {v : β} : (m.insertIfNew k v).contains k = true`
- **mem_insertIfNew_self**: `… {m : Std.HashMap α β} [EquivBEq α] [LawfulHashable α] {k : α} {v : β} : k ∈ m.insertIfNew k v`
- **contains_of_contains_insertIfNew**: `… {m : Std.HashMap α β} [EquivBEq α] [LawfulHashable α] {k a : α} {v : β} : (m.insertIfNew k v).contains a = true → (k == a) = false → m.contains a = true`
- **mem_of_mem_insertIfNew**: `… {m : Std.HashMap α β} [EquivBEq α] [LawfulHashable α] {k a : α} {v : β} : a ∈ m.insertIfNew k v → (k == a) = false → a ∈ m`
- **contains_of_contains_insertIfNew'**: `… {m : Std.HashMap α β} [EquivBEq α] [LawfulHashable α] {k a : α} {v : β} : (m.insertIfNew k v).contains a = true → ¬((k == a) = true ∧ m.contains k = false) → m.contains a = true`
- **mem_of_mem_insertIfNew'**: `… {m : Std.HashMap α β} [EquivBEq α] [LawfulHashable α] {k a : α} {v : β} : a ∈ m.insertIfNew k v → ¬((k == a) = true ∧ ¬k ∈ m) → a ∈ m`
- **size_insertIfNew** [grind =]: `… {m : Std.HashMap α β} [EquivBEq α] [LawfulHashable α] {k : α} {v : β} : (m.insertIfNew k v).size = if k ∈ m then m.size else m.size + 1`
- **size_le_size_insertIfNew**: `… {m : Std.HashMap α β} [EquivBEq α] [LawfulHashable α] {k : α} {v : β} : m.size ≤ (m.insertIfNew k v).size`
- **size_insertIfNew_le**: `… {m : Std.HashMap α β} [EquivBEq α] [LawfulHashable α] {k : α} {v : β} : (m.insertIfNew k v).size ≤ m.size + 1`
- **getElem?_insertIfNew** [grind =]: `… {m : Std.HashMap α β} [EquivBEq α] [LawfulHashable α] {k a : α} {v : β} : (m.insertIfNew k v)[a]? = if (k == a) = true ∧ ¬k ∈ m then some v else m[a]?`
- **getElem_insertIfNew** [grind =]: `… {m : Std.HashMap α β} [EquivBEq α] [LawfulHashable α] {k a : α} {v : β} {h₁ : a ∈ m.insertIfNew k v} : (m.insertIfNew k v)[a] = if h₂ : (k == a) = true ∧ ¬k ∈ m then v else m[a]`
- **getElem!_insertIfNew** [grind =]: `… {m : Std.HashMap α β} [EquivBEq α] [LawfulHashable α] [Inhabited β] {k a : α} {v : β} : (m.insertIfNew k v)[a]! = if (k == a) = true ∧ ¬k ∈ m then v else m[a]!`
- **getD_insertIfNew** [grind =]: `… {m : Std.HashMap α β} [EquivBEq α] [LawfulHashable α] {k a : α} {fallback v : β} : (m.insertIfNew k v).getD a fallback = if (k == a) = true ∧ ¬k ∈ m then v else m.getD a fallback`
- **getKey?_insertIfNew** [grind =]: `… {m : Std.HashMap α β} [EquivBEq α] [LawfulHashable α] {k a : α} {v : β} : (m.insertIfNew k v).getKey? a = if (k == a) = true ∧ ¬k ∈ m then some k else m.getKey? a`
- **getKey_insertIfNew** [grind =]: `… {m : Std.HashMap α β} [EquivBEq α] [LawfulHashable α] {k a : α} {v : β} {h₁ : a ∈ m.insertIfNew k v} : (m.insertIfNew k v).getKey a h₁ = if h₂ : (k == a) = true ∧ ¬k ∈ m then k else m.getKey a ⋯`
- **getKey!_insertIfNew** [grind =]: `… {m : Std.HashMap α β} [EquivBEq α] [LawfulHashable α] [Inhabited α] {k a : α} {v : β} : (m.insertIfNew k v).getKey! a = if (k == a) = true ∧ ¬k ∈ m then k else m.getKey! a`
- **getKeyD_insertIfNew** [grind =]: `… {m : Std.HashMap α β} [EquivBEq α] [LawfulHashable α] {k a fallback : α} {v : β} : (m.insertIfNew k v).getKeyD a fallback = if (k == a) = true ∧ ¬k ∈ m then k else m.getKeyD a fallback`

#### HashMap.Lemmas: getThenInsertIfNew? (2)

_scope: section@34_

- **getThenInsertIfNew?_fst** [simp, grind =]: `… {m : Std.HashMap α β} {k : α} {v : β} : (m.getThenInsertIfNew? k v).fst = m[k]?`
- **getThenInsertIfNew?_snd** [simp, grind =]: `… {m : Std.HashMap α β} {k : α} {v : β} : (m.getThenInsertIfNew? k v).snd = m.insertIfNew k v`

#### HashMap.Lemmas: keys / keysArray (15)

_scope: section@34_

- **length_keys** [simp, grind =]: `… {m : Std.HashMap α β} [EquivBEq α] [LawfulHashable α] : m.keys.length = m.size`
- **isEmpty_keys** [simp, grind =]: `… {m : Std.HashMap α β} [EquivBEq α] [LawfulHashable α] : m.keys.isEmpty = m.isEmpty`
- **contains_keys** [simp, grind =]: `… {m : Std.HashMap α β} [EquivBEq α] [LawfulHashable α] {k : α} : m.keys.contains k = m.contains k`
- **mem_keys** [simp, grind =]: `… {m : Std.HashMap α β} [LawfulBEq α] {k : α} : k ∈ m.keys ↔ k ∈ m`
- **mem_of_mem_keys**: `… {m : Std.HashMap α β} [EquivBEq α] [LawfulHashable α] {k : α} (h : k ∈ m.keys) : k ∈ m`
- **distinct_keys**: `… {m : Std.HashMap α β} [EquivBEq α] [LawfulHashable α] : List.Pairwise (fun a b => (a == b) = false) m.keys`
- **nodup_keys**: `… {m : Std.HashMap α β} [EquivBEq α] [LawfulHashable α] : m.keys.Nodup`
- **toArray_keys** [simp]: `… {m : Std.HashMap α β} : m.keys.toArray = m.keysArray`
- **toList_keysArray** [simp]: `… {m : Std.HashMap α β} : m.keysArray.toList = m.keys`
- **size_keysArray** [simp]: `… {m : Std.HashMap α β} [EquivBEq α] [LawfulHashable α] : m.keysArray.size = m.size`
- **isEmpty_keysArray** [simp]: `… {m : Std.HashMap α β} [EquivBEq α] [LawfulHashable α] : m.keysArray.isEmpty = m.isEmpty`
- **contains_keysArray** [simp]: `… {m : Std.HashMap α β} [EquivBEq α] [LawfulHashable α] {k : α} : m.keysArray.contains k = m.contains k`
- **mem_keysArray** [simp]: `… {m : Std.HashMap α β} [LawfulBEq α] {k : α} : k ∈ m.keysArray ↔ k ∈ m`
- **forall_mem_keysArray_iff_forall_mem_getKey**: `… {m : Std.HashMap α β} [EquivBEq α] [LawfulHashable α] {p : α → Prop} : (∀ (k : α), k ∈ m.keysArray → p k) ↔ ∀ (k : α) (h : k ∈ m), p (m.getKey k h)`
- **contains_of_mem_keysArray**: `… {m : Std.HashMap α β} [EquivBEq α] [LawfulHashable α] {k : α} (h' : k ∈ m.keysArray) : m.contains k = true`

#### HashMap.Lemmas: toList / toArray (20)

_scope: section@34_

- **map_fst_toList_eq_keys** [simp, grind _=_]: `… {m : Std.HashMap α β} [EquivBEq α] [LawfulHashable α] : List.map Prod.fst m.toList = m.keys`
- **length_toList** [simp, grind =]: `… {m : Std.HashMap α β} [EquivBEq α] [LawfulHashable α] : m.toList.length = m.size`
- **isEmpty_toList** [simp, grind =]: `… {m : Std.HashMap α β} [EquivBEq α] [LawfulHashable α] : m.toList.isEmpty = m.isEmpty`
- **mem_toList_iff_getElem?_eq_some** [simp, grind =]: `… {m : Std.HashMap α β} [LawfulBEq α] {k : α} {v : β} : (k, v) ∈ m.toList ↔ m[k]? = some v`
- **mem_toList_iff_getKey?_eq_some_and_getElem?_eq_some** [simp]: `… {m : Std.HashMap α β} [EquivBEq α] [LawfulHashable α] {k : α} {v : β} : (k, v) ∈ m.toList ↔ m.getKey? k = some k ∧ m[k]? = some v`
- **getElem?_eq_some_iff_exists_beq_and_mem_toList**: `… {m : Std.HashMap α β} [EquivBEq α] [LawfulHashable α] {k : α} {v : β} : m[k]? = some v ↔ ∃ k', (k == k') = true ∧ (k', v) ∈ m.toList`
- **find?_toList_eq_some_iff_getKey?_eq_some_and_getElem?_eq_some**: `… {m : Std.HashMap α β} [EquivBEq α] [LawfulHashable α] {k k' : α} {v : β} : List.find? (fun a => a.fst == k) m.toList = some (k', v) ↔ m.getKey? k = some k' ∧ m[k]? = some v`
- **find?_toList_eq_none_iff_contains_eq_false**: `… {m : Std.HashMap α β} [EquivBEq α] [LawfulHashable α] {k : α} : List.find? (fun x => x.fst == k) m.toList = none ↔ m.contains k = false`
- **find?_toList_eq_none_iff_not_mem** [simp]: `… {m : Std.HashMap α β} [EquivBEq α] [LawfulHashable α] {k : α} : List.find? (fun x => x.fst == k) m.toList = none ↔ ¬k ∈ m`
- **distinct_keys_toList**: `… {m : Std.HashMap α β} [EquivBEq α] [LawfulHashable α] : List.Pairwise (fun a b => (a.fst == b.fst) = false) m.toList`
- **toArray_toList** [simp]: `… {m : Std.HashMap α β} : m.toList.toArray = m.toArray`
- **toList_toArray** [simp]: `… {m : Std.HashMap α β} : m.toArray.toList = m.toList`
- **map_fst_toArray_eq_keysArray** [simp]: `… {m : Std.HashMap α β} [EquivBEq α] [LawfulHashable α] : Array.map Prod.fst m.toArray = m.keysArray`
- **size_toArray** [simp]: `… {m : Std.HashMap α β} [EquivBEq α] [LawfulHashable α] : m.toArray.size = m.size`
- **isEmpty_toArray** [simp]: `… {m : Std.HashMap α β} [EquivBEq α] [LawfulHashable α] : m.toArray.isEmpty = m.isEmpty`
- **mem_toArray_iff_getElem?_eq_some**: `… {m : Std.HashMap α β} [LawfulBEq α] {k : α} {v : β} : (k, v) ∈ m.toArray ↔ m[k]? = some v`
- **getElem?_eq_some_iff_exists_beq_and_mem_toArray**: `… {m : Std.HashMap α β} [EquivBEq α] [LawfulHashable α] {k : α} {v : β} : m[k]? = some v ↔ ∃ k', (k == k') = true ∧ (k', v) ∈ m.toArray`
- **find?_toArray_eq_some_iff_getKey?_eq_some_and_getElem?_eq_some**: `… {m : Std.HashMap α β} [EquivBEq α] [LawfulHashable α] {k k' : α} {v : β} : Array.find? (fun a => a.fst == k) m.toArray = some (k', v) ↔ m.getKey? k = some k' ∧ m[k]? = some v`
- **find?_toArray_eq_none_iff_contains_eq_false**: `… {m : Std.HashMap α β} [EquivBEq α] [LawfulHashable α] {k : α} : Array.find? (fun x => x.fst == k) m.toArray = none ↔ m.contains k = false`
- **mem_toArray_iff_getKey?_eq_some_and_getElem?_eq_some**: `… {m : Std.HashMap α β} [EquivBEq α] [LawfulHashable α] {k : α} {v : β} : (k, v) ∈ m.toArray ↔ m.getKey? k = some k ∧ m[k]? = some v`

#### HashMap.Lemmas: monadic: fold / foldM / forM / forIn (19)

_scope: section@34 › section monadic_

- **foldM_eq_foldlM_toList**: `… {m : Std.HashMap α β} {δ : Type w} {m' : Type w → Type w'} [Monad m'] [LawfulMonad m'] {f : δ → α → β → m' δ} {init : δ} : Std.HashMap.foldM f init m = List.foldlM (fun a b => f a b.fst b.snd) init m.toList`
- **fold_eq_foldl_toList**: `… {m : Std.HashMap α β} {δ : Type w} {f : δ → α → β → δ} {init : δ} : Std.HashMap.fold f init m = List.foldl (fun a b => f a b.fst b.snd) init m.toList`
- **forM_eq_forM** [simp, grind =]: `… {m : Std.HashMap α β} {m' : Type w → Type w'} [Monad m'] [LawfulMonad m'] {f : α → β → m' PUnit} : Std.HashMap.forM f m = forM m fun a => f a.fst a.snd`
- **forM_eq_forM_toList**: `… {m : Std.HashMap α β} {m' : Type w → Type w'} [Monad m'] [LawfulMonad m'] {f : α × β → m' PUnit} : forM m f = forM m.toList f`
- **forIn_eq_forIn** [simp, grind =]: `… {m : Std.HashMap α β} {δ : Type w} {m' : Type w → Type w'} [Monad m'] [LawfulMonad m'] {f : α → β → δ → m' (ForInStep δ)} {init : δ} : Std.HashMap.forIn f init m = forIn m init fun a d => f a.fst a.snd d`
- **forIn_eq_forIn_toList**: `… {m : Std.HashMap α β} {δ : Type w} {m' : Type w → Type w'} [Monad m'] [LawfulMonad m'] {f : α × β → δ → m' (ForInStep δ)} {init : δ} : forIn m init f = forIn m.toList init f`
- **forIn_toList** [simp, grind =]: `… (c : Std.HashMap α β) : ForIn.toList c = c.toList`
- **foldM_eq_foldlM_keys**: `… {m : Std.HashMap α β} {δ : Type w} {m' : Type w → Type w'} [Monad m'] [LawfulMonad m'] {f : δ → α → m' δ} {init : δ} : Std.HashMap.foldM (fun d a x => f d a) init m = List.foldlM f init m.keys`
- **fold_eq_foldl_keys**: `… {m : Std.HashMap α β} {δ : Type w} {f : δ → α → δ} {init : δ} : Std.HashMap.fold (fun d a x => f d a) init m = List.foldl f init m.keys`
- **forM_eq_forM_keys**: `… {m : Std.HashMap α β} {m' : Type w → Type w'} [Monad m'] [LawfulMonad m'] {f : α → m' PUnit} : (forM m fun a => f a.fst) = m.keys.forM f`
- **forIn_eq_forIn_keys**: `… {m : Std.HashMap α β} {δ : Type w} {m' : Type w → Type w'} [Monad m'] [LawfulMonad m'] {f : α → δ → m' (ForInStep δ)} {init : δ} : (forIn m init fun a d => f a.fst d) = forIn m.keys init f`
- **foldM_eq_foldlM_toArray**: `… {m : Std.HashMap α β} {δ : Type w} {m' : Type w → Type w'} [Monad m'] [LawfulMonad m'] {f : δ → α → β → m' δ} {init : δ} : Std.HashMap.foldM f init m = Array.foldlM (fun a b => f a b.fst b.snd) init m.toArray`
- **fold_eq_foldl_toArray**: `… {m : Std.HashMap α β} {δ : Type w} {f : δ → α → β → δ} {init : δ} : Std.HashMap.fold f init m = Array.foldl (fun a b => f a b.fst b.snd) init m.toArray`
- **forM_eq_forM_toArray**: `… {m : Std.HashMap α β} {m' : Type w → Type w'} [Monad m'] [LawfulMonad m'] {f : α → β → m' PUnit} : Std.HashMap.forM f m = Array.forM (fun a => f a.fst a.snd) m.toArray`
- **forIn_eq_forIn_toArray**: `… {m : Std.HashMap α β} {δ : Type w} {m' : Type w → Type w'} [Monad m'] [LawfulMonad m'] {f : α → β → δ → m' (ForInStep δ)} {init : δ} : Std.HashMap.forIn f init m = forIn m.toArray init fun a b => f a.fst a.snd b`
- **foldM_eq_foldlM_keysArray**: `… {m : Std.HashMap α β} {δ : Type w} {m' : Type w → Type w'} [Monad m'] [LawfulMonad m'] {f : δ → α → m' δ} {init : δ} : Std.HashMap.foldM (fun d a x => f d a) init m = Array.foldlM f init m.keysArray`
- **fold_eq_foldl_keysArray**: `… {m : Std.HashMap α β} {δ : Type w} {f : δ → α → δ} {init : δ} : Std.HashMap.fold (fun d a x => f d a) init m = Array.foldl f init m.keysArray`
- **forM_eq_forM_keysArray**: `… {m : Std.HashMap α β} {m' : Type w → Type w'} [Monad m'] [LawfulMonad m'] {f : α → m' PUnit} : Std.HashMap.forM (fun a x => f a) m = Array.forM f m.keysArray`
- **forIn_eq_forIn_keysArray**: `… {m : Std.HashMap α β} {δ : Type w} {m' : Type w → Type w'} [Monad m'] [LawfulMonad m'] {f : α → δ → m' (ForInStep δ)} {init : δ} : Std.HashMap.forIn (fun a x d => f a d) init m = forIn m.keysArray init f`

#### HashMap.Lemmas: all / any (14)

_scope: section@34_

- **all_eq_not_any_not**: `… {m : Std.HashMap α β} {p : α → β → Bool} : m.all p = !m.any fun a b => !p a b`
- **any_eq_not_all_not**: `… {m : Std.HashMap α β} {p : α → β → Bool} : m.any p = !m.all fun a b => !p a b`
- **any_toList** [simp]: `… {m : Std.HashMap α β} {p : α → β → Bool} : (m.toList.any fun x => p x.fst x.snd) = m.any p`
- **any_eq_true_iff_exists_mem_getKey_getElem**: `… {m : Std.HashMap α β} [LawfulHashable α] [EquivBEq α] {p : α → β → Bool} : m.any p = true ↔ ∃ a h, p (m.getKey a h) m[a] = true`
- **any_eq_true_iff_exists_mem_getElem**: `… {m : Std.HashMap α β} [LawfulBEq α] {p : α → β → Bool} : m.any p = true ↔ ∃ a h, p a m[a] = true`
- **any_eq_false_iff_forall_mem_getKey_getElem**: `… {m : Std.HashMap α β} [LawfulHashable α] [EquivBEq α] {p : α → β → Bool} : m.any p = false ↔ ∀ (a : α) (h : a ∈ m), p (m.getKey a h) m[a] = false`
- **any_eq_false_iff_forall_mem_getElem**: `… {m : Std.HashMap α β} [LawfulBEq α] {p : α → β → Bool} : m.any p = false ↔ ∀ (a : α) (h : a ∈ m), p a m[a] = false`
- **all_toList** [simp]: `… {m : Std.HashMap α β} {p : α → β → Bool} : (m.toList.all fun x => p x.fst x.snd) = m.all p`
- **all_eq_true_iff_forall_mem_getKey_getElem**: `… {m : Std.HashMap α β} [EquivBEq α] [LawfulHashable α] {p : α → β → Bool} : m.all p = true ↔ ∀ (a : α) (h : a ∈ m), p (m.getKey a h) m[a] = true`
- **all_eq_true_iff_forall_mem_getElem**: `… {m : Std.HashMap α β} [LawfulBEq α] {p : α → β → Bool} : m.all p = true ↔ ∀ (a : α) (h : a ∈ m), p a m[a] = true`
- **all_eq_false_iff_exists_mem_getKey_getElem**: `… {m : Std.HashMap α β} [EquivBEq α] [LawfulHashable α] {p : α → β → Bool} : m.all p = false ↔ ∃ a h, p (m.getKey a h) m[a] = false`
- **all_eq_false_iff_exists_mem_getElem**: `… {m : Std.HashMap α β} [LawfulBEq α] {p : α → β → Bool} : m.all p = false ↔ ∃ a h, p a m[a] = false`
- **any_keys**: `… {m : Std.HashMap α β} [LawfulHashable α] [EquivBEq α] {p : α → Bool} : m.keys.any p = m.any fun a x => p a`
- **all_keys**: `… {m : Std.HashMap α β} [LawfulHashable α] [EquivBEq α] {p : α → Bool} : m.keys.all p = m.all fun a x => p a`

#### HashMap.Lemmas: insertMany (32)

_scope: section@34_

- **insertMany_nil** [simp, grind =, cbv_eval]: `… {m : Std.HashMap α β} : m.insertMany [] = m`
- **insertMany_list_singleton** [simp, grind =]: `… {m : Std.HashMap α β} {k : α} {v : β} : m.insertMany [(k, v)] = m.insert k v`
- **insertMany_cons** [grind _=_, cbv_eval]: `… {m : Std.HashMap α β} {l : List (α × β)} {k : α} {v : β} : m.insertMany ((k, v) :: l) = (m.insert k v).insertMany l`
- **insertMany_append** [grind _=_]: `… {m : Std.HashMap α β} {l₁ l₂ : List (α × β)} : m.insertMany (l₁ ++ l₂) = (m.insertMany l₁).insertMany l₂`
- **insertMany_ind** [elab_as_elim]: `… {ρ : Type w} [ForIn Id ρ (α × β)] {motive : Std.HashMap α β → Prop} (m : Std.HashMap α β) {l : ρ} (init : motive m) (insert : ∀ (m : Std.HashMap α β) (a : α) (b : β), motive m → motive (m.insert a b)) : motive (m.insertMany l)`
- **contains_insertMany_list** [simp, grind =]: `… {m : Std.HashMap α β} [EquivBEq α] [LawfulHashable α] {l : List (α × β)} {k : α} : (m.insertMany l).contains k = (m.contains k || (List.map Prod.fst l).contains k)`
- **mem_insertMany_list** [simp, grind =]: `… {m : Std.HashMap α β} [EquivBEq α] [LawfulHashable α] {l : List (α × β)} {k : α} : k ∈ m.insertMany l ↔ k ∈ m ∨ (List.map Prod.fst l).contains k = true`
- **mem_of_mem_insertMany_list**: `… {m : Std.HashMap α β} [EquivBEq α] [LawfulHashable α] {l : List (α × β)} {k : α} (mem : k ∈ m.insertMany l) (contains_eq_false : (List.map Prod.fst l).contains k = false) : k ∈ m`
- **mem_insertMany_of_mem**: `… {m : Std.HashMap α β} {ρ : Type w} [ForIn Id ρ (α × β)] [EquivBEq α] [LawfulHashable α] {l : ρ} {k : α} : k ∈ m → k ∈ m.insertMany l`
- **getElem?_insertMany_list_of_contains_eq_false**: `… {m : Std.HashMap α β} [EquivBEq α] [LawfulHashable α] {l : List (α × β)} {k : α} (contains_eq_false : (List.map Prod.fst l).contains k = false) : (m.insertMany l)[k]? = m[k]?`
- **getElem?_insertMany_list_of_mem**: `… {m : Std.HashMap α β} [EquivBEq α] [LawfulHashable α] {l : List (α × β)} {k k' : α} (k_beq : (k == k') = true) {v : β} (distinct : List.Pairwise (fun a b => (a.fst == b.fst) = false) l) (mem : (k, v) ∈ l) : (m.insertMany l)[k']? = some v`
- **getElem?_insertMany_list** [grind =]: `… {m : Std.HashMap α β} [EquivBEq α] [LawfulHashable α] {l : List (α × β)} {k : α} : (m.insertMany l)[k]? = (List.findSomeRev? (fun x => match x with | (a, b) => if (a == k) = true then some b else none) l).or m[k]?`
- **getElem_insertMany_list_of_contains_eq_false**: `… {m : Std.HashMap α β} [EquivBEq α] [LawfulHashable α] {l : List (α × β)} {k : α} (contains_eq_false : (List.map Prod.fst l).contains k = false) {h : k ∈ m.insertMany l} : (m.insertMany l)[k] = m[k]`
- **getElem_insertMany_list_of_mem**: `… {m : Std.HashMap α β} [EquivBEq α] [LawfulHashable α] {l : List (α × β)} {k k' : α} (k_beq : (k == k') = true) {v : β} (distinct : List.Pairwise (fun a b => (a.fst == b.fst) = false) l) (mem : (k, v) ∈ l) {h : k' ∈ m.insertMany l} : (m.insertMany l)[k'] = v`
- **getElem!_insertMany_list_of_contains_eq_false**: `… {m : Std.HashMap α β} [EquivBEq α] [LawfulHashable α] [Inhabited β] {l : List (α × β)} {k : α} (contains_eq_false : (List.map Prod.fst l).contains k = false) : (m.insertMany l)[k]! = m[k]!`
- **getElem!_insertMany_list_of_mem**: `… {m : Std.HashMap α β} [EquivBEq α] [LawfulHashable α] [Inhabited β] {l : List (α × β)} {k k' : α} (k_beq : (k == k') = true) {v : β} (distinct : List.Pairwise (fun a b => (a.fst == b.fst) = false) l) (mem : (k, v) ∈ l) : (m.insertMany l)[k']! = v`
- **getD_insertMany_list_of_contains_eq_false**: `… {m : Std.HashMap α β} [EquivBEq α] [LawfulHashable α] {l : List (α × β)} {k : α} {fallback : β} (contains_eq_false : (List.map Prod.fst l).contains k = false) : (m.insertMany l).getD k fallback = m.getD k fallback`
- **getD_insertMany_list_of_mem**: `… {m : Std.HashMap α β} [EquivBEq α] [LawfulHashable α] {l : List (α × β)} {k k' : α} (k_beq : (k == k') = true) {v fallback : β} (distinct : List.Pairwise (fun a b => (a.fst == b.fst) = false) l) (mem : (k, v) ∈ l) : (m.insertMany l).getD k' fallback = v`
- **getKey?_insertMany_list_of_contains_eq_false**: `… {m : Std.HashMap α β} [EquivBEq α] [LawfulHashable α] {l : List (α × β)} {k : α} (contains_eq_false : (List.map Prod.fst l).contains k = false) : (m.insertMany l).getKey? k = m.getKey? k`
- **getKey?_insertMany_list_of_mem**: `… {m : Std.HashMap α β} [EquivBEq α] [LawfulHashable α] {l : List (α × β)} {k k' : α} (k_beq : (k == k') = true) (distinct : List.Pairwise (fun a b => (a.fst == b.fst) = false) l) (mem : k ∈ List.map Prod.fst l) : (m.insertMany l).getKey? k' = some k`
- **getKey_insertMany_list_of_contains_eq_false**: `… {m : Std.HashMap α β} [EquivBEq α] [LawfulHashable α] {l : List (α × β)} {k : α} (contains_eq_false : (List.map Prod.fst l).contains k = false) {h : k ∈ m.insertMany l} : (m.insertMany l).getKey k h = m.getKey k ⋯`
- **getKey_insertMany_list_of_mem**: `… {m : Std.HashMap α β} [EquivBEq α] [LawfulHashable α] {l : List (α × β)} {k k' : α} (k_beq : (k == k') = true) (distinct : List.Pairwise (fun a b => (a.fst == b.fst) = false) l) (mem : k ∈ List.map Prod.fst l) {h : k' ∈ m.insertMany l} : (m.insertMany l).getKey k' h = k`
- **getKey!_insertMany_list_of_contains_eq_false**: `… {m : Std.HashMap α β} [EquivBEq α] [LawfulHashable α] [Inhabited α] {l : List (α × β)} {k : α} (contains_eq_false : (List.map Prod.fst l).contains k = false) : (m.insertMany l).getKey! k = m.getKey! k`
- **getKey!_insertMany_list_of_mem**: `… {m : Std.HashMap α β} [EquivBEq α] [LawfulHashable α] [Inhabited α] {l : List (α × β)} {k k' : α} (k_beq : (k == k') = true) (distinct : List.Pairwise (fun a b => (a.fst == b.fst) = false) l) (mem : k ∈ List.map Prod.fst l) : (m.insertMany l).getKey! k' = k`
- **getKeyD_insertMany_list_of_contains_eq_false**: `… {m : Std.HashMap α β} [EquivBEq α] [LawfulHashable α] {l : List (α × β)} {k fallback : α} (contains_eq_false : (List.map Prod.fst l).contains k = false) : (m.insertMany l).getKeyD k fallback = m.getKeyD k fallback`
- **getKeyD_insertMany_list_of_mem**: `… {m : Std.HashMap α β} [EquivBEq α] [LawfulHashable α] {l : List (α × β)} {k k' fallback : α} (k_beq : (k == k') = true) (distinct : List.Pairwise (fun a b => (a.fst == b.fst) = false) l) (mem : k ∈ List.map Prod.fst l) : (m.insertMany l).getKeyD k' fallback = k`
- **size_insertMany_list**: `… {m : Std.HashMap α β} [EquivBEq α] [LawfulHashable α] {l : List (α × β)} (distinct : List.Pairwise (fun a b => (a.fst == b.fst) = false) l) : (∀ (a : α), a ∈ m → (List.map Prod.fst l).contains a = false) → (m.insertMany l).size = m.size + l.length`
- **size_le_size_insertMany_list**: `… {m : Std.HashMap α β} [EquivBEq α] [LawfulHashable α] {l : List (α × β)} : m.size ≤ (m.insertMany l).size`
- **size_le_size_insertMany** [grind_pattern (insertMany m l).size (l.1377)]: `… {m : Std.HashMap α β} {ρ : Type w} [ForIn Id ρ (α × β)] [EquivBEq α] [LawfulHashable α] {l : ρ} : m.size ≤ (m.insertMany l).size`
- **size_insertMany_list_le** [grind_pattern (insertMany m l).size (l.1384)]: `… {m : Std.HashMap α β} [EquivBEq α] [LawfulHashable α] {l : List (α × β)} : (m.insertMany l).size ≤ m.size + l.length`
- **isEmpty_insertMany_list** [simp, grind =]: `… {m : Std.HashMap α β} [EquivBEq α] [LawfulHashable α] {l : List (α × β)} : (m.insertMany l).isEmpty = (m.isEmpty && l.isEmpty)`
- **isEmpty_of_isEmpty_insertMany**: `… {m : Std.HashMap α β} {ρ : Type w} [ForIn Id ρ (α × β)] [EquivBEq α] [LawfulHashable α] {l : ρ} : (m.insertMany l).isEmpty = true → m.isEmpty = true`

#### HashMap.Lemmas: BEq vs Equiv (4)

_scope: section@34 › section@1396_

- **Equiv.beq**: `… {β : Type v} {m₁ m₂ : Std.HashMap α β} [BEq β] [EquivBEq α] [LawfulHashable α] [ReflBEq β] (h : m₁.Equiv m₂) : (m₁ == m₂) = true`
- **equiv_of_beq**: `… {β : Type v} {m₁ m₂ : Std.HashMap α β} [BEq β] [LawfulBEq α] [LawfulBEq β] (h : (m₁ == m₂) = true) : m₁.Equiv m₂`
- **beq_iff_equiv**: `… {β : Type v} {m₁ m₂ : Std.HashMap α β} [BEq β] [LawfulBEq α] [LawfulBEq β] : (m₁ == m₂) = true ↔ m₁.Equiv m₂`
- **Equiv.beq_congr**: `… {β : Type v} {m₁ m₂ : Std.HashMap α β} [BEq β] [EquivBEq α] [LawfulHashable α] {m₃ m₄ : Std.HashMap α β} (w₁ : m₁.Equiv m₃) (w₂ : m₂.Equiv m₄) : (m₁ == m₂) = (m₃ == m₄)`

#### HashMap.Lemmas: Union (41)

_scope: section@34 › section Union_; subheadings: contains (1), mem (5), Equiv (5), getElem? (3), getElem (3), getD (3), getElem! (3), getKey? (3), getKey (3), getKeyD (3), getKey! (3), size (4), isEmpty (1)

- **union_eq** [simp]: `… {β : Type v} {m₁ m₂ : Std.HashMap α β} : m₁.union m₂ = m₁ ∪ m₂`
- **contains_union** [simp] {contains}: `… {β : Type v} {m₁ m₂ : Std.HashMap α β} [EquivBEq α] [LawfulHashable α] {k : α} : (m₁ ∪ m₂).contains k = (m₁.contains k || m₂.contains k)`
- **mem_union_of_left** {mem}: `… {β : Type v} {m₁ m₂ : Std.HashMap α β} [EquivBEq α] [LawfulHashable α] {k : α} : k ∈ m₁ → k ∈ m₁ ∪ m₂`
- **mem_union_of_right** {mem}: `… {β : Type v} {m₁ m₂ : Std.HashMap α β} [EquivBEq α] [LawfulHashable α] {k : α} : k ∈ m₂ → k ∈ m₁ ∪ m₂`
- **mem_union_iff** [simp] {mem}: `… {β : Type v} {m₁ m₂ : Std.HashMap α β} [EquivBEq α] [LawfulHashable α] {k : α} : k ∈ m₁ ∪ m₂ ↔ k ∈ m₁ ∨ k ∈ m₂`
- **mem_of_mem_union_of_not_mem_right** {mem}: `… {β : Type v} {m₁ m₂ : Std.HashMap α β} [EquivBEq α] [LawfulHashable α] {k : α} : k ∈ m₁ ∪ m₂ → ¬k ∈ m₂ → k ∈ m₁`
- **mem_of_mem_union_of_not_mem_left** {mem}: `… {β : Type v} {m₁ m₂ : Std.HashMap α β} [EquivBEq α] [LawfulHashable α] {k : α} : k ∈ m₁ ∪ m₂ → ¬k ∈ m₁ → k ∈ m₂`
- **Equiv.union_left** {Equiv}: `… {β : Type v} {m₁ m₂ m₃ : Std.HashMap α β} [EquivBEq α] [LawfulHashable α] (equiv : m₁.Equiv m₂) : (m₁ ∪ m₃).Equiv (m₂ ∪ m₃)`
- **Equiv.union_right** {Equiv}: `… {β : Type v} {m₁ m₂ m₃ : Std.HashMap α β} [EquivBEq α] [LawfulHashable α] (equiv : m₂.Equiv m₃) : (m₁ ∪ m₂).Equiv (m₁ ∪ m₃)`
- **Equiv.union_congr** {Equiv}: `… {β : Type v} {m₁ m₂ m₃ m₄ : Std.HashMap α β} [EquivBEq α] [LawfulHashable α] (equiv₁ : m₁.Equiv m₃) (equiv₂ : m₂.Equiv m₄) : (m₁ ∪ m₂).Equiv (m₃ ∪ m₄)`
- **union_insert_right_equiv_insert_union** {Equiv}: `… {β : Type v} {m₁ m₂ : Std.HashMap α β} [EquivBEq α] [LawfulHashable α] {p : α × β} : (m₁ ∪ m₂.insert p.fst p.snd).Equiv ((m₁ ∪ m₂).insert p.fst p.snd)`
- **union_insert_right_equiv_union_insert** [deprecated union_insert_right_equiv_insert_union (since := "2025-11-03"), DEPRECATED→union_insert_right_equiv_insert_union] {Equiv}: `… {β : Type v} {m₁ m₂ : Std.HashMap α β} [EquivBEq α] [LawfulHashable α] {p : α × β} : (m₁ ∪ m₂.insert p.fst p.snd).Equiv ((m₁ ∪ m₂).insert p.fst p.snd)`
- **getElem?_union** {getElem?}: `… {β : Type v} {m₁ m₂ : Std.HashMap α β} [EquivBEq α] [LawfulHashable α] {k : α} : (m₁ ∪ m₂)[k]? = m₂[k]?.or m₁[k]?`
- **getElem?_union_of_not_mem_left** {getElem?}: `… {β : Type v} {m₁ m₂ : Std.HashMap α β} [EquivBEq α] [LawfulHashable α] {k : α} (not_mem : ¬k ∈ m₁) : (m₁ ∪ m₂)[k]? = m₂[k]?`
- **getElem?_union_of_not_mem_right** {getElem?}: `… {β : Type v} {m₁ m₂ : Std.HashMap α β} [EquivBEq α] [LawfulHashable α] {k : α} (not_mem : ¬k ∈ m₂) : (m₁ ∪ m₂)[k]? = m₁[k]?`
- **getElem_union_of_mem_right** {getElem}: `… {β : Type v} {m₁ m₂ : Std.HashMap α β} [EquivBEq α] [LawfulHashable α] {k : α} (contains_right : k ∈ m₂) : (m₁ ∪ m₂)[k] = m₂[k]`
- **getElem_union_of_not_mem_left** {getElem}: `… {β : Type v} {m₁ m₂ : Std.HashMap α β} [EquivBEq α] [LawfulHashable α] {k : α} (not_mem : ¬k ∈ m₁) {h' : k ∈ m₁ ∪ m₂} : (m₁ ∪ m₂)[k] = m₂[k]`
- **getElem_union_of_not_mem_right** {getElem}: `… {β : Type v} {m₁ m₂ : Std.HashMap α β} [EquivBEq α] [LawfulHashable α] {k : α} (not_mem : ¬k ∈ m₂) {h' : k ∈ m₁ ∪ m₂} : (m₁ ∪ m₂)[k] = m₁[k]`
- **getD_union** {getD}: `… {β : Type v} {m₁ m₂ : Std.HashMap α β} [EquivBEq α] [LawfulHashable α] {k : α} {fallback : β} : (m₁ ∪ m₂).getD k fallback = m₂.getD k (m₁.getD k fallback)`
- **getD_union_of_not_mem_left** {getD}: `… {β : Type v} {m₁ m₂ : Std.HashMap α β} [EquivBEq α] [LawfulHashable α] {k : α} {fallback : β} (not_mem : ¬k ∈ m₁) : (m₁ ∪ m₂).getD k fallback = m₂.getD k fallback`
- **getD_union_of_not_mem_right** {getD}: `… {β : Type v} {m₁ m₂ : Std.HashMap α β} [EquivBEq α] [LawfulHashable α] {k : α} {fallback : β} (not_mem : ¬k ∈ m₂) : (m₁ ∪ m₂).getD k fallback = m₁.getD k fallback`
- **getElem!_union** {getElem!}: `… {β : Type v} {m₁ m₂ : Std.HashMap α β} [EquivBEq α] [LawfulHashable α] {k : α} [Inhabited β] : (m₁ ∪ m₂)[k]! = m₂.getD k m₁[k]!`
- **getElem!_union_of_not_mem_left** {getElem!}: `… {β : Type v} {m₁ m₂ : Std.HashMap α β} [EquivBEq α] [LawfulHashable α] {k : α} [Inhabited β] (not_mem : ¬k ∈ m₁) : (m₁ ∪ m₂)[k]! = m₂[k]!`
- **getElem!_union_of_not_mem_right** {getElem!}: `… {β : Type v} {m₁ m₂ : Std.HashMap α β} [EquivBEq α] [LawfulHashable α] {k : α} [Inhabited β] (not_mem : ¬k ∈ m₂) : (m₁ ∪ m₂)[k]! = m₁[k]!`
- **getKey?_union** {getKey?}: `… {β : Type v} {m₁ m₂ : Std.HashMap α β} [EquivBEq α] [LawfulHashable α] {k : α} : (m₁ ∪ m₂).getKey? k = (m₂.getKey? k).or (m₁.getKey? k)`
- **getKey?_union_of_not_mem_left** {getKey?}: `… {β : Type v} {m₁ m₂ : Std.HashMap α β} [EquivBEq α] [LawfulHashable α] {k : α} (not_mem : ¬k ∈ m₁) : (m₁ ∪ m₂).getKey? k = m₂.getKey? k`
- **getKey?_union_of_not_mem_right** {getKey?}: `… {β : Type v} {m₁ m₂ : Std.HashMap α β} [EquivBEq α] [LawfulHashable α] {k : α} (not_mem : ¬k ∈ m₂) : (m₁ ∪ m₂).getKey? k = m₁.getKey? k`
- **getKey_union_of_mem_right** {getKey}: `… {β : Type v} {m₁ m₂ : Std.HashMap α β} [EquivBEq α] [LawfulHashable α] {k : α} (mem : k ∈ m₂) : (m₁ ∪ m₂).getKey k ⋯ = m₂.getKey k mem`
- **getKey_union_of_not_mem_left** {getKey}: `… {β : Type v} {m₁ m₂ : Std.HashMap α β} [EquivBEq α] [LawfulHashable α] {k : α} (not_mem : ¬k ∈ m₁) {h' : k ∈ m₁ ∪ m₂} : (m₁ ∪ m₂).getKey k h' = m₂.getKey k ⋯`
- **getKey_union_of_not_mem_right** {getKey}: `… {β : Type v} {m₁ m₂ : Std.HashMap α β} [EquivBEq α] [LawfulHashable α] {k : α} (not_mem : ¬k ∈ m₂) {h' : k ∈ m₁ ∪ m₂} : (m₁ ∪ m₂).getKey k h' = m₁.getKey k ⋯`
- **getKeyD_union** {getKeyD}: `… {β : Type v} {m₁ m₂ : Std.HashMap α β} [EquivBEq α] [LawfulHashable α] {k fallback : α} : (m₁ ∪ m₂).getKeyD k fallback = m₂.getKeyD k (m₁.getKeyD k fallback)`
- **getKeyD_union_of_not_mem_left** {getKeyD}: `… {β : Type v} {m₁ m₂ : Std.HashMap α β} [EquivBEq α] [LawfulHashable α] {k fallback : α} (mem : ¬k ∈ m₁) : (m₁ ∪ m₂).getKeyD k fallback = m₂.getKeyD k fallback`
- **getKeyD_union_of_not_mem_right** {getKeyD}: `… {β : Type v} {m₁ m₂ : Std.HashMap α β} [EquivBEq α] [LawfulHashable α] {k fallback : α} (mem : ¬k ∈ m₂) : (m₁ ∪ m₂).getKeyD k fallback = m₁.getKeyD k fallback`
- **getKey!_union** {getKey!}: `… {β : Type v} {m₁ m₂ : Std.HashMap α β} [EquivBEq α] [LawfulHashable α] [Inhabited α] {k : α} : (m₁ ∪ m₂).getKey! k = m₂.getKeyD k (m₁.getKey! k)`
- **getKey!_union_of_not_mem_left** {getKey!}: `… {β : Type v} {m₁ m₂ : Std.HashMap α β} [Inhabited α] [EquivBEq α] [LawfulHashable α] {k : α} (mem : ¬k ∈ m₁) : (m₁ ∪ m₂).getKey! k = m₂.getKey! k`
- **getKey!_union_of_not_mem_right** {getKey!}: `… {β : Type v} {m₁ m₂ : Std.HashMap α β} [Inhabited α] [EquivBEq α] [LawfulHashable α] {k : α} (mem : ¬k ∈ m₂) : (m₁ ∪ m₂).getKey! k = m₁.getKey! k`
- **size_union_of_not_mem** {size}: `… {β : Type v} {m₁ m₂ : Std.HashMap α β} [EquivBEq α] [LawfulHashable α] : (∀ (a : α), a ∈ m₁ → ¬a ∈ m₂) → (m₁ ∪ m₂).size = m₁.size + m₂.size`
- **size_left_le_size_union** {size}: `… {β : Type v} {m₁ m₂ : Std.HashMap α β} [EquivBEq α] [LawfulHashable α] : m₁.size ≤ (m₁ ∪ m₂).size`
- **size_right_le_size_union** {size}: `… {β : Type v} {m₁ m₂ : Std.HashMap α β} [EquivBEq α] [LawfulHashable α] : m₂.size ≤ (m₁ ∪ m₂).size`
- **size_union_le_size_add_size** {size}: `… {β : Type v} {m₁ m₂ : Std.HashMap α β} [EquivBEq α] [LawfulHashable α] : (m₁ ∪ m₂).size ≤ m₁.size + m₂.size`
- **isEmpty_union** [simp] {isEmpty}: `… {β : Type v} {m₁ m₂ : Std.HashMap α β} [EquivBEq α] [LawfulHashable α] : (m₁ ∪ m₂).isEmpty = (m₁.isEmpty && m₂.isEmpty)`

#### HashMap.Lemmas: Inter (43)

_scope: section@34 › section Inter_; subheadings: contains (1), mem (3), Equiv (3), getElem? (4), getElem (1), getD (4), getElem! (4), getKey? (4), getKey (1), getKeyD (4), getKey! (4), size (5), isEmpty (4)

- **inter_eq** [simp]: `… {β : Type v} {m₁ m₂ : Std.HashMap α β} : m₁.inter m₂ = m₁ ∩ m₂`
- **contains_inter** [simp] {contains}: `… {β : Type v} {m₁ m₂ : Std.HashMap α β} [EquivBEq α] [LawfulHashable α] {k : α} : (m₁ ∩ m₂).contains k = (m₁.contains k && m₂.contains k)`
- **mem_inter_iff** [simp] {mem}: `… {β : Type v} {m₁ m₂ : Std.HashMap α β} [EquivBEq α] [LawfulHashable α] {k : α} : k ∈ m₁ ∩ m₂ ↔ k ∈ m₁ ∧ k ∈ m₂`
- **not_mem_inter_of_not_mem_left** {mem}: `… {β : Type v} {m₁ m₂ : Std.HashMap α β} [EquivBEq α] [LawfulHashable α] {k : α} (not_mem : ¬k ∈ m₁) : ¬k ∈ m₁ ∩ m₂`
- **not_mem_inter_of_not_mem_right** {mem}: `… {β : Type v} {m₁ m₂ : Std.HashMap α β} [EquivBEq α] [LawfulHashable α] {k : α} (not_mem : ¬k ∈ m₂) : ¬k ∈ m₁ ∩ m₂`
- **Equiv.inter_left** {Equiv}: `… {β : Type v} {m₁ m₂ m₃ : Std.HashMap α β} [EquivBEq α] [LawfulHashable α] (equiv : m₁.Equiv m₂) : (m₁ ∩ m₃).Equiv (m₂ ∩ m₃)`
- **Equiv.inter_right** {Equiv}: `… {β : Type v} {m₁ m₂ m₃ : Std.HashMap α β} [EquivBEq α] [LawfulHashable α] (equiv : m₂.Equiv m₃) : (m₁ ∩ m₂).Equiv (m₁ ∩ m₃)`
- **Equiv.inter_congr** {Equiv}: `… {β : Type v} {m₁ m₂ m₃ m₄ : Std.HashMap α β} [EquivBEq α] [LawfulHashable α] (equiv₁ : m₁.Equiv m₃) (equiv₂ : m₂.Equiv m₄) : (m₁ ∩ m₂).Equiv (m₃ ∩ m₄)`
- **getElem?_inter** {getElem?}: `… {β : Type v} {m₁ m₂ : Std.HashMap α β} [EquivBEq α] [LawfulHashable α] {k : α} : (m₁ ∩ m₂)[k]? = if k ∈ m₂ then m₁[k]? else none`
- **getElem?_inter_of_mem_right** {getElem?}: `… {β : Type v} {m₁ m₂ : Std.HashMap α β} [EquivBEq α] [LawfulHashable α] {k : α} (mem : k ∈ m₂) : (m₁ ∩ m₂)[k]? = m₁[k]?`
- **getElem?_inter_of_not_mem_left** {getElem?}: `… {β : Type v} {m₁ m₂ : Std.HashMap α β} [EquivBEq α] [LawfulHashable α] {k : α} (not_mem : ¬k ∈ m₁) : (m₁ ∩ m₂)[k]? = none`
- **getElem?_inter_of_not_mem_right** {getElem?}: `… {β : Type v} {m₁ m₂ : Std.HashMap α β} [EquivBEq α] [LawfulHashable α] {k : α} (not_mem : ¬k ∈ m₂) : (m₁ ∩ m₂)[k]? = none`
- **getElem_inter** [simp] {getElem}: `… {β : Type v} {m₁ m₂ : Std.HashMap α β} [EquivBEq α] [LawfulHashable α] {k : α} {h_mem : k ∈ m₁ ∩ m₂} : (m₁ ∩ m₂)[k] = m₁[k]`
- **getD_inter** {getD}: `… {β : Type v} {m₁ m₂ : Std.HashMap α β} [EquivBEq α] [LawfulHashable α] {k : α} {fallback : β} : (m₁ ∩ m₂).getD k fallback = if k ∈ m₂ then m₁.getD k fallback else fallback`
- **getD_inter_of_mem_right** {getD}: `… {β : Type v} {m₁ m₂ : Std.HashMap α β} [EquivBEq α] [LawfulHashable α] {k : α} {fallback : β} (mem : k ∈ m₂) : (m₁ ∩ m₂).getD k fallback = m₁.getD k fallback`
- **getD_inter_of_not_mem_right** {getD}: `… {β : Type v} {m₁ m₂ : Std.HashMap α β} [EquivBEq α] [LawfulHashable α] {k : α} {fallback : β} (not_mem : ¬k ∈ m₂) : (m₁ ∩ m₂).getD k fallback = fallback`
- **getD_inter_of_not_mem_left** {getD}: `… {β : Type v} {m₁ m₂ : Std.HashMap α β} [EquivBEq α] [LawfulHashable α] {k : α} {fallback : β} (not_mem : ¬k ∈ m₁) : (m₁ ∩ m₂).getD k fallback = fallback`
- **getElem!_inter** {getElem!}: `… {β : Type v} {m₁ m₂ : Std.HashMap α β} [EquivBEq α] [LawfulHashable α] {k : α} [Inhabited β] : (m₁ ∩ m₂)[k]! = if k ∈ m₂ then m₁[k]! else default`
- **getElem!_inter_of_mem_right** {getElem!}: `… {β : Type v} {m₁ m₂ : Std.HashMap α β} [EquivBEq α] [LawfulHashable α] {k : α} [Inhabited β] (mem : k ∈ m₂) : (m₁ ∩ m₂)[k]! = m₁[k]!`
- **getElem!_inter_of_not_mem_right** {getElem!}: `… {β : Type v} {m₁ m₂ : Std.HashMap α β} [EquivBEq α] [LawfulHashable α] {k : α} [Inhabited β] (not_mem : ¬k ∈ m₂) : (m₁ ∩ m₂)[k]! = default`
- **getElem!_inter_of_not_mem_left** {getElem!}: `… {β : Type v} {m₁ m₂ : Std.HashMap α β} [EquivBEq α] [LawfulHashable α] {k : α} [Inhabited β] (not_mem : ¬k ∈ m₁) : (m₁ ∩ m₂)[k]! = default`
- **getKey?_inter** {getKey?}: `… {β : Type v} {m₁ m₂ : Std.HashMap α β} [EquivBEq α] [LawfulHashable α] {k : α} : (m₁ ∩ m₂).getKey? k = if k ∈ m₂ then m₁.getKey? k else none`
- **getKey?_inter_of_mem_right** {getKey?}: `… {β : Type v} {m₁ m₂ : Std.HashMap α β} [EquivBEq α] [LawfulHashable α] {k : α} (mem : k ∈ m₂) : (m₁ ∩ m₂).getKey? k = m₁.getKey? k`
- **getKey?_inter_of_not_mem_right** {getKey?}: `… {β : Type v} {m₁ m₂ : Std.HashMap α β} [EquivBEq α] [LawfulHashable α] {k : α} (not_mem : ¬k ∈ m₂) : (m₁ ∩ m₂).getKey? k = none`
- **getKey?_inter_of_not_mem_left** {getKey?}: `… {β : Type v} {m₁ m₂ : Std.HashMap α β} [EquivBEq α] [LawfulHashable α] {k : α} (not_mem : ¬k ∈ m₁) : (m₁ ∩ m₂).getKey? k = none`
- **getKey_inter** [simp] {getKey}: `… {β : Type v} {m₁ m₂ : Std.HashMap α β} [EquivBEq α] [LawfulHashable α] {k : α} {h_mem : k ∈ m₁ ∩ m₂} : (m₁ ∩ m₂).getKey k h_mem = m₁.getKey k ⋯`
- **getKeyD_inter** {getKeyD}: `… {β : Type v} {m₁ m₂ : Std.HashMap α β} [EquivBEq α] [LawfulHashable α] {k fallback : α} : (m₁ ∩ m₂).getKeyD k fallback = if k ∈ m₂ then m₁.getKeyD k fallback else fallback`
- **getKeyD_inter_of_mem_right** {getKeyD}: `… {β : Type v} {m₁ m₂ : Std.HashMap α β} [EquivBEq α] [LawfulHashable α] {k fallback : α} (mem : k ∈ m₂) : (m₁ ∩ m₂).getKeyD k fallback = m₁.getKeyD k fallback`
- **getKeyD_inter_of_not_mem_right** {getKeyD}: `… {β : Type v} {m₁ m₂ : Std.HashMap α β} [EquivBEq α] [LawfulHashable α] {k fallback : α} (not_mem : ¬k ∈ m₂) : (m₁ ∩ m₂).getKeyD k fallback = fallback`
- **getKeyD_inter_of_not_mem_left** {getKeyD}: `… {β : Type v} {m₁ m₂ : Std.HashMap α β} [EquivBEq α] [LawfulHashable α] {k fallback : α} (not_mem : ¬k ∈ m₁) : (m₁ ∩ m₂).getKeyD k fallback = fallback`
- **getKey!_inter** {getKey!}: `… {β : Type v} {m₁ m₂ : Std.HashMap α β} [EquivBEq α] [LawfulHashable α] [Inhabited α] {k : α} : (m₁ ∩ m₂).getKey! k = if k ∈ m₂ then m₁.getKey! k else default`
- **getKey!_inter_of_mem_right** {getKey!}: `… {β : Type v} {m₁ m₂ : Std.HashMap α β} [EquivBEq α] [LawfulHashable α] [Inhabited α] {k : α} (mem : k ∈ m₂) : (m₁ ∩ m₂).getKey! k = m₁.getKey! k`
- **getKey!_inter_of_not_mem_right** {getKey!}: `… {β : Type v} {m₁ m₂ : Std.HashMap α β} [EquivBEq α] [LawfulHashable α] [Inhabited α] {k : α} (not_mem : ¬k ∈ m₂) : (m₁ ∩ m₂).getKey! k = default`
- **getKey!_inter_of_not_mem_left** {getKey!}: `… {β : Type v} {m₁ m₂ : Std.HashMap α β} [EquivBEq α] [LawfulHashable α] [Inhabited α] {k : α} (not_mem : ¬k ∈ m₁) : (m₁ ∩ m₂).getKey! k = default`
- **size_inter_le_size_left** {size}: `… {β : Type v} {m₁ m₂ : Std.HashMap α β} [EquivBEq α] [LawfulHashable α] : (m₁ ∩ m₂).size ≤ m₁.size`
- **size_inter_le_size_right** {size}: `… {β : Type v} {m₁ m₂ : Std.HashMap α β} [EquivBEq α] [LawfulHashable α] : (m₁ ∩ m₂).size ≤ m₂.size`
- **size_inter_eq_size_left** {size}: `… {β : Type v} {m₁ m₂ : Std.HashMap α β} [EquivBEq α] [LawfulHashable α] (h : ∀ (a : α), a ∈ m₁ → a ∈ m₂) : (m₁ ∩ m₂).size = m₁.size`
- **size_inter_eq_size_right** {size}: `… {β : Type v} {m₁ m₂ : Std.HashMap α β} [EquivBEq α] [LawfulHashable α] (h : ∀ (a : α), a ∈ m₂ → a ∈ m₁) : (m₁ ∩ m₂).size = m₂.size`
- **size_add_size_eq_size_union_add_size_inter** {size}: `… {β : Type v} {m₁ m₂ : Std.HashMap α β} [EquivBEq α] [LawfulHashable α] : m₁.size + m₂.size = (m₁ ∪ m₂).size + (m₁ ∩ m₂).size`
- **isEmpty_inter_left** [simp] {isEmpty}: `… {β : Type v} {m₁ m₂ : Std.HashMap α β} [EquivBEq α] [LawfulHashable α] (h : m₁.isEmpty = true) : (m₁ ∩ m₂).isEmpty = true`
- **isEmpty_inter_right** [simp] {isEmpty}: `… {β : Type v} {m₁ m₂ : Std.HashMap α β} [EquivBEq α] [LawfulHashable α] (h : m₂.isEmpty = true) : (m₁ ∩ m₂).isEmpty = true`
- **isEmpty_inter_iff** {isEmpty}: `… {β : Type v} {m₁ m₂ : Std.HashMap α β} [EquivBEq α] [LawfulHashable α] : (m₁ ∩ m₂).isEmpty = true ↔ ∀ (k : α), k ∈ m₁ → ¬k ∈ m₂`
- **isEmpty_inter_comm** {isEmpty}: `… {β : Type v} {m₁ m₂ : Std.HashMap α β} [EquivBEq α] [LawfulHashable α] : (m₁ ∩ m₂).isEmpty = (m₂ ∩ m₁).isEmpty`

#### HashMap.Lemmas: Diff (39)

_scope: section@34 › section Diff_; subheadings: contains (1), mem (3), getElem? (4), Equiv (3), getElem (1), getD (4), getElem! (4), getKey? (4), getKey (1), getKeyD (4), getKey! (4), size (3), isEmpty (2)

- **diff_eq** [simp]: `… {β : Type v} {m₁ m₂ : Std.HashMap α β} : m₁.diff m₂ = m₁ \ m₂`
- **contains_diff** [simp] {contains}: `… {β : Type v} {m₁ m₂ : Std.HashMap α β} [EquivBEq α] [LawfulHashable α] {k : α} : (m₁ \ m₂).contains k = (m₁.contains k && !m₂.contains k)`
- **mem_diff_iff** [simp] {mem}: `… {β : Type v} {m₁ m₂ : Std.HashMap α β} [EquivBEq α] [LawfulHashable α] {k : α} : k ∈ m₁ \ m₂ ↔ k ∈ m₁ ∧ ¬k ∈ m₂`
- **not_mem_diff_of_not_mem_left** {mem}: `… {β : Type v} {m₁ m₂ : Std.HashMap α β} [EquivBEq α] [LawfulHashable α] {k : α} (not_mem : ¬k ∈ m₁) : ¬k ∈ m₁ \ m₂`
- **not_mem_diff_of_mem_right** {mem}: `… {β : Type v} {m₁ m₂ : Std.HashMap α β} [EquivBEq α] [LawfulHashable α] {k : α} (mem : k ∈ m₂) : ¬k ∈ m₁ \ m₂`
- **getElem?_diff** {getElem?}: `… {β : Type v} {m₁ m₂ : Std.HashMap α β} [EquivBEq α] [LawfulHashable α] {k : α} : (m₁ \ m₂)[k]? = if k ∈ m₂ then none else m₁[k]?`
- **getElem?_diff_of_not_mem_right** {getElem?}: `… {β : Type v} {m₁ m₂ : Std.HashMap α β} [EquivBEq α] [LawfulHashable α] {k : α} (not_mem : ¬k ∈ m₂) : (m₁ \ m₂)[k]? = m₁[k]?`
- **getElem?_diff_of_not_mem_left** {getElem?}: `… {β : Type v} {m₁ m₂ : Std.HashMap α β} [EquivBEq α] [LawfulHashable α] {k : α} (not_mem : ¬k ∈ m₁) : (m₁ \ m₂)[k]? = none`
- **getElem?_diff_of_mem_right** {getElem?}: `… {β : Type v} {m₁ m₂ : Std.HashMap α β} [EquivBEq α] [LawfulHashable α] {k : α} (mem : k ∈ m₂) : (m₁ \ m₂)[k]? = none`
- **Equiv.diff_left** {Equiv}: `… {β : Type v} {m₁ m₂ m₃ : Std.HashMap α β} [EquivBEq α] [LawfulHashable α] (equiv : m₁.Equiv m₂) : (m₁ \ m₃).Equiv (m₂ \ m₃)`
- **Equiv.diff_right** {Equiv}: `… {β : Type v} {m₁ m₂ m₃ : Std.HashMap α β} [EquivBEq α] [LawfulHashable α] (equiv : m₂.Equiv m₃) : (m₁ \ m₂).Equiv (m₁ \ m₃)`
- **Equiv.diff_congr** {Equiv}: `… {β : Type v} {m₁ m₂ m₃ m₄ : Std.HashMap α β} [EquivBEq α] [LawfulHashable α] (equiv₁ : m₁.Equiv m₃) (equiv₂ : m₂.Equiv m₄) : (m₁ \ m₂).Equiv (m₃ \ m₄)`
- **getElem_diff** [simp] {getElem}: `… {β : Type v} {m₁ m₂ : Std.HashMap α β} [EquivBEq α] [LawfulHashable α] {k : α} {h_mem : k ∈ m₁ \ m₂} : (m₁ \ m₂)[k] = m₁[k]`
- **getD_diff** {getD}: `… {β : Type v} {m₁ m₂ : Std.HashMap α β} [EquivBEq α] [LawfulHashable α] {k : α} {fallback : β} : (m₁ \ m₂).getD k fallback = if k ∈ m₂ then fallback else m₁.getD k fallback`
- **getD_diff_of_not_mem_right** {getD}: `… {β : Type v} {m₁ m₂ : Std.HashMap α β} [EquivBEq α] [LawfulHashable α] {k : α} {fallback : β} (not_mem : ¬k ∈ m₂) : (m₁ \ m₂).getD k fallback = m₁.getD k fallback`
- **getD_diff_of_mem_right** {getD}: `… {β : Type v} {m₁ m₂ : Std.HashMap α β} [EquivBEq α] [LawfulHashable α] {k : α} {fallback : β} (mem : k ∈ m₂) : (m₁ \ m₂).getD k fallback = fallback`
- **getD_diff_of_not_mem_left** {getD}: `… {β : Type v} {m₁ m₂ : Std.HashMap α β} [EquivBEq α] [LawfulHashable α] {k : α} {fallback : β} (not_mem : ¬k ∈ m₁) : (m₁ \ m₂).getD k fallback = fallback`
- **getElem!_diff** {getElem!}: `… {β : Type v} {m₁ m₂ : Std.HashMap α β} [EquivBEq α] [LawfulHashable α] {k : α} [Inhabited β] : (m₁ \ m₂)[k]! = if k ∈ m₂ then default else m₁[k]!`
- **getElem!_diff_of_not_mem_right** {getElem!}: `… {β : Type v} {m₁ m₂ : Std.HashMap α β} [EquivBEq α] [LawfulHashable α] {k : α} [Inhabited β] (not_mem : ¬k ∈ m₂) : (m₁ \ m₂)[k]! = m₁[k]!`
- **getElem!_diff_of_mem_right** {getElem!}: `… {β : Type v} {m₁ m₂ : Std.HashMap α β} [EquivBEq α] [LawfulHashable α] {k : α} [Inhabited β] (mem : k ∈ m₂) : (m₁ \ m₂)[k]! = default`
- **getElem!_diff_of_not_mem_left** {getElem!}: `… {β : Type v} {m₁ m₂ : Std.HashMap α β} [EquivBEq α] [LawfulHashable α] {k : α} [Inhabited β] (not_mem : ¬k ∈ m₁) : (m₁ \ m₂)[k]! = default`
- **getKey?_diff** {getKey?}: `… {β : Type v} {m₁ m₂ : Std.HashMap α β} [EquivBEq α] [LawfulHashable α] {k : α} : (m₁ \ m₂).getKey? k = if k ∈ m₂ then none else m₁.getKey? k`
- **getKey?_diff_of_not_mem_right** {getKey?}: `… {β : Type v} {m₁ m₂ : Std.HashMap α β} [EquivBEq α] [LawfulHashable α] {k : α} (not_mem : ¬k ∈ m₂) : (m₁ \ m₂).getKey? k = m₁.getKey? k`
- **getKey?_diff_of_not_mem_left** {getKey?}: `… {β : Type v} {m₁ m₂ : Std.HashMap α β} [EquivBEq α] [LawfulHashable α] {k : α} (not_mem : ¬k ∈ m₁) : (m₁ \ m₂).getKey? k = none`
- **getKey?_diff_of_mem_right** {getKey?}: `… {β : Type v} {m₁ m₂ : Std.HashMap α β} [EquivBEq α] [LawfulHashable α] {k : α} (mem : k ∈ m₂) : (m₁ \ m₂).getKey? k = none`
- **getKey_diff** [simp] {getKey}: `… {β : Type v} {m₁ m₂ : Std.HashMap α β} [EquivBEq α] [LawfulHashable α] {k : α} {h_mem : k ∈ m₁ \ m₂} : (m₁ \ m₂).getKey k h_mem = m₁.getKey k ⋯`
- **getKeyD_diff** {getKeyD}: `… {β : Type v} {m₁ m₂ : Std.HashMap α β} [EquivBEq α] [LawfulHashable α] {k fallback : α} : (m₁ \ m₂).getKeyD k fallback = if k ∈ m₂ then fallback else m₁.getKeyD k fallback`
- **getKeyD_diff_of_not_mem_right** {getKeyD}: `… {β : Type v} {m₁ m₂ : Std.HashMap α β} [EquivBEq α] [LawfulHashable α] {k fallback : α} (not_mem : ¬k ∈ m₂) : (m₁ \ m₂).getKeyD k fallback = m₁.getKeyD k fallback`
- **getKeyD_diff_of_mem_right** {getKeyD}: `… {β : Type v} {m₁ m₂ : Std.HashMap α β} [EquivBEq α] [LawfulHashable α] {k fallback : α} (mem : k ∈ m₂) : (m₁ \ m₂).getKeyD k fallback = fallback`
- **getKeyD_diff_of_not_mem_left** {getKeyD}: `… {β : Type v} {m₁ m₂ : Std.HashMap α β} [EquivBEq α] [LawfulHashable α] {k fallback : α} (not_mem : ¬k ∈ m₁) : (m₁ \ m₂).getKeyD k fallback = fallback`
- **getKey!_diff** {getKey!}: `… {β : Type v} {m₁ m₂ : Std.HashMap α β} [EquivBEq α] [LawfulHashable α] [Inhabited α] {k : α} : (m₁ \ m₂).getKey! k = if k ∈ m₂ then default else m₁.getKey! k`
- **getKey!_diff_of_not_mem_right** {getKey!}: `… {β : Type v} {m₁ m₂ : Std.HashMap α β} [EquivBEq α] [LawfulHashable α] [Inhabited α] {k : α} (not_mem : ¬k ∈ m₂) : (m₁ \ m₂).getKey! k = m₁.getKey! k`
- **getKey!_diff_of_mem_right** {getKey!}: `… {β : Type v} {m₁ m₂ : Std.HashMap α β} [EquivBEq α] [LawfulHashable α] [Inhabited α] {k : α} (mem : k ∈ m₂) : (m₁ \ m₂).getKey! k = default`
- **getKey!_diff_of_not_mem_left** {getKey!}: `… {β : Type v} {m₁ m₂ : Std.HashMap α β} [EquivBEq α] [LawfulHashable α] [Inhabited α] {k : α} (not_mem : ¬k ∈ m₁) : (m₁ \ m₂).getKey! k = default`
- **size_diff_le_size_left** {size}: `… {β : Type v} {m₁ m₂ : Std.HashMap α β} [EquivBEq α] [LawfulHashable α] : (m₁ \ m₂).size ≤ m₁.size`
- **size_diff_eq_size_left** {size}: `… {β : Type v} {m₁ m₂ : Std.HashMap α β} [EquivBEq α] [LawfulHashable α] (h : ∀ (a : α), a ∈ m₁ → ¬a ∈ m₂) : (m₁ \ m₂).size = m₁.size`
- **size_diff_add_size_inter_eq_size_left** {size}: `… {β : Type v} {m₁ m₂ : Std.HashMap α β} [EquivBEq α] [LawfulHashable α] : (m₁ \ m₂).size + (m₁ ∩ m₂).size = m₁.size`
- **isEmpty_diff_left** [simp] {isEmpty}: `… {β : Type v} {m₁ m₂ : Std.HashMap α β} [EquivBEq α] [LawfulHashable α] (h : m₁.isEmpty = true) : (m₁ \ m₂).isEmpty = true`
- **isEmpty_diff_iff** {isEmpty}: `… {β : Type v} {m₁ m₂ : Std.HashMap α β} [EquivBEq α] [LawfulHashable α] : (m₁ \ m₂).isEmpty = true ↔ ∀ (k : α), k ∈ m₁ → k ∈ m₂`

#### HashMap.Lemmas: insertManyIfNewUnit (HashMap α Unit) (29)

_scope: section@34_

- **insertManyIfNewUnit_nil** [simp]: `… {m : Std.HashMap α Unit} : m.insertManyIfNewUnit [] = m`
- **insertManyIfNewUnit_list_singleton** [simp]: `… {m : Std.HashMap α Unit} {k : α} : m.insertManyIfNewUnit [k] = m.insertIfNew k ()`
- **insertManyIfNewUnit_cons**: `… {m : Std.HashMap α Unit} {l : List α} {k : α} : m.insertManyIfNewUnit (k :: l) = (m.insertIfNew k ()).insertManyIfNewUnit l`
- **insertManyIfNewUnit_ind** [elab_as_elim]: `… {ρ : Type w} [ForIn Id ρ α] {motive : Std.HashMap α Unit → Prop} (m : Std.HashMap α Unit) (l : ρ) (init : motive m) (insert : ∀ (m : Std.HashMap α Unit) (a : α), motive m → motive (m.insertIfNew a ())) : motive (m.insertManyIfNewUnit l)`
- **contains_insertManyIfNewUnit_list** [simp]: `… {m : Std.HashMap α Unit} [EquivBEq α] [LawfulHashable α] {l : List α} {k : α} : (m.insertManyIfNewUnit l).contains k = (m.contains k || l.contains k)`
- **mem_insertManyIfNewUnit_list** [simp]: `… {m : Std.HashMap α Unit} [EquivBEq α] [LawfulHashable α] {l : List α} {k : α} : k ∈ m.insertManyIfNewUnit l ↔ k ∈ m ∨ l.contains k = true`
- **mem_of_mem_insertManyIfNewUnit_list**: `… {m : Std.HashMap α Unit} [EquivBEq α] [LawfulHashable α] {l : List α} {k : α} (contains_eq_false : l.contains k = false) : k ∈ m.insertManyIfNewUnit l → k ∈ m`
- **mem_insertManyIfNewUnit_of_mem**: `… {m : Std.HashMap α Unit} {ρ : Type w} [ForIn Id ρ α] [EquivBEq α] [LawfulHashable α] {l : ρ} {k : α} : k ∈ m → k ∈ m.insertManyIfNewUnit l`
- **getElem?_insertManyIfNewUnit_list**: `… {m : Std.HashMap α Unit} [EquivBEq α] [LawfulHashable α] {l : List α} {k : α} : (m.insertManyIfNewUnit l)[k]? = if k ∈ m ∨ l.contains k = true then some () else none`
- **getElem_insertManyIfNewUnit_list**: `… {m : Std.HashMap α Unit} {l : List α} {k : α} {h : k ∈ m.insertManyIfNewUnit l} : (m.insertManyIfNewUnit l)[k] = ()`
- **getElem!_insertManyIfNewUnit_list**: `… {m : Std.HashMap α Unit} {l : List α} {k : α} : (m.insertManyIfNewUnit l)[k]! = ()`
- **getD_insertManyIfNewUnit_list**: `… {m : Std.HashMap α Unit} {l : List α} {k : α} {fallback : Unit} : (m.insertManyIfNewUnit l).getD k fallback = ()`
- **getKey?_insertManyIfNewUnit_list_of_not_mem_of_contains_eq_false**: `… {m : Std.HashMap α Unit} [EquivBEq α] [LawfulHashable α] {l : List α} {k : α} (not_mem : ¬k ∈ m) (contains_eq_false : l.contains k = false) : (m.insertManyIfNewUnit l).getKey? k = none`
- **getKey?_insertManyIfNewUnit_list_of_not_mem_of_mem**: `… {m : Std.HashMap α Unit} [EquivBEq α] [LawfulHashable α] {l : List α} {k k' : α} (k_beq : (k == k') = true) (not_mem : ¬k ∈ m) (distinct : List.Pairwise (fun a b => (a == b) = false) l) (mem : k ∈ l) : (m.insertManyIfNewUnit l).getKey? k' = some k`
- **getKey?_insertManyIfNewUnit_list_of_mem**: `… {m : Std.HashMap α Unit} [EquivBEq α] [LawfulHashable α] {l : List α} {k : α} (mem : k ∈ m) : (m.insertManyIfNewUnit l).getKey? k = m.getKey? k`
- **getKey_insertManyIfNewUnit_list_of_not_mem_of_mem**: `… {m : Std.HashMap α Unit} [EquivBEq α] [LawfulHashable α] {l : List α} {k k' : α} (k_beq : (k == k') = true) (not_mem : ¬k ∈ m) (distinct : List.Pairwise (fun a b => (a == b) = false) l) (mem : k ∈ l) {h : k' ∈ m.insertManyIfNewUnit l} : (m.insertManyIfNewUnit l).getKey k' h = k`
- **getKey_insertManyIfNewUnit_list_of_mem**: `… {m : Std.HashMap α Unit} [EquivBEq α] [LawfulHashable α] {l : List α} {k : α} (mem : k ∈ m) {h : k ∈ m.insertManyIfNewUnit l} : (m.insertManyIfNewUnit l).getKey k h = m.getKey k mem`
- **getKey!_insertManyIfNewUnit_list_of_not_mem_of_contains_eq_false**: `… {m : Std.HashMap α Unit} [EquivBEq α] [LawfulHashable α] [Inhabited α] {l : List α} {k : α} (not_mem : ¬k ∈ m) (contains_eq_false : l.contains k = false) : (m.insertManyIfNewUnit l).getKey! k = default`
- **getKey!_insertManyIfNewUnit_list_of_not_mem_of_mem**: `… {m : Std.HashMap α Unit} [EquivBEq α] [LawfulHashable α] [Inhabited α] {l : List α} {k k' : α} (k_beq : (k == k') = true) (not_mem : ¬k ∈ m) (distinct : List.Pairwise (fun a b => (a == b) = false) l) (mem : k ∈ l) : (m.insertManyIfNewUnit l).getKey! k' = k`
- **getKey!_insertManyIfNewUnit_list_of_mem**: `… {m : Std.HashMap α Unit} [EquivBEq α] [LawfulHashable α] [Inhabited α] {l : List α} {k : α} (mem : k ∈ m) : (m.insertManyIfNewUnit l).getKey! k = m.getKey! k`
- **getKeyD_insertManyIfNewUnit_list_of_not_mem_of_contains_eq_false**: `… {m : Std.HashMap α Unit} [EquivBEq α] [LawfulHashable α] {l : List α} {k fallback : α} (not_mem : ¬k ∈ m) (contains_eq_false : l.contains k = false) : (m.insertManyIfNewUnit l).getKeyD k fallback = fallback`
- **getKeyD_insertManyIfNewUnit_list_of_not_mem_of_mem**: `… {m : Std.HashMap α Unit} [EquivBEq α] [LawfulHashable α] {l : List α} {k k' fallback : α} (k_beq : (k == k') = true) (not_mem : ¬k ∈ m) (distinct : List.Pairwise (fun a b => (a == b) = false) l) (mem : k ∈ l) : (m.insertManyIfNewUnit l).getKeyD k' fallback = k`
- **getKeyD_insertManyIfNewUnit_list_of_mem**: `… {m : Std.HashMap α Unit} [EquivBEq α] [LawfulHashable α] {l : List α} {k fallback : α} (mem : k ∈ m) : (m.insertManyIfNewUnit l).getKeyD k fallback = m.getKeyD k fallback`
- **size_insertManyIfNewUnit_list**: `… {m : Std.HashMap α Unit} [EquivBEq α] [LawfulHashable α] {l : List α} (distinct : List.Pairwise (fun a b => (a == b) = false) l) : (∀ (a : α), a ∈ m → l.contains a = false) → (m.insertManyIfNewUnit l).size = m.size + l.length`
- **size_le_size_insertManyIfNewUnit_list**: `… {m : Std.HashMap α Unit} [EquivBEq α] [LawfulHashable α] {l : List α} : m.size ≤ (m.insertManyIfNewUnit l).size`
- **size_le_size_insertManyIfNewUnit**: `… {m : Std.HashMap α Unit} {ρ : Type w} [ForIn Id ρ α] [EquivBEq α] [LawfulHashable α] {l : ρ} : m.size ≤ (m.insertManyIfNewUnit l).size`
- **size_insertManyIfNewUnit_list_le**: `… {m : Std.HashMap α Unit} [EquivBEq α] [LawfulHashable α] {l : List α} : (m.insertManyIfNewUnit l).size ≤ m.size + l.length`
- **isEmpty_insertManyIfNewUnit_list** [simp]: `… {m : Std.HashMap α Unit} [EquivBEq α] [LawfulHashable α] {l : List α} : (m.insertManyIfNewUnit l).isEmpty = (m.isEmpty && l.isEmpty)`
- **isEmpty_of_isEmpty_insertManyIfNewUnit**: `… {m : Std.HashMap α Unit} {ρ : Type w} [ForIn Id ρ α] [EquivBEq α] [LawfulHashable α] {l : ρ} : (m.insertManyIfNewUnit l).isEmpty = true → m.isEmpty = true`

#### HashMap.Lemmas: ofList / ofArray (24)

_scope: section@2244_

- **ofList_nil** [simp, grind =]: `… : Std.HashMap.ofList [] = ∅`
- **ofList_singleton** [simp, grind =]: `… {k : α} {v : β} : Std.HashMap.ofList [(k, v)] = ∅.insert k v`
- **ofList_cons** [grind _=_]: `… {k : α} {v : β} {tl : List (α × β)} : Std.HashMap.ofList ((k, v) :: tl) = (∅.insert k v).insertMany tl`
- **ofList_eq_insertMany_empty** [cbv_eval]: `… {l : List (α × β)} : Std.HashMap.ofList l = ∅.insertMany l`
- **contains_ofList** [simp, grind =]: `… [EquivBEq α] [LawfulHashable α] {l : List (α × β)} {k : α} : (Std.HashMap.ofList l).contains k = (List.map Prod.fst l).contains k`
- **mem_ofList** [simp, grind =]: `… [EquivBEq α] [LawfulHashable α] {l : List (α × β)} {k : α} : k ∈ Std.HashMap.ofList l ↔ (List.map Prod.fst l).contains k = true`
- **getElem?_ofList_of_contains_eq_false**: `… [EquivBEq α] [LawfulHashable α] {l : List (α × β)} {k : α} (contains_eq_false : (List.map Prod.fst l).contains k = false) : (Std.HashMap.ofList l)[k]? = none`
- **getElem?_ofList_of_mem**: `… [EquivBEq α] [LawfulHashable α] {l : List (α × β)} {k k' : α} (k_beq : (k == k') = true) {v : β} (distinct : List.Pairwise (fun a b => (a.fst == b.fst) = false) l) (mem : (k, v) ∈ l) : (Std.HashMap.ofList l)[k']? = some v`
- **getElem_ofList_of_mem**: `… [EquivBEq α] [LawfulHashable α] {l : List (α × β)} {k k' : α} (k_beq : (k == k') = true) {v : β} (distinct : List.Pairwise (fun a b => (a.fst == b.fst) = false) l) (mem : (k, v) ∈ l) {h : k' ∈ Std.HashMap.ofList l} : (Std.HashMap.ofList l)[k'] = v`
- **getElem!_ofList_of_contains_eq_false**: `… [EquivBEq α] [LawfulHashable α] {l : List (α × β)} {k : α} [Inhabited β] (contains_eq_false : (List.map Prod.fst l).contains k = false) : (Std.HashMap.ofList l)[k]! = default`
- **getElem!_ofList_of_mem**: `… [EquivBEq α] [LawfulHashable α] {l : List (α × β)} {k k' : α} (k_beq : (k == k') = true) {v : β} [Inhabited β] (distinct : List.Pairwise (fun a b => (a.fst == b.fst) = false) l) (mem : (k, v) ∈ l) : (Std.HashMap.ofList l)[k']! = v`
- **getD_ofList_of_contains_eq_false**: `… [EquivBEq α] [LawfulHashable α] {l : List (α × β)} {k : α} {fallback : β} (contains_eq_false : (List.map Prod.fst l).contains k = false) : (Std.HashMap.ofList l).getD k fallback = fallback`
- **getD_ofList_of_mem**: `… [EquivBEq α] [LawfulHashable α] {l : List (α × β)} {k k' : α} (k_beq : (k == k') = true) {v fallback : β} (distinct : List.Pairwise (fun a b => (a.fst == b.fst) = false) l) (mem : (k, v) ∈ l) : (Std.HashMap.ofList l).getD k' fallback = v`
- **getKey?_ofList_of_contains_eq_false**: `… [EquivBEq α] [LawfulHashable α] {l : List (α × β)} {k : α} (contains_eq_false : (List.map Prod.fst l).contains k = false) : (Std.HashMap.ofList l).getKey? k = none`
- **getKey?_ofList_of_mem**: `… [EquivBEq α] [LawfulHashable α] {l : List (α × β)} {k k' : α} (k_beq : (k == k') = true) (distinct : List.Pairwise (fun a b => (a.fst == b.fst) = false) l) (mem : k ∈ List.map Prod.fst l) : (Std.HashMap.ofList l).getKey? k' = some k`
- **getKey_ofList_of_mem**: `… [EquivBEq α] [LawfulHashable α] {l : List (α × β)} {k k' : α} (k_beq : (k == k') = true) (distinct : List.Pairwise (fun a b => (a.fst == b.fst) = false) l) (mem : k ∈ List.map Prod.fst l) {h : k' ∈ Std.HashMap.ofList l} : (Std.HashMap.ofList l).getKey k' h = k`
- **getKey!_ofList_of_contains_eq_false**: `… [EquivBEq α] [LawfulHashable α] [Inhabited α] {l : List (α × β)} {k : α} (contains_eq_false : (List.map Prod.fst l).contains k = false) : (Std.HashMap.ofList l).getKey! k = default`
- **getKey!_ofList_of_mem**: `… [EquivBEq α] [LawfulHashable α] [Inhabited α] {l : List (α × β)} {k k' : α} (k_beq : (k == k') = true) (distinct : List.Pairwise (fun a b => (a.fst == b.fst) = false) l) (mem : k ∈ List.map Prod.fst l) : (Std.HashMap.ofList l).getKey! k' = k`
- **getKeyD_ofList_of_contains_eq_false**: `… [EquivBEq α] [LawfulHashable α] {l : List (α × β)} {k fallback : α} (contains_eq_false : (List.map Prod.fst l).contains k = false) : (Std.HashMap.ofList l).getKeyD k fallback = fallback`
- **getKeyD_ofList_of_mem**: `… [EquivBEq α] [LawfulHashable α] {l : List (α × β)} {k k' fallback : α} (k_beq : (k == k') = true) (distinct : List.Pairwise (fun a b => (a.fst == b.fst) = false) l) (mem : k ∈ List.map Prod.fst l) : (Std.HashMap.ofList l).getKeyD k' fallback = k`
- **size_ofList**: `… [EquivBEq α] [LawfulHashable α] {l : List (α × β)} (distinct : List.Pairwise (fun a b => (a.fst == b.fst) = false) l) : (Std.HashMap.ofList l).size = l.length`
- **size_ofList_le** [grind_pattern (ofList l).size (l.2385)]: `… [EquivBEq α] [LawfulHashable α] {l : List (α × β)} : (Std.HashMap.ofList l).size ≤ l.length`
- **ofArray_eq_ofList** [simp, grind =, cbv_eval]: `… (a : Array (α × β)) : Std.HashMap.ofArray a = Std.HashMap.ofList a.toList`
- **isEmpty_ofList** [simp, grind =]: `… [EquivBEq α] [LawfulHashable α] {l : List (α × β)} : (Std.HashMap.ofList l).isEmpty = l.isEmpty`

#### HashMap.Lemmas: unitOfList / unitOfArray (HashMap α Unit) (21)

_scope: section@2244_

- **unitOfList_nil** [simp]: `… : Std.HashMap.unitOfList [] = ∅`
- **unitOfList_singleton** [simp]: `… {k : α} : Std.HashMap.unitOfList [k] = ∅.insertIfNew k ()`
- **unitOfList_cons**: `… {hd : α} {tl : List α} : Std.HashMap.unitOfList (hd :: tl) = (∅.insertIfNew hd ()).insertManyIfNewUnit tl`
- **unitOfList_eq_insertManyIfNewUnit_empty**: `… {l : List α} : Std.HashMap.unitOfList l = ∅.insertManyIfNewUnit l`
- **contains_unitOfList** [simp]: `… [EquivBEq α] [LawfulHashable α] {l : List α} {k : α} : (Std.HashMap.unitOfList l).contains k = l.contains k`
- **mem_unitOfList** [simp]: `… [EquivBEq α] [LawfulHashable α] {l : List α} {k : α} : k ∈ Std.HashMap.unitOfList l ↔ l.contains k = true`
- **getElem?_unitOfList** [simp]: `… [EquivBEq α] [LawfulHashable α] {l : List α} {k : α} : (Std.HashMap.unitOfList l)[k]? = if l.contains k = true then some () else none`
- **getElem_unitOfList** [simp]: `… {l : List α} {k : α} {h : k ∈ Std.HashMap.unitOfList l} : (Std.HashMap.unitOfList l)[k] = ()`
- **getElem!_unitOfList** [simp]: `… {l : List α} {k : α} : (Std.HashMap.unitOfList l)[k]! = ()`
- **getD_unitOfList** [simp]: `… {l : List α} {k : α} {fallback : Unit} : (Std.HashMap.unitOfList l).getD k fallback = ()`
- **getKey?_unitOfList_of_contains_eq_false**: `… [EquivBEq α] [LawfulHashable α] {l : List α} {k : α} (contains_eq_false : l.contains k = false) : (Std.HashMap.unitOfList l).getKey? k = none`
- **getKey?_unitOfList_of_mem**: `… [EquivBEq α] [LawfulHashable α] {l : List α} {k k' : α} (k_beq : (k == k') = true) (distinct : List.Pairwise (fun a b => (a == b) = false) l) (mem : k ∈ l) : (Std.HashMap.unitOfList l).getKey? k' = some k`
- **getKey_unitOfList_of_mem**: `… [EquivBEq α] [LawfulHashable α] {l : List α} {k k' : α} (k_beq : (k == k') = true) (distinct : List.Pairwise (fun a b => (a == b) = false) l) (mem : k ∈ l) {h : k' ∈ Std.HashMap.unitOfList l} : (Std.HashMap.unitOfList l).getKey k' h = k`
- **getKey!_unitOfList_of_contains_eq_false**: `… [EquivBEq α] [LawfulHashable α] [Inhabited α] {l : List α} {k : α} (contains_eq_false : l.contains k = false) : (Std.HashMap.unitOfList l).getKey! k = default`
- **getKey!_unitOfList_of_mem**: `… [EquivBEq α] [LawfulHashable α] [Inhabited α] {l : List α} {k k' : α} (k_beq : (k == k') = true) (distinct : List.Pairwise (fun a b => (a == b) = false) l) (mem : k ∈ l) : (Std.HashMap.unitOfList l).getKey! k' = k`
- **getKeyD_unitOfList_of_contains_eq_false**: `… [EquivBEq α] [LawfulHashable α] {l : List α} {k fallback : α} (contains_eq_false : l.contains k = false) : (Std.HashMap.unitOfList l).getKeyD k fallback = fallback`
- **getKeyD_unitOfList_of_mem**: `… [EquivBEq α] [LawfulHashable α] {l : List α} {k k' fallback : α} (k_beq : (k == k') = true) (distinct : List.Pairwise (fun a b => (a == b) = false) l) (mem : k ∈ l) : (Std.HashMap.unitOfList l).getKeyD k' fallback = k`
- **size_unitOfList**: `… [EquivBEq α] [LawfulHashable α] {l : List α} (distinct : List.Pairwise (fun a b => (a == b) = false) l) : (Std.HashMap.unitOfList l).size = l.length`
- **size_unitOfList_le**: `… [EquivBEq α] [LawfulHashable α] {l : List α} : (Std.HashMap.unitOfList l).size ≤ l.length`
- **unitOfArray_eq_unitOfList** [simp, grind =]: `… (a : Array α) : Std.HashMap.unitOfArray a = Std.HashMap.unitOfList a.toList`
- **isEmpty_unitOfList** [simp]: `… [EquivBEq α] [LawfulHashable α] {l : List α} : (Std.HashMap.unitOfList l).isEmpty = l.isEmpty`

#### HashMap.Lemmas: alter (32)

_scope: section Alter_

- **isEmpty_alter_eq_isEmpty_erase**: `… {m : Std.HashMap α β} [EquivBEq α] [LawfulHashable α] {k : α} {f : Option β → Option β} : (m.alter k f).isEmpty = ((m.erase k).isEmpty && (f m[k]?).isNone)`
- **isEmpty_alter** [simp, grind =]: `… {m : Std.HashMap α β} [EquivBEq α] [LawfulHashable α] {k : α} {f : Option β → Option β} : (m.alter k f).isEmpty = ((m.isEmpty || m.size == 1 && m.contains k) && (f m[k]?).isNone)`
- **contains_alter** [grind =]: `… {m : Std.HashMap α β} [EquivBEq α] [LawfulHashable α] {k k' : α} {f : Option β → Option β} : (m.alter k f).contains k' = if (k == k') = true then (f m[k]?).isSome else m.contains k'`
- **mem_alter** [grind =]: `… {m : Std.HashMap α β} [EquivBEq α] [LawfulHashable α] {k k' : α} {f : Option β → Option β} : k' ∈ m.alter k f ↔ if (k == k') = true then (f m[k]?).isSome = true else k' ∈ m`
- **mem_alter_of_beq**: `… {m : Std.HashMap α β} [EquivBEq α] [LawfulHashable α] {k k' : α} {f : Option β → Option β} (h : (k == k') = true) : k' ∈ m.alter k f ↔ (f m[k]?).isSome = true`
- **contains_alter_self** [simp]: `… {m : Std.HashMap α β} [EquivBEq α] [LawfulHashable α] {k : α} {f : Option β → Option β} : (m.alter k f).contains k = (f m[k]?).isSome`
- **mem_alter_self** [simp]: `… {m : Std.HashMap α β} [EquivBEq α] [LawfulHashable α] {k : α} {f : Option β → Option β} : k ∈ m.alter k f ↔ (f m[k]?).isSome = true`
- **contains_alter_of_beq_eq_false**: `… {m : Std.HashMap α β} [EquivBEq α] [LawfulHashable α] {k k' : α} {f : Option β → Option β} (h : (k == k') = false) : (m.alter k f).contains k' = m.contains k'`
- **mem_alter_of_beq_eq_false**: `… {m : Std.HashMap α β} [EquivBEq α] [LawfulHashable α] {k k' : α} {f : Option β → Option β} (h : (k == k') = false) : k' ∈ m.alter k f ↔ k' ∈ m`
- **size_alter** [grind =]: `… {m : Std.HashMap α β} [EquivBEq α] [LawfulHashable α] {k : α} {f : Option β → Option β} : (m.alter k f).size = if k ∈ m ∧ (f m[k]?).isNone = true then m.size - 1 else if ¬k ∈ m ∧ (f m[k]?).isSome = true then m.size + 1 else m.size`
- **size_alter_eq_add_one**: `… {m : Std.HashMap α β} [EquivBEq α] [LawfulHashable α] {k : α} {f : Option β → Option β} (h : ¬k ∈ m) (h' : (f m[k]?).isSome = true) : (m.alter k f).size = m.size + 1`
- **size_alter_eq_sub_one**: `… {m : Std.HashMap α β} [EquivBEq α] [LawfulHashable α] {k : α} {f : Option β → Option β} (h : k ∈ m) (h' : (f m[k]?).isNone = true) : (m.alter k f).size = m.size - 1`
- **size_alter_eq_self_of_not_mem**: `… {m : Std.HashMap α β} [EquivBEq α] [LawfulHashable α] {k : α} {f : Option β → Option β} (h : ¬k ∈ m) (h' : (f m[k]?).isNone = true) : (m.alter k f).size = m.size`
- **size_alter_eq_self_of_mem**: `… {m : Std.HashMap α β} [EquivBEq α] [LawfulHashable α] {k : α} {f : Option β → Option β} (h : k ∈ m) (h' : (f m[k]?).isSome = true) : (m.alter k f).size = m.size`
- **size_alter_le_size**: `… {m : Std.HashMap α β} [EquivBEq α] [LawfulHashable α] {k : α} {f : Option β → Option β} : (m.alter k f).size ≤ m.size + 1`
- **size_le_size_alter**: `… {m : Std.HashMap α β} [EquivBEq α] [LawfulHashable α] {k : α} {f : Option β → Option β} : m.size - 1 ≤ (m.alter k f).size`
- **getElem?_alter** [grind =]: `… {m : Std.HashMap α β} [EquivBEq α] [LawfulHashable α] {k k' : α} {f : Option β → Option β} : (m.alter k f)[k']? = if (k == k') = true then f m[k]? else m[k']?`
- **getElem?_alter_self** [simp]: `… {m : Std.HashMap α β} [EquivBEq α] [LawfulHashable α] {k : α} {f : Option β → Option β} : (m.alter k f)[k]? = f m[k]?`
- **getElem_alter** [grind =]: `… {m : Std.HashMap α β} [EquivBEq α] [LawfulHashable α] {k k' : α} {f : Option β → Option β} {h : k' ∈ m.alter k f} : (m.alter k f)[k'] = if heq : (k == k') = true then (f m[k]?).get ⋯ else m[k']`
- **getElem_alter_self** [simp]: `… {m : Std.HashMap α β} [EquivBEq α] [LawfulHashable α] {k : α} {f : Option β → Option β} {h : k ∈ m.alter k f} : (m.alter k f)[k] = (f m[k]?).get ⋯`
- **getElem!_alter** [grind =]: `… {m : Std.HashMap α β} [EquivBEq α] [LawfulHashable α] {k k' : α} [Inhabited β] {f : Option β → Option β} : (m.alter k f)[k']! = if (k == k') = true then (f m[k]?).get! else m[k']!`
- **getElem!_alter_self** [simp]: `… {m : Std.HashMap α β} [EquivBEq α] [LawfulHashable α] {k : α} [Inhabited β] {f : Option β → Option β} : (m.alter k f)[k]! = (f m[k]?).get!`
- **getD_alter** [grind =]: `… {m : Std.HashMap α β} [EquivBEq α] [LawfulHashable α] {k k' : α} {fallback : β} {f : Option β → Option β} : (m.alter k f).getD k' fallback = if (k == k') = true then (f m[k]?).getD fallback else m.getD k' fallback`
- **getD_alter_self** [simp]: `… {m : Std.HashMap α β} [EquivBEq α] [LawfulHashable α] {k : α} {fallback : β} {f : Option β → Option β} : (m.alter k f).getD k fallback = (f m[k]?).getD fallback`
- **getKey?_alter** [grind =]: `… {m : Std.HashMap α β} [EquivBEq α] [LawfulHashable α] {k k' : α} {f : Option β → Option β} : (m.alter k f).getKey? k' = if (k == k') = true then if (f m[k]?).isSome = true then some k else none else m.getKey? k'`
- **getKey?_alter_self**: `… {m : Std.HashMap α β} [EquivBEq α] [LawfulHashable α] {k : α} {f : Option β → Option β} : (m.alter k f).getKey? k = if (f m[k]?).isSome = true then some k else none`
- **getKey!_alter** [grind =]: `… {m : Std.HashMap α β} [EquivBEq α] [LawfulHashable α] [Inhabited α] {k k' : α} {f : Option β → Option β} : (m.alter k f).getKey! k' = if (k == k') = true then if (f m[k]?).isSome = true then k else default else m.getKey! k'`
- **getKey!_alter_self**: `… {m : Std.HashMap α β} [EquivBEq α] [LawfulHashable α] [Inhabited α] {k : α} {f : Option β → Option β} : (m.alter k f).getKey! k = if (f m[k]?).isSome = true then k else default`
- **getKey_alter** [grind =]: `… {m : Std.HashMap α β} [EquivBEq α] [LawfulHashable α] [Inhabited α] {k k' : α} {f : Option β → Option β} {h : k' ∈ m.alter k f} : (m.alter k f).getKey k' h = if heq : (k == k') = true then k else m.getKey k' ⋯`
- **getKey_alter_self** [simp]: `… {m : Std.HashMap α β} [EquivBEq α] [LawfulHashable α] [Inhabited α] {k : α} {f : Option β → Option β} {h : k ∈ m.alter k f} : (m.alter k f).getKey k h = k`
- **getKeyD_alter** [grind =]: `… {m : Std.HashMap α β} [EquivBEq α] [LawfulHashable α] {k k' fallback : α} {f : Option β → Option β} : (m.alter k f).getKeyD k' fallback = if (k == k') = true then if (f m[k]?).isSome = true then k else fallback else m.getKeyD k' fallback`
- **getKeyD_alter_self**: `… {m : Std.HashMap α β} [EquivBEq α] [LawfulHashable α] [Inhabited α] {k fallback : α} {f : Option β → Option β} : (m.alter k f).getKeyD k fallback = if (f m[k]?).isSome = true then k else fallback`

#### HashMap.Lemmas: modify (20)

_scope: section Modify_

- **isEmpty_modify** [simp, grind =]: `… {m : Std.HashMap α β} [EquivBEq α] [LawfulHashable α] {k : α} {f : β → β} : (m.modify k f).isEmpty = m.isEmpty`
- **contains_modify** [simp, grind =]: `… {m : Std.HashMap α β} [EquivBEq α] [LawfulHashable α] {k k' : α} {f : β → β} : (m.modify k f).contains k' = m.contains k'`
- **mem_modify** [simp, grind =]: `… {m : Std.HashMap α β} [EquivBEq α] [LawfulHashable α] {k k' : α} {f : β → β} : k' ∈ m.modify k f ↔ k' ∈ m`
- **size_modify** [simp, grind =]: `… {m : Std.HashMap α β} [EquivBEq α] [LawfulHashable α] {k : α} {f : β → β} : (m.modify k f).size = m.size`
- **getElem?_modify** [grind =]: `… {m : Std.HashMap α β} [EquivBEq α] [LawfulHashable α] {k k' : α} {f : β → β} : (m.modify k f)[k']? = if (k == k') = true then Option.map f m[k]? else m[k']?`
- **getElem?_modify_self** [simp]: `… {m : Std.HashMap α β} [EquivBEq α] [LawfulHashable α] {k : α} {f : β → β} : (m.modify k f)[k]? = Option.map f m[k]?`
- **getElem_modify** [grind =]: `… {m : Std.HashMap α β} [EquivBEq α] [LawfulHashable α] {k k' : α} {f : β → β} {h : k' ∈ m.modify k f} : (m.modify k f)[k'] = if heq : (k == k') = true then f m[k] else m[k']`
- **getElem_modify_self** [simp]: `… {m : Std.HashMap α β} [EquivBEq α] [LawfulHashable α] {k : α} {f : β → β} {h : k ∈ m.modify k f} : (m.modify k f)[k] = f m[k]`
- **getElem!_modify** [grind =]: `… {m : Std.HashMap α β} [EquivBEq α] [LawfulHashable α] {k k' : α} [Inhabited β] {f : β → β} : (m.modify k f)[k']! = if (k == k') = true then (Option.map f m[k]?).get! else m[k']!`
- **getElem!_modify_self** [simp]: `… {m : Std.HashMap α β} [EquivBEq α] [LawfulHashable α] {k : α} [Inhabited β] {f : β → β} : (m.modify k f)[k]! = (Option.map f m[k]?).get!`
- **getD_modify** [grind =]: `… {m : Std.HashMap α β} [EquivBEq α] [LawfulHashable α] {k k' : α} {fallback : β} {f : β → β} : (m.modify k f).getD k' fallback = if (k == k') = true then (Option.map f m[k]?).getD fallback else m.getD k' fallback`
- **getD_modify_self** [simp]: `… {m : Std.HashMap α β} [EquivBEq α] [LawfulHashable α] {k : α} {fallback : β} {f : β → β} : (m.modify k f).getD k fallback = (Option.map f m[k]?).getD fallback`
- **getKey?_modify** [grind =]: `… {m : Std.HashMap α β} [EquivBEq α] [LawfulHashable α] {k k' : α} {f : β → β} : (m.modify k f).getKey? k' = if (k == k') = true then if k ∈ m then some k else none else m.getKey? k'`
- **getKey?_modify_self**: `… {m : Std.HashMap α β} [EquivBEq α] [LawfulHashable α] {k : α} {f : β → β} : (m.modify k f).getKey? k = if k ∈ m then some k else none`
- **getKey!_modify** [grind =]: `… {m : Std.HashMap α β} [EquivBEq α] [LawfulHashable α] [Inhabited α] {k k' : α} {f : β → β} : (m.modify k f).getKey! k' = if (k == k') = true then if k ∈ m then k else default else m.getKey! k'`
- **getKey!_modify_self**: `… {m : Std.HashMap α β} [EquivBEq α] [LawfulHashable α] [Inhabited α] {k : α} {f : β → β} : (m.modify k f).getKey! k = if k ∈ m then k else default`
- **getKey_modify** [grind =]: `… {m : Std.HashMap α β} [EquivBEq α] [LawfulHashable α] [Inhabited α] {k k' : α} {f : β → β} {h : k' ∈ m.modify k f} : (m.modify k f).getKey k' h = if (k == k') = true then k else m.getKey k' ⋯`
- **getKey_modify_self** [simp]: `… {m : Std.HashMap α β} [EquivBEq α] [LawfulHashable α] [Inhabited α] {k : α} {f : β → β} {h : k ∈ m.modify k f} : (m.modify k f).getKey k h = k`
- **getKeyD_modify** [grind =]: `… {m : Std.HashMap α β} [EquivBEq α] [LawfulHashable α] {k k' fallback : α} {f : β → β} : (m.modify k f).getKeyD k' fallback = if (k == k') = true then if k ∈ m then k else fallback else m.getKeyD k' fallback`
- **getKeyD_modify_self**: `… {m : Std.HashMap α β} [EquivBEq α] [LawfulHashable α] [Inhabited α] {k fallback : α} {f : β → β} : (m.modify k f).getKeyD k fallback = if k ∈ m then k else fallback`

#### HashMap.Lemmas: namespace Equiv (Equiv.* lemmas) (38)

_scope: namespace Equiv_

- **Equiv.refl** [refl, simp]: `… (m : Std.HashMap α β) : m.Equiv m`
- **Equiv.rfl**: `… {m : Std.HashMap α β} : m.Equiv m`
- **Equiv.symm** [symm]: `… {m₁ m₂ : Std.HashMap α β} : m₁.Equiv m₂ → m₂.Equiv m₁`
- **Equiv.trans**: `… {m₁ m₂ m₃ : Std.HashMap α β} : m₁.Equiv m₂ → m₂.Equiv m₃ → m₁.Equiv m₃`
- **Equiv.comm**: `… {m₁ m₂ : Std.HashMap α β} : m₁.Equiv m₂ ↔ m₂.Equiv m₁`
- **Equiv.congr_left**: `… {m₁ m₂ m₃ : Std.HashMap α β} (h : m₁.Equiv m₂) : m₁.Equiv m₃ ↔ m₂.Equiv m₃`
- **Equiv.congr_right**: `… {m₁ m₂ m₃ : Std.HashMap α β} (h : m₁.Equiv m₂) : m₃.Equiv m₁ ↔ m₃.Equiv m₂`
- **Equiv.isEmpty_eq**: `… {m₁ m₂ : Std.HashMap α β} [EquivBEq α] [LawfulHashable α] (h : m₁.Equiv m₂) : m₁.isEmpty = m₂.isEmpty`
- **Equiv.size_eq**: `… {m₁ m₂ : Std.HashMap α β} [EquivBEq α] [LawfulHashable α] (h : m₁.Equiv m₂) : m₁.size = m₂.size`
- **Equiv.contains_eq**: `… {m₁ m₂ : Std.HashMap α β} [EquivBEq α] [LawfulHashable α] {k : α} (h : m₁.Equiv m₂) : m₁.contains k = m₂.contains k`
- **Equiv.mem_iff**: `… {m₁ m₂ : Std.HashMap α β} [EquivBEq α] [LawfulHashable α] {k : α} (h : m₁.Equiv m₂) : k ∈ m₁ ↔ k ∈ m₂`
- **Equiv.toList_perm**: `… {m₁ m₂ : Std.HashMap α β} (h : m₁.Equiv m₂) : m₁.toList.Perm m₂.toList`
- **Equiv.of_toList_perm**: `… {m₁ m₂ : Std.HashMap α β} (h : m₁.toList.Perm m₂.toList) : m₁.Equiv m₂`
- **Equiv.keys_perm**: `… {m₁ m₂ : Std.HashMap α β} (h : m₁.Equiv m₂) : m₁.keys.Perm m₂.keys`
- **Equiv.of_keys_unit_perm**: `… {m₁ m₂ : Std.HashMap α Unit} (h : m₁.keys.Perm m₂.keys) : m₁.Equiv m₂`
- **Equiv.getElem?_eq**: `… {m₁ m₂ : Std.HashMap α β} [EquivBEq α] [LawfulHashable α] {k : α} (h : m₁.Equiv m₂) : m₁[k]? = m₂[k]?`
- **Equiv.getElem_eq**: `… {m₁ m₂ : Std.HashMap α β} [EquivBEq α] [LawfulHashable α] {k : α} (hk : k ∈ m₁) (h : m₁.Equiv m₂) : m₁[k] = m₂[k]`
- **Equiv.getElem!_eq**: `… {m₁ m₂ : Std.HashMap α β} [EquivBEq α] [LawfulHashable α] {k : α} [Inhabited β] (h : m₁.Equiv m₂) : m₁[k]! = m₂[k]!`
- **Equiv.getD_eq**: `… {m₁ m₂ : Std.HashMap α β} [EquivBEq α] [LawfulHashable α] {k : α} {fallback : β} (h : m₁.Equiv m₂) : m₁.getD k fallback = m₂.getD k fallback`
- **Equiv.getKey?_eq**: `… {m₁ m₂ : Std.HashMap α β} [EquivBEq α] [LawfulHashable α] {k : α} (h : m₁.Equiv m₂) : m₁.getKey? k = m₂.getKey? k`
- **Equiv.getKey_eq**: `… {m₁ m₂ : Std.HashMap α β} [EquivBEq α] [LawfulHashable α] {k : α} (hk : k ∈ m₁) (h : m₁.Equiv m₂) : m₁.getKey k hk = m₂.getKey k ⋯`
- **Equiv.getKey!_eq**: `… {m₁ m₂ : Std.HashMap α β} [EquivBEq α] [LawfulHashable α] [Inhabited α] {k : α} (h : m₁.Equiv m₂) : m₁.getKey! k = m₂.getKey! k`
- **Equiv.getKeyD_eq**: `… {m₁ m₂ : Std.HashMap α β} [EquivBEq α] [LawfulHashable α] {k fallback : α} (h : m₁.Equiv m₂) : m₁.getKeyD k fallback = m₂.getKeyD k fallback`
- **Equiv.insert**: `… {m₁ m₂ : Std.HashMap α β} [EquivBEq α] [LawfulHashable α] (k : α) (v : β) (h : m₁.Equiv m₂) : (m₁.insert k v).Equiv (m₂.insert k v)`
- **Equiv.erase**: `… {m₁ m₂ : Std.HashMap α β} [EquivBEq α] [LawfulHashable α] (k : α) (h : m₁.Equiv m₂) : (m₁.erase k).Equiv (m₂.erase k)`
- **Equiv.insertIfNew**: `… {m₁ m₂ : Std.HashMap α β} [EquivBEq α] [LawfulHashable α] (k : α) (v : β) (h : m₁.Equiv m₂) : (m₁.insertIfNew k v).Equiv (m₂.insertIfNew k v)`
- **Equiv.insertMany_list**: `… {m₁ m₂ : Std.HashMap α β} [EquivBEq α] [LawfulHashable α] (l : List (α × β)) (h : m₁.Equiv m₂) : (m₁.insertMany l).Equiv (m₂.insertMany l)`
- **Equiv.insertManyIfNewUnit_list**: `… [EquivBEq α] [LawfulHashable α] {m₁ m₂ : Std.HashMap α Unit} (l : List α) (h : m₁.Equiv m₂) : (m₁.insertManyIfNewUnit l).Equiv (m₂.insertManyIfNewUnit l)`
- **Equiv.alter**: `… {m₁ m₂ : Std.HashMap α β} [EquivBEq α] [LawfulHashable α] (k : α) (f : Option β → Option β) (h : m₁.Equiv m₂) : (m₁.alter k f).Equiv (m₂.alter k f)`
- **Equiv.modify**: `… {m₁ m₂ : Std.HashMap α β} [EquivBEq α] [LawfulHashable α] (k : α) (f : β → β) (h : m₁.Equiv m₂) : (m₁.modify k f).Equiv (m₂.modify k f)`
- **Equiv.filter**: `… {m₁ m₂ : Std.HashMap α β} (f : α → β → Bool) (h : m₁.Equiv m₂) : (Std.HashMap.filter f m₁).Equiv (Std.HashMap.filter f m₂)`
- **Equiv.map**: `{α : Type u} {β : Type v} {γ : Type w} {x✝ : BEq α} {x✝¹ : Hashable α} {m₁ m₂ : Std.HashMap α β} (f : α → β → γ) (h : m₁.Equiv m₂) : (Std.HashMap.map f m₁).Equiv (Std.HashMap.map f m₂)`
- **Equiv.filterMap**: `{α : Type u} {β : Type v} {γ : Type w} {x✝ : BEq α} {x✝¹ : Hashable α} {m₁ m₂ : Std.HashMap α β} (f : α → β → Option γ) (h : m₁.Equiv m₂) : (Std.HashMap.filterMap f m₁).Equiv (Std.HashMap.filterMap f m₂)`
- **Equiv.of_forall_getKey_eq_of_forall_getElem?_eq**: `… {m₁ m₂ : Std.HashMap α β} [EquivBEq α] [LawfulHashable α] (hk : ∀ (k : α) (hk : k ∈ m₁) (hk' : k ∈ m₂), m₁.getKey k hk = m₂.getKey k hk') (hv : ∀ (k : α), m₁[k]? = m₂[k]?) : m₁.Equiv m₂`
- **Equiv.of_forall_getElem?_eq**: `… {m₁ m₂ : Std.HashMap α β} [LawfulBEq α] (h : ∀ (k : α), m₁[k]? = m₂[k]?) : m₁.Equiv m₂`
- **Equiv.of_forall_getKey?_unit_eq**: `… [EquivBEq α] [LawfulHashable α] {m₁ m₂ : Std.HashMap α Unit} (h : ∀ (k : α), m₁.getKey? k = m₂.getKey? k) : m₁.Equiv m₂`
- **Equiv.of_forall_contains_unit_eq**: `… [LawfulBEq α] {m₁ m₂ : Std.HashMap α Unit} (h : ∀ (k : α), m₁.contains k = m₂.contains k) : m₁.Equiv m₂`
- **Equiv.of_forall_mem_unit_iff**: `… [LawfulBEq α] {m₁ m₂ : Std.HashMap α Unit} (h : ∀ (k : α), k ∈ m₁ ↔ k ∈ m₂) : m₁.Equiv m₂`

#### HashMap.Lemmas: Equiv characterisations (section Equiv) (11)

_scope: section Equiv_

- **equiv_emptyWithCapacity_iff_isEmpty** [simp]: `… {m : Std.HashMap α β} [EquivBEq α] [LawfulHashable α] {c : Nat} : m.Equiv (Std.HashMap.emptyWithCapacity c) ↔ m.isEmpty = true`
- **equiv_empty_iff_isEmpty** [simp]: `… {m : Std.HashMap α β} [EquivBEq α] [LawfulHashable α] : m.Equiv ∅ ↔ m.isEmpty = true`
- **inter_equiv_empty_comm**: `… {m₁ m₂ : Std.HashMap α β} [EquivBEq α] [LawfulHashable α] : (m₁ ∩ m₂).Equiv ∅ ↔ (m₂ ∩ m₁).Equiv ∅`
- **emptyWithCapacity_equiv_iff_isEmpty** [simp]: `… {m : Std.HashMap α β} [EquivBEq α] [LawfulHashable α] {c : Nat} : (Std.HashMap.emptyWithCapacity c).Equiv m ↔ m.isEmpty = true`
- **empty_equiv_iff_isEmpty** [simp]: `… {m : Std.HashMap α β} [EquivBEq α] [LawfulHashable α] : ∅.Equiv m ↔ m.isEmpty = true`
- **equiv_iff_toList_perm**: `… {m₁ m₂ : Std.HashMap α β} [EquivBEq α] [LawfulHashable α] : m₁.Equiv m₂ ↔ m₁.toList.Perm m₂.toList`
- **equiv_iff_keys_unit_perm**: `… {m₁ m₂ : Std.HashMap α Unit} [EquivBEq α] [LawfulHashable α] : m₁.Equiv m₂ ↔ m₁.keys.Perm m₂.keys`
- **insertMany_list_equiv_foldl**: `… {m : Std.HashMap α β} {l : List (α × β)} : (m.insertMany l).Equiv (List.foldl (fun acc p => acc.insert p.fst p.snd) m l)`
- **ofList_equiv_foldl**: `… {l : List (α × β)} : (Std.HashMap.ofList l).Equiv (List.foldl (fun acc p => acc.insert p.fst p.snd) ∅ l)`
- **insertManyIfNewUnit_list_equiv_foldl**: `… {m : Std.HashMap α Unit} {l : List α} : (m.insertManyIfNewUnit l).Equiv (List.foldl (fun acc a => acc.insertIfNew a ()) m l)`
- **unitOfList_equiv_foldl**: `… {l : List α} : (Std.HashMap.unitOfList l).Equiv (List.foldl (fun acc a => acc.insertIfNew a ()) ∅ l)`

#### HashMap.Lemmas: filterMap (24)

_scope: section filterMap_

- **toList_filterMap**: `{α : Type u} {β : Type v} {γ : Type w} {x✝ : BEq α} {x✝¹ : Hashable α} {m : Std.HashMap α β} {f : α → β → Option γ} : (Std.HashMap.filterMap f m).toList.Perm (List.filterMap (fun p => Option.map (fun x => (p.fst, x)) (f p.fst p.snd)) m.toList)`
- **isEmpty_filterMap_iff** [grind =]: `{α : Type u} {β : Type v} {γ : Type w} {x✝ : BEq α} {x✝¹ : Hashable α} {m : Std.HashMap α β} [EquivBEq α] [LawfulHashable α] {f : α → β → Option γ} : (Std.HashMap.filterMap f m).isEmpty = true ↔ ∀ (k : α) (h : k ∈ m), f (m.getKey k h) m[k] = none`
- **isEmpty_filterMap_eq_false_iff**: `{α : Type u} {β : Type v} {γ : Type w} {x✝ : BEq α} {x✝¹ : Hashable α} {m : Std.HashMap α β} [EquivBEq α] [LawfulHashable α] {f : α → β → Option γ} : (Std.HashMap.filterMap f m).isEmpty = false ↔ ∃ k h, (f (m.getKey k h) m[k]).isSome = true`
- **mem_filterMap** [grind =]: `{α : Type u} {β : Type v} {γ : Type w} {x✝ : BEq α} {x✝¹ : Hashable α} {m : Std.HashMap α β} [EquivBEq α] [LawfulHashable α] {f : α → β → Option γ} {k : α} : k ∈ Std.HashMap.filterMap f m ↔ ∃ h, (f (m.getKey k h) m[k]).isSome = true`
- **contains_of_contains_filterMap**: `{α : Type u} {β : Type v} {γ : Type w} {x✝ : BEq α} {x✝¹ : Hashable α} {m : Std.HashMap α β} [EquivBEq α] [LawfulHashable α] {f : α → β → Option γ} {k : α} : (Std.HashMap.filterMap f m).contains k = true → m.contains k = true`
- **mem_of_mem_filterMap**: `{α : Type u} {β : Type v} {γ : Type w} {x✝ : BEq α} {x✝¹ : Hashable α} {m : Std.HashMap α β} [EquivBEq α] [LawfulHashable α] {f : α → β → Option γ} {k : α} : k ∈ Std.HashMap.filterMap f m → k ∈ m`
- **size_filterMap_le_size** [grind_pattern (m.filterMap f).size (l.3119)]: `{α : Type u} {β : Type v} {γ : Type w} {x✝ : BEq α} {x✝¹ : Hashable α} {m : Std.HashMap α β} [EquivBEq α] [LawfulHashable α] {f : α → β → Option γ} : (Std.HashMap.filterMap f m).size ≤ m.size`
- **size_filterMap_eq_size_iff**: `{α : Type u} {β : Type v} {γ : Type w} {x✝ : BEq α} {x✝¹ : Hashable α} {m : Std.HashMap α β} [EquivBEq α] [LawfulHashable α] {f : α → β → Option γ} : (Std.HashMap.filterMap f m).size = m.size ↔ ∀ (k : α) (h : k ∈ m), (f (m.getKey k h) m[k]).isSome = true`
- **getElem?_filterMap** [simp]: `{α : Type u} {β : Type v} {γ : Type w} {x✝ : BEq α} {x✝¹ : Hashable α} {m : Std.HashMap α β} [EquivBEq α] [LawfulHashable α] {f : α → β → Option γ} {k : α} : (Std.HashMap.filterMap f m)[k]? = m[k]?.pbind fun x h' => f (m.getKey k ⋯) x`
- **getElem?_filterMap'** [grind =, cbv_eval]: `{α : Type u} {β : Type v} {γ : Type w} {x✝ : BEq α} {x✝¹ : Hashable α} {m : Std.HashMap α β} [LawfulBEq α] {f : α → β → Option γ} {k : α} : (Std.HashMap.filterMap f m)[k]? = m[k]?.bind fun x => f k x`
- **getElem?_filterMap_of_getKey?_eq_some**: `{α : Type u} {β : Type v} {γ : Type w} {x✝ : BEq α} {x✝¹ : Hashable α} {m : Std.HashMap α β} [EquivBEq α] [LawfulHashable α] {f : α → β → Option γ} {k k' : α} (h : m.getKey? k = some k') : (Std.HashMap.filterMap f m)[k]? = m[k]?.bind (f k')`
- **isSome_apply_of_mem_filterMap**: `{α : Type u} {β : Type v} {γ : Type w} {x✝ : BEq α} {x✝¹ : Hashable α} {m : Std.HashMap α β} [EquivBEq α] [LawfulHashable α] {f : α → β → Option γ} {k : α} (h : k ∈ Std.HashMap.filterMap f m) : (f (m.getKey k ⋯) m[k]).isSome = true`
- **getElem_filterMap** [simp]: `{α : Type u} {β : Type v} {γ : Type w} {x✝ : BEq α} {x✝¹ : Hashable α} {m : Std.HashMap α β} [EquivBEq α] [LawfulHashable α] {f : α → β → Option γ} {k : α} {h : k ∈ Std.HashMap.filterMap f m} : (Std.HashMap.filterMap f m)[k] = (f (m.getKey k ⋯) m[k]).get ⋯`
- **getElem_filterMap'** [grind =]: `{α : Type u} {β : Type v} {γ : Type w} {x✝ : BEq α} {x✝¹ : Hashable α} {m : Std.HashMap α β} [LawfulBEq α] {f : α → β → Option γ} {k : α} {h : k ∈ Std.HashMap.filterMap f m} : (Std.HashMap.filterMap f m)[k] = (f k m[k]).get ⋯`
- **getElem!_filterMap**: `{α : Type u} {β : Type v} {γ : Type w} {x✝ : BEq α} {x✝¹ : Hashable α} {m : Std.HashMap α β} [EquivBEq α] [LawfulHashable α] [Inhabited γ] {f : α → β → Option γ} {k : α} : (Std.HashMap.filterMap f m)[k]! = (m[k]?.pbind fun x h' => f (m.getKey k ⋯) x).get!`
- **getElem!_filterMap'** [grind =, cbv_eval]: `{α : Type u} {β : Type v} {γ : Type w} {x✝ : BEq α} {x✝¹ : Hashable α} {m : Std.HashMap α β} [LawfulBEq α] [Inhabited γ] {f : α → β → Option γ} {k : α} : (Std.HashMap.filterMap f m)[k]! = (m[k]?.bind (f k)).get!`
- **getElem!_filterMap_of_getKey?_eq_some**: `{α : Type u} {β : Type v} {γ : Type w} {x✝ : BEq α} {x✝¹ : Hashable α} {m : Std.HashMap α β} [EquivBEq α] [LawfulHashable α] [Inhabited γ] {f : α → β → Option γ} {k k' : α} (h : m.getKey? k = some k') : (Std.HashMap.filterMap f m)[k]! = (m[k]?.bind (f k')).get!`
- **getD_filterMap**: `{α : Type u} {β : Type v} {γ : Type w} {x✝ : BEq α} {x✝¹ : Hashable α} {m : Std.HashMap α β} [EquivBEq α] [LawfulHashable α] {f : α → β → Option γ} {k : α} {fallback : γ} : (Std.HashMap.filterMap f m).getD k fallback = (m[k]?.pbind fun x h' => f (m.getKey k ⋯) x).getD fallback`
- **getD_filterMap'** [grind =, cbv_eval]: `{α : Type u} {β : Type v} {γ : Type w} {x✝ : BEq α} {x✝¹ : Hashable α} {m : Std.HashMap α β} [LawfulBEq α] {f : α → β → Option γ} {k : α} {fallback : γ} : (Std.HashMap.filterMap f m).getD k fallback = (m[k]?.bind (f k)).getD fallback`
- **getD_filterMap_of_getKey?_eq_some**: `{α : Type u} {β : Type v} {γ : Type w} {x✝ : BEq α} {x✝¹ : Hashable α} {m : Std.HashMap α β} [EquivBEq α] [LawfulHashable α] {f : α → β → Option γ} {k k' : α} {fallback : γ} (h : m.getKey? k = some k') : (Std.HashMap.filterMap f m).getD k fallback = (m[k]?.bind (f k')).getD fallback`
- **getKey?_filterMap** [grind =]: `{α : Type u} {β : Type v} {γ : Type w} {x✝ : BEq α} {x✝¹ : Hashable α} {m : Std.HashMap α β} [EquivBEq α] [LawfulHashable α] {f : α → β → Option γ} {k : α} : (Std.HashMap.filterMap f m).getKey? k = (m.getKey? k).pfilter fun x h' => (f x m[x]).isSome`
- **getKey_filterMap** [simp, grind =]: `{α : Type u} {β : Type v} {γ : Type w} {x✝ : BEq α} {x✝¹ : Hashable α} {m : Std.HashMap α β} [EquivBEq α] [LawfulHashable α] {f : α → β → Option γ} {k : α} {h' : k ∈ Std.HashMap.filterMap f m} : (Std.HashMap.filterMap f m).getKey k h' = m.getKey k ⋯`
- **getKey!_filterMap** [grind =]: `{α : Type u} {β : Type v} {γ : Type w} {x✝ : BEq α} {x✝¹ : Hashable α} {m : Std.HashMap α β} [EquivBEq α] [LawfulHashable α] [Inhabited α] {f : α → β → Option γ} {k : α} : (Std.HashMap.filterMap f m).getKey! k = ((m.getKey? k).pfilter fun x h' => (f x m[x]).isSome).get!`
- **getKeyD_filterMap** [grind =]: `{α : Type u} {β : Type v} {γ : Type w} {x✝ : BEq α} {x✝¹ : Hashable α} {m : Std.HashMap α β} [EquivBEq α] [LawfulHashable α] {f : α → β → Option γ} {k fallback : α} : (Std.HashMap.filterMap f m).getKeyD k fallback = ((m.getKey? k).pfilter fun x h' => (f x m[x]).isSome).getD fallback`

#### HashMap.Lemmas: filter (29)

_scope: section filter_

- **filterMap_equiv_filter**: `… {m : Std.HashMap α β} {f : α → β → Bool} : (Std.HashMap.filterMap (fun k => Option.guard fun v => f k v) m).Equiv (Std.HashMap.filter f m)`
- **toList_filter**: `… {m : Std.HashMap α β} {f : α → β → Bool} : (Std.HashMap.filter f m).toList.Perm (List.filter (fun p => f p.fst p.snd) m.toList)`
- **keys_filter_key**: `… {m : Std.HashMap α β} {f : α → Bool} : (Std.HashMap.filter (fun k x => f k) m).keys.Perm (List.filter f m.keys)`
- **isEmpty_filter_iff** [grind =]: `… {m : Std.HashMap α β} [EquivBEq α] [LawfulHashable α] {f : α → β → Bool} : (Std.HashMap.filter f m).isEmpty = true ↔ ∀ (k : α) (h : k ∈ m), f (m.getKey k h) m[k] = false`
- **isEmpty_filter_eq_false_iff**: `… {m : Std.HashMap α β} [EquivBEq α] [LawfulHashable α] {f : α → β → Bool} : (Std.HashMap.filter f m).isEmpty = false ↔ ∃ k h, f (m.getKey k h) m[k] = true`
- **mem_filter** [grind =]: `… {m : Std.HashMap α β} [EquivBEq α] [LawfulHashable α] {f : α → β → Bool} {k : α} : k ∈ Std.HashMap.filter f m ↔ ∃ h', f (m.getKey k h') m[k] = true`
- **contains_of_contains_filter**: `… {m : Std.HashMap α β} [EquivBEq α] [LawfulHashable α] {f : α → β → Bool} {k : α} : (Std.HashMap.filter f m).contains k = true → m.contains k = true`
- **mem_of_mem_filter**: `… {m : Std.HashMap α β} [EquivBEq α] [LawfulHashable α] {f : α → β → Bool} {k : α} : k ∈ Std.HashMap.filter f m → k ∈ m`
- **size_filter_le_size** [grind_pattern (m.filter f).size (l.3291)]: `… {m : Std.HashMap α β} [EquivBEq α] [LawfulHashable α] {f : α → β → Bool} : (Std.HashMap.filter f m).size ≤ m.size`
- **size_filter_eq_size_iff**: `… {m : Std.HashMap α β} [EquivBEq α] [LawfulHashable α] {f : α → β → Bool} : (Std.HashMap.filter f m).size = m.size ↔ ∀ (k : α) (h : k ∈ m), f (m.getKey k h) m[k] = true`
- **filter_equiv_self_iff**: `… {m : Std.HashMap α β} [EquivBEq α] [LawfulHashable α] {f : α → β → Bool} : (Std.HashMap.filter f m).Equiv m ↔ ∀ (k : α) (h : k ∈ m), f (m.getKey k h) m[k] = true`
- **getElem?_filter** [simp]: `… {m : Std.HashMap α β} [EquivBEq α] [LawfulHashable α] {f : α → β → Bool} {k : α} : (Std.HashMap.filter f m)[k]? = m[k]?.pfilter fun x h' => f (m.getKey k ⋯) x`
- **getElem?_filter'** [grind =, cbv_eval]: `… {m : Std.HashMap α β} [LawfulBEq α] {f : α → β → Bool} {k : α} : (Std.HashMap.filter f m)[k]? = Option.filter (f k) m[k]?`
- **getElem?_filter_of_getKey?_eq_some**: `… {m : Std.HashMap α β} [EquivBEq α] [LawfulHashable α] {f : α → β → Bool} {k k' : α} : m.getKey? k = some k' → (Std.HashMap.filter f m)[k]? = Option.filter (fun x => f k' x) m[k]?`
- **getElem_filter** [simp, grind =]: `… {m : Std.HashMap α β} [EquivBEq α] [LawfulHashable α] {f : α → β → Bool} {k : α} {h' : k ∈ Std.HashMap.filter f m} : (Std.HashMap.filter f m)[k] = m[k]`
- **getElem!_filter**: `… {m : Std.HashMap α β} [EquivBEq α] [LawfulHashable α] [Inhabited β] {f : α → β → Bool} {k : α} : (Std.HashMap.filter f m)[k]! = (m[k]?.pfilter fun x h' => f (m.getKey k ⋯) x).get!`
- **getElem!_filter'** [grind =, cbv_eval]: `… {m : Std.HashMap α β} [LawfulBEq α] [Inhabited β] {f : α → β → Bool} {k : α} : (Std.HashMap.filter f m)[k]! = (Option.filter (f k) m[k]?).get!`
- **getElem!_filter_of_getKey?_eq_some**: `… {m : Std.HashMap α β} [EquivBEq α] [LawfulHashable α] [Inhabited β] {f : α → β → Bool} {k k' : α} : m.getKey? k = some k' → (Std.HashMap.filter f m)[k]! = (Option.filter (f k') m[k]?).get!`
- **getD_filter**: `… {m : Std.HashMap α β} [EquivBEq α] [LawfulHashable α] {f : α → β → Bool} {k : α} {fallback : β} : (Std.HashMap.filter f m).getD k fallback = (m[k]?.pfilter fun x h' => f (m.getKey k ⋯) x).getD fallback`
- **getD_filter'** [grind =, cbv_eval]: `… {m : Std.HashMap α β} [LawfulBEq α] {f : α → β → Bool} {k : α} {fallback : β} : (Std.HashMap.filter f m).getD k fallback = (Option.filter (f k) m[k]?).getD fallback`
- **getD_filter_of_getKey?_eq_some**: `… {m : Std.HashMap α β} [EquivBEq α] [LawfulHashable α] {f : α → β → Bool} {k k' : α} {fallback : β} : m.getKey? k = some k' → (Std.HashMap.filter f m).getD k fallback = (Option.filter (fun x => f k' x) m[k]?).getD fallback`
- **keys_filter**: `… {m : Std.HashMap α β} [EquivBEq α] [LawfulHashable α] {f : α → β → Bool} : (Std.HashMap.filter f m).keys.Perm (List.filter (fun x => match x with | ⟨x, h'⟩ => f x m[x]) m.keys.attach).unattach`
- **getKey?_filter** [grind =]: `… {m : Std.HashMap α β} [EquivBEq α] [LawfulHashable α] {f : α → β → Bool} {k : α} : (Std.HashMap.filter f m).getKey? k = (m.getKey? k).pfilter fun x h' => f x m[x]`
- **getKey?_filter_key** [cbv_eval]: `… {m : Std.HashMap α β} [EquivBEq α] [LawfulHashable α] {f : α → Bool} {k : α} : (Std.HashMap.filter (fun k x => f k) m).getKey? k = Option.filter f (m.getKey? k)`
- **getKey_filter** [simp, grind =]: `… {m : Std.HashMap α β} [EquivBEq α] [LawfulHashable α] {f : α → β → Bool} {k : α} {h' : k ∈ Std.HashMap.filter f m} : (Std.HashMap.filter f m).getKey k h' = m.getKey k ⋯`
- **getKey!_filter** [grind =]: `… {m : Std.HashMap α β} [EquivBEq α] [LawfulHashable α] [Inhabited α] {f : α → β → Bool} {k : α} : (Std.HashMap.filter f m).getKey! k = ((m.getKey? k).pfilter fun x h' => f x m[x]).get!`
- **getKey!_filter_key** [cbv_eval]: `… {m : Std.HashMap α β} [EquivBEq α] [LawfulHashable α] [Inhabited α] {f : α → Bool} {k : α} : (Std.HashMap.filter (fun k x => f k) m).getKey! k = (Option.filter f (m.getKey? k)).get!`
- **getKeyD_filter** [grind =]: `… {m : Std.HashMap α β} [EquivBEq α] [LawfulHashable α] {f : α → β → Bool} {k fallback : α} : (Std.HashMap.filter f m).getKeyD k fallback = ((m.getKey? k).pfilter fun x h' => f x m[x]).getD fallback`
- **getKeyD_filter_key** [cbv_eval]: `… {m : Std.HashMap α β} [EquivBEq α] [LawfulHashable α] {f : α → Bool} {k fallback : α} : (Std.HashMap.filter (fun k x => f k) m).getKeyD k fallback = (Option.filter f (m.getKey? k)).getD fallback`

#### HashMap.Lemmas: map (26)

_scope: section map_

- **map_id_equiv**: `… {m : Std.HashMap α β} : (Std.HashMap.map (fun x v => v) m).Equiv m`
- **map_map_equiv**: `{α : Type u} {β : Type v} {γ : Type w} {δ : Type w'} {x✝ : BEq α} {x✝¹ : Hashable α} {m : Std.HashMap α β} {f : α → β → γ} {g : α → γ → δ} : (Std.HashMap.map g (Std.HashMap.map f m)).Equiv (Std.HashMap.map (fun k v => g k (f k v)) m)`
- **toList_map**: `{α : Type u} {β : Type v} {γ : Type w} {x✝ : BEq α} {x✝¹ : Hashable α} {m : Std.HashMap α β} {f : α → β → γ} : (Std.HashMap.map f m).toList.Perm (List.map (fun p => (p.fst, f p.fst p.snd)) m.toList)`
- **keys_map**: `{α : Type u} {β : Type v} {γ : Type w} {x✝ : BEq α} {x✝¹ : Hashable α} {m : Std.HashMap α β} {f : α → β → γ} : (Std.HashMap.map f m).keys.Perm m.keys`
- **filterMap_equiv_map**: `{α : Type u} {β : Type v} {γ : Type w} {x✝ : BEq α} {x✝¹ : Hashable α} {m : Std.HashMap α β} [EquivBEq α] [LawfulHashable α] {f : α → β → γ} : (Std.HashMap.filterMap (fun k v => some (f k v)) m).Equiv (Std.HashMap.map f m)`
- **isEmpty_map** [simp, grind =, cbv_eval]: `{α : Type u} {β : Type v} {γ : Type w} {x✝ : BEq α} {x✝¹ : Hashable α} {m : Std.HashMap α β} [EquivBEq α] [LawfulHashable α] {f : α → β → γ} : (Std.HashMap.map f m).isEmpty = m.isEmpty`
- **contains_map** [simp, grind =, cbv_eval]: `{α : Type u} {β : Type v} {γ : Type w} {x✝ : BEq α} {x✝¹ : Hashable α} {m : Std.HashMap α β} [EquivBEq α] [LawfulHashable α] {f : α → β → γ} {k : α} : (Std.HashMap.map f m).contains k = m.contains k`
- **contains_of_contains_map**: `{α : Type u} {β : Type v} {γ : Type w} {x✝ : BEq α} {x✝¹ : Hashable α} {m : Std.HashMap α β} [EquivBEq α] [LawfulHashable α] {f : α → β → γ} {k : α} : (Std.HashMap.map f m).contains k = true → m.contains k = true`
- **mem_map** [simp, grind =]: `{α : Type u} {β : Type v} {γ : Type w} {x✝ : BEq α} {x✝¹ : Hashable α} {m : Std.HashMap α β} [EquivBEq α] [LawfulHashable α] {f : α → β → γ} {k : α} : k ∈ Std.HashMap.map f m ↔ k ∈ m`
- **mem_of_mem_map**: `{α : Type u} {β : Type v} {γ : Type w} {x✝ : BEq α} {x✝¹ : Hashable α} {m : Std.HashMap α β} [EquivBEq α] [LawfulHashable α] {f : α → β → γ} {k : α} : k ∈ Std.HashMap.map f m → k ∈ m`
- **size_map** [simp, grind =, cbv_eval]: `{α : Type u} {β : Type v} {γ : Type w} {x✝ : BEq α} {x✝¹ : Hashable α} {m : Std.HashMap α β} [EquivBEq α] [LawfulHashable α] {f : α → β → γ} : (Std.HashMap.map f m).size = m.size`
- **getElem?_map** [simp, grind =, cbv_eval]: `{α : Type u} {β : Type v} {γ : Type w} {x✝ : BEq α} {x✝¹ : Hashable α} {m : Std.HashMap α β} [LawfulBEq α] {f : α → β → γ} {k : α} : (Std.HashMap.map f m)[k]? = Option.map (f k) m[k]?`
- **getElem?_map'** [simp (low)]: `{α : Type u} {β : Type v} {γ : Type w} {x✝ : BEq α} {x✝¹ : Hashable α} {m : Std.HashMap α β} [EquivBEq α] [LawfulHashable α] {f : α → β → γ} {k : α} : (Std.HashMap.map f m)[k]? = Option.pmap (fun v h' => f (m.getKey k h') v) m[k]? ⋯`
- **getElem?_map_of_getKey?_eq_some**: `{α : Type u} {β : Type v} {γ : Type w} {x✝ : BEq α} {x✝¹ : Hashable α} {m : Std.HashMap α β} [EquivBEq α] [LawfulHashable α] {f : α → β → γ} {k k' : α} (h : m.getKey? k = some k') : (Std.HashMap.map f m)[k]? = Option.map (f k') m[k]?`
- **getElem_map** [simp, grind =]: `{α : Type u} {β : Type v} {γ : Type w} {x✝ : BEq α} {x✝¹ : Hashable α} {m : Std.HashMap α β} [LawfulBEq α] {f : α → β → γ} {k : α} {h' : k ∈ Std.HashMap.map f m} : (Std.HashMap.map f m)[k] = f k m[k]`
- **getElem_map'** [simp (low)]: `{α : Type u} {β : Type v} {γ : Type w} {x✝ : BEq α} {x✝¹ : Hashable α} {m : Std.HashMap α β} [EquivBEq α] [LawfulHashable α] {f : α → β → γ} {k : α} {h' : k ∈ Std.HashMap.map f m} : (Std.HashMap.map f m)[k] = f (m.getKey k ⋯) m[k]`
- **getElem!_map** [grind =, cbv_eval]: `{α : Type u} {β : Type v} {γ : Type w} {x✝ : BEq α} {x✝¹ : Hashable α} {m : Std.HashMap α β} [LawfulBEq α] [Inhabited γ] {f : α → β → γ} {k : α} : (Std.HashMap.map f m)[k]! = (Option.map (f k) m[k]?).get!`
- **getElem!_map'**: `{α : Type u} {β : Type v} {γ : Type w} {x✝ : BEq α} {x✝¹ : Hashable α} {m : Std.HashMap α β} [EquivBEq α] [LawfulHashable α] [Inhabited γ] {f : α → β → γ} {k : α} : (Std.HashMap.map f m)[k]! = (Option.pmap (fun v h => f (m.getKey k h) v) m[k]? ⋯).get!`
- **getElem!_map_of_getKey?_eq_some**: `{α : Type u} {β : Type v} {γ : Type w} {x✝ : BEq α} {x✝¹ : Hashable α} {m : Std.HashMap α β} [EquivBEq α] [LawfulHashable α] [Inhabited γ] {f : α → β → γ} {k k' : α} (h : m.getKey? k = some k') : (Std.HashMap.map f m)[k]! = (Option.map (f k') m[k]?).get!`
- **getD_map** [grind =, cbv_eval]: `{α : Type u} {β : Type v} {γ : Type w} {x✝ : BEq α} {x✝¹ : Hashable α} {m : Std.HashMap α β} [LawfulBEq α] {f : α → β → γ} {k : α} {fallback : γ} : (Std.HashMap.map f m).getD k fallback = (Option.map (f k) m[k]?).getD fallback`
- **getD_map'**: `{α : Type u} {β : Type v} {γ : Type w} {x✝ : BEq α} {x✝¹ : Hashable α} {m : Std.HashMap α β} [EquivBEq α] [LawfulHashable α] {f : α → β → γ} {k : α} {fallback : γ} : (Std.HashMap.map f m).getD k fallback = (Option.pmap (fun v h => f (m.getKey k h) v) m[k]? ⋯).getD fallback`
- **getD_map_of_getKey?_eq_some**: `{α : Type u} {β : Type v} {γ : Type w} {x✝ : BEq α} {x✝¹ : Hashable α} {m : Std.HashMap α β} [EquivBEq α] [LawfulHashable α] [Inhabited γ] {f : α → β → γ} {k k' : α} {fallback : γ} (h : m.getKey? k = some k') : (Std.HashMap.map f m).getD k fallback = (Option.map (f k') m[k]?).getD fallback`
- **getKey?_map** [simp, grind =, cbv_eval]: `{α : Type u} {β : Type v} {γ : Type w} {x✝ : BEq α} {x✝¹ : Hashable α} {m : Std.HashMap α β} [EquivBEq α] [LawfulHashable α] {f : α → β → γ} {k : α} : (Std.HashMap.map f m).getKey? k = m.getKey? k`
- **getKey_map** [simp, grind =]: `{α : Type u} {β : Type v} {γ : Type w} {x✝ : BEq α} {x✝¹ : Hashable α} {m : Std.HashMap α β} [EquivBEq α] [LawfulHashable α] {f : α → β → γ} {k : α} {h' : k ∈ Std.HashMap.map f m} : (Std.HashMap.map f m).getKey k h' = m.getKey k ⋯`
- **getKey!_map** [simp, grind =, cbv_eval]: `{α : Type u} {β : Type v} {γ : Type w} {x✝ : BEq α} {x✝¹ : Hashable α} {m : Std.HashMap α β} [EquivBEq α] [LawfulHashable α] [Inhabited α] {f : α → β → γ} {k : α} : (Std.HashMap.map f m).getKey! k = m.getKey! k`
- **getKeyD_map** [simp, grind =, cbv_eval]: `{α : Type u} {β : Type v} {γ : Type w} {x✝ : BEq α} {x✝¹ : Hashable α} {m : Std.HashMap α β} [EquivBEq α] [LawfulHashable α] {f : α → β → γ} {k fallback : α} : (Std.HashMap.map f m).getKeyD k fallback = m.getKeyD k fallback`

#### HashMap.IteratorLemmas: section EntriesIter (3)

_scope: section EntriesIter_

- **toList_iter** [simp]: `{α : Type u} {β : Type v} [BEq α] [Hashable α] {m : Std.HashMap α β} : m.iter.toList = m.toList`
- **toListRev_iter** [simp]: `{α : Type u} {β : Type v} [BEq α] [Hashable α] {m : Std.HashMap α β} : m.iter.toListRev = m.toList.reverse`
- **toArray_iter** [simp]: `{α : Type u} {β : Type v} [BEq α] [Hashable α] {m : Std.HashMap α β} : m.iter.toArray = m.toArray`

#### HashMap.IteratorLemmas: section KeysIter (3)

_scope: section KeysIter_

- **toList_keysIter** [simp]: `{α β : Type u} [BEq α] [Hashable α] {m : Std.HashMap α β} [EquivBEq α] [LawfulHashable α] : m.keysIter.toList = m.keys`
- **toListRev_keysIter** [simp]: `{α β : Type u} [BEq α] [Hashable α] {m : Std.HashMap α β} [EquivBEq α] [LawfulHashable α] : m.keysIter.toListRev = m.keys.reverse`
- **toArray_keysIter** [simp]: `{α β : Type u} [BEq α] [Hashable α] {m : Std.HashMap α β} [EquivBEq α] [LawfulHashable α] : m.keysIter.toArray = m.keysArray`

#### HashMap.IteratorLemmas: section ValuesIter (3)

_scope: section ValuesIter_

- **toList_valuesIter_eq_toList_map_snd** [simp]: `{α β : Type u} [BEq α] [Hashable α] {m : Std.HashMap α β} : m.valuesIter.toList = List.map Prod.snd m.toList`
- **toListRev_valuesIter** [simp]: `{α β : Type u} [BEq α] [Hashable α] {m : Std.HashMap α β} : m.valuesIter.toListRev = (List.map Prod.snd m.toList).reverse`
- **toArray_valuesIter** [simp]: `{α β : Type u} [BEq α] [Hashable α] {m : Std.HashMap α β} : m.valuesIter.toArray = (List.map Prod.snd m.toList).toArray`

## Std.HashSet

### Types, structure-generated constants, notation

- `Std.HashSet.ctorIdx` (structure_generated, def): `{α : Type u} {inst✝ : BEq α} {inst✝¹ : Hashable α} : Std.HashSet α → Nat`
- `Std.HashSet.mk.inj` (structure_generated, theorem): `{α : Type u} {inst✝ : BEq α} {inst✝¹ : Hashable α} {inner inner✝ : Std.HashMap α Unit} : { inner := inner } = { inner := inner✝ } → inner = inner✝`
- `Std.HashSet.mk.injEq` (structure_generated, theorem): `{α : Type u} [BEq α] [Hashable α] (inner inner✝ : Std.HashMap α Unit) : ({ inner := inner } = { inner := inner✝ }) = (inner = inner✝)`
- `Std.HashSet.mk.sizeOf_spec` (structure_generated, theorem): `{α : Type u} [BEq α] [Hashable α] [SizeOf α] (inner : Std.HashMap α Unit) : sizeOf { inner := inner } = 1 + sizeOf inner`
- `Std.HashSet.noConfusionType` (structure_generated, def): `(P : Sort u_1) {α : Type u} [BEq α] [Hashable α] (t : Std.HashSet α) {α' : Type u} [BEq α'] [Hashable α'] (t' : Std.HashSet α') : Sort u_1`
- `Std.HashSet` (type, structure): `(α : Type u) [BEq α] [Hashable α] : Type u`
- `Std.HashSet.rec` (structure_generated, recursor): `{α : Type u} [BEq α] [Hashable α] {motive : Std.HashSet α → Sort u_1} (mk : (inner : Std.HashMap α Unit) → motive { inner := inner }) (t : Std.HashSet α) : motive t`
- `Std.HashSet.mk` (structure_generated, ctor): `{α : Type u} [BEq α] [Hashable α] (inner : Std.HashMap α Unit) : Std.HashSet α`
- `Std.HashSet.inner` (structure_generated, projection): `{α : Type u} [BEq α] [Hashable α] (self : Std.HashSet α) : Std.HashMap α Unit`
- `Std.HashSet.Equiv` (type, structure): `… (m₁ m₂ : Std.HashSet α) : Prop`
- `Std.HashSet.Equiv.rec` (structure_generated, recursor): `… {m₁ m₂ : Std.HashSet α} {motive : m₁.Equiv m₂ → Sort u_1} (mk : (inner : m₁.inner.Equiv m₂.inner) → motive ⋯) (t : m₁.Equiv m₂) : motive t`
- `Std.HashSet.Equiv.mk` (structure_generated, ctor): `… {m₁ m₂ : Std.HashSet α} (inner : m₁.inner.Equiv m₂.inner) : m₁.Equiv m₂`
- `Std.HashSet.Equiv.inner` (structure_generated, theorem): `… {m₁ m₂ : Std.HashSet α} (self : m₁.Equiv m₂) : m₁.inner.Equiv m₂.inner`
- `Std.HashSet.«term_~m_»` (notation, def): `: TrailingParserDescr`
- `Std.HashSet.get.congr_simp` (auto_generated, theorem): `{α : Type u} [BEq α] [Hashable α] (m m✝ : Std.HashSet α) (e_m : m = m✝) (a a✝ : α) (e_a : a = a✝) (h : a ∈ m) : m.get a h = m✝.get a✝ ⋯`

### Definitions

- **emptyWithCapacity** (Basic, l.62) [cbv_opaque, inline] (lemmas mentioning it: 11)  
  `{α : Type u} [BEq α] [Hashable α] (capacity : Nat := 8) : Std.HashSet α`  
  _Creates a new empty hash set_
- **insert** (Basic, l.86) [cbv_opaque, inline] (lemmas mentioning it: 28)  
  `… (m : Std.HashSet α) (a : α) : Std.HashSet α`  
  _Inserts the given element into the set_
- **containsThenInsert** (Basic, l.101) [inline] (lemmas mentioning it: 2)  
  `… (m : Std.HashSet α) (a : α) : Bool × Std.HashSet α`  
  _Checks whether an element is present in a set and inserts the element if it was not found_
- **contains** (Basic, l.112) [inline] (lemmas mentioning it: 41)  
  `… (m : Std.HashSet α) (a : α) : Bool`  
  _Returns `true` if the given key is present in the set_
- **erase** (Basic, l.128) [cbv_opaque, inline] (lemmas mentioning it: 18)  
  `… (m : Std.HashSet α) (a : α) : Std.HashSet α`  
  _Removes the element if it exists._
- **size** (Basic, l.132) [inline] (lemmas mentioning it: 33)  
  `… (m : Std.HashSet α) : Nat`  
  _The number of elements present in the set_
- **get?** (Basic, l.136) [inline] (lemmas mentioning it: 48)  
  `… (m : Std.HashSet α) (a : α) : Option α`  
  _Checks if given key is contained and returns the key if it is, otherwise `none`_
- **get** (Basic, l.143) [inline] (lemmas mentioning it: 32)  
  `{α : Type u} [BEq α] [Hashable α] (m : Std.HashSet α) (a : α) (h : a ∈ m) : α`  
  _Retrieves the key from the set that matches `a`_
- **getD** (Basic, l.150) [inline] (lemmas mentioning it: 35)  
  `{α : Type u} [BEq α] [Hashable α] (m : Std.HashSet α) (a fallback : α) : α`  
  _Checks if given key is contained and returns the key if it is, otherwise `fallback`_
- **get!** (Basic, l.157) [inline] (lemmas mentioning it: 34)  
  `{α : Type u} [BEq α] [Hashable α] [Inhabited α] (m : Std.HashSet α) (a : α) : α`  
  _Checks if given key is contained and returns the key if it is, otherwise panics_
- **isEmpty** (Basic, l.164) [inline] (lemmas mentioning it: 33)  
  `… (m : Std.HashSet α) : Bool`  
  _Returns `true` if the hash set contains no elements_
- **toList** (Basic, l.174) [inline] (lemmas mentioning it: 24)  
  `… (m : Std.HashSet α) : List α`  
  _Transforms the hash set into a list of elements in some order._
- **ofList** (Basic, l.178) [inline] (lemmas mentioning it: 18)  
  `{α : Type u} [BEq α] [Hashable α] (l : List α) : Std.HashSet α`  
  _Creates a hash set from a list of elements_
- **foldM** (Basic, l.186) [inline] (lemmas mentioning it: 2)  
  `… {m : Type v → Type w} [Monad m] {β : Type v} (f : β → α → m β) (init : β) (b : Std.HashSet α) : m β`  
  _Monadically computes a value by folding the given function over the elements in the hash set in some order._
- **fold** (Basic, l.194) [inline] (lemmas mentioning it: 2)  
  `… {β : Type v} (f : β → α → β) (init : β) (m : Std.HashSet α) : β`  
  _Folds the given function over the elements of the hash set in some order._
- **forM** (Basic, l.199) [inline] (lemmas mentioning it: 2)  
  `… {m : Type v → Type w} [Monad m] (f : α → m PUnit) (b : Std.HashSet α) : m PUnit`  
  _Carries out a monadic action on each element in the hash set in some order._
- **forIn** (Basic, l.204) [inline] (lemmas mentioning it: 1)  
  `… {m : Type v → Type w} [Monad m] {β : Type v} (f : α → β → m (ForInStep β)) (init : β) (b : Std.HashSet α) : m β`  
  _Support for the `for` loop construct in `do` blocks._
- **filter** (Basic, l.215) [cbv_opaque, inline] (lemmas mentioning it: 14)  
  `… (f : α → Bool) (m : Std.HashSet α) : Std.HashSet α`  
  _Removes all elements from the hash set for which the given function returns `false`._
- **insertMany** (Basic, l.219) [inline] (lemmas mentioning it: 30)  
  `… {ρ : Type v} [ForIn Id ρ α] (m : Std.HashSet α) (l : ρ) : Std.HashSet α`  
  _Inserts multiple mappings into the hash set by iterating over the given collection and calling `insert`_
- **toArray** (Basic, l.231) [inline] (lemmas mentioning it: 13)  
  `… (m : Std.HashSet α) : Array α`  
  _Transforms the hash set into an array of elements in some order._
- **all** (Basic, l.235) [inline] (lemmas mentioning it: 7)  
  `… (m : Std.HashSet α) (p : α → Bool) : Bool`  
  _Check if all elements satisfy the predicate, short-circuiting if a predicate fails._
- **any** (Basic, l.238) [inline] (lemmas mentioning it: 7)  
  `… (m : Std.HashSet α) (p : α → Bool) : Bool`  
  _Check if any element satisfies the predicate, short-circuiting if a predicate succeeds._
- **union** (Basic, l.240) [inline] (lemmas mentioning it: 1)  
  `{α : Type u} [BEq α] [Hashable α] (m₁ m₂ : Std.HashSet α) : Std.HashSet α`  
  _Computes the union of the given hash sets_
- **inter** (Basic, l.251) [inline] (lemmas mentioning it: 1)  
  `{α : Type u} [BEq α] [Hashable α] (m₁ m₂ : Std.HashSet α) : Std.HashSet α`  
  _Computes the intersection of the given hash sets_
- **beq** (Basic, l.263) (lemmas mentioning it: 0)  
  `{α : Type u} {x✝ : Hashable α} [BEq α] (m₁ m₂ : Std.HashSet α) : Bool`  
  _Compares two hash sets using Boolean equality on keys_
- **diff** (Basic, l.273) [inline] (lemmas mentioning it: 1)  
  `{α : Type u} [BEq α] [Hashable α] (m₁ m₂ : Std.HashSet α) : Std.HashSet α`  
  _Computes the difference of the given hash sets_
- **partition** (Basic, l.288) [inline] (lemmas mentioning it: 0)  
  `… (f : α → Bool) (m : Std.HashSet α) : Std.HashSet α × Std.HashSet α`  
  _Partition a hashset into two hashsets based on a predicate._
- **ofArray** (Basic, l.293) [inline] (lemmas mentioning it: 1)  
  `{α : Type u} [BEq α] [Hashable α] (l : Array α) : Std.HashSet α`  
  _Creates a hash set from an array of elements_
- **Internal.numBuckets** (Basic, l.301) (lemmas mentioning it: 0)  
  `… (m : Std.HashSet α) : Nat`  
  _Returns the number of buckets in the internal representation of the hash set_
- **iter** (Iterator, l.37) [inline] (lemmas mentioning it: 3)  
  `{α : Type u} [BEq α] [Hashable α] (m : Std.HashSet α) : Std.Iter α`  
  _Returns a finite iterator over the elements of a hash set_

### Instances

- **instEmptyCollection**: class `EmptyCollection` (Basic, l.71); `{α : Type u} [BEq α] [Hashable α] : EmptyCollection (Std.HashSet α)`
- **instInhabited**: class `Inhabited` (Basic, l.74); `{α : Type u} [BEq α] [Hashable α] : Inhabited (Std.HashSet α)`
- **instSingleton**: class `Singleton` (Basic, l.97); `… : Singleton α (Std.HashSet α)`
- **instInsert**: class `Insert` (Basic, l.99); `… : Insert α (Std.HashSet α)`
- **instMembership**: class `Membership` (Basic, l.122); `{α : Type u} [BEq α] [Hashable α] : Membership α (Std.HashSet α)`
- **instDecidableMem**: class `Decidable` (Basic, l.125); `{α : Type u} [BEq α] [Hashable α] {m : Std.HashSet α} {a : α} : Decidable (a ∈ m)`
- **instForMOfMonad**: class `ForM` (Basic, l.209); `{α : Type u} [BEq α] [Hashable α] {m : Type v → Type w} [Monad m] : ForM m (Std.HashSet α) α`
- **instForInOfMonad**: class `ForIn` (Basic, l.212); `{α : Type u} [BEq α] [Hashable α] {m : Type v → Type w} [Monad m] : ForIn m (Std.HashSet α) α`
- **instUnion**: class `Union` (Basic, l.249); `{α : Type u} [BEq α] [Hashable α] : Union (Std.HashSet α)`
- **instInter**: class `Inter` (Basic, l.260); `{α : Type u} [BEq α] [Hashable α] : Inter (Std.HashSet α)`
- **instBEq**: class `BEq` (Basic, l.271); `{α : Type u} {x✝ : Hashable α} [BEq α] : BEq (Std.HashSet α)`
- **instSDiff**: class `SDiff` (Basic, l.282); `{α : Type u} [BEq α] [Hashable α] : SDiff (Std.HashSet α)`
- **instRepr**: class `Repr` (Basic, l.309); `{α : Type u} [BEq α] [Hashable α] [Repr α] : Repr (Std.HashSet α)`
- **instDecidableEquivOfLawfulBEq**: class `Decidable` (DecidableEquiv, l.20); `{α : Type u} [BEq α] [LawfulBEq α] [Hashable α] (m₁ m₂ : Std.HashSet α) : Decidable (m₁.Equiv m₂)`
- **instPureForInOfLawfulMonad**: class `Std.Internal.PureForIn` (Lemmas, l.559); `… {m' : Type v → Type w} [Monad m'] [LawfulMonad m'] : Std.Internal.PureForIn m' (Std.HashSet α) α`
- **Equiv.instTrans**: class `Trans` (Lemmas, l.1382); `… : Trans Std.HashSet.Equiv Std.HashSet.Equiv Std.HashSet.Equiv`

### Theorems by section

#### HashSet.Lemmas: isEmpty / contains / mem basics (empty, congr, isEmpty characterisations) (18)

_scope: section@32_

- **isEmpty_emptyWithCapacity** [simp, grind =]: `… {c : Nat} : (Std.HashSet.emptyWithCapacity c).isEmpty = true`
- **isEmpty_empty** [simp, grind =]: `… : ∅.isEmpty = true`
- **isEmpty_insert** [simp, grind =]: `… {m : Std.HashSet α} [EquivBEq α] [LawfulHashable α] {a : α} : (m.insert a).isEmpty = false`
- **mem_iff_contains**: `… {m : Std.HashSet α} {a : α} : a ∈ m ↔ m.contains a = true`
- **contains_iff_mem** [simp, grind _=_]: `… {m : Std.HashSet α} {a : α} : m.contains a = true ↔ a ∈ m`
- **contains_eq_false_iff_not_mem** [attribute [simp] (l.1583)]: `… {m : Std.HashSet α} {k : α} : m.contains k = false ↔ ¬k ∈ m`
- **contains_congr**: `… {m : Std.HashSet α} [EquivBEq α] [LawfulHashable α] {a b : α} (hab : (a == b) = true) : m.contains a = m.contains b`
- **mem_congr**: `… {m : Std.HashSet α} [EquivBEq α] [LawfulHashable α] {a b : α} (hab : (a == b) = true) : a ∈ m ↔ b ∈ m`
- **contains_emptyWithCapacity** [simp, grind =, cbv_eval]: `… {a : α} {c : Nat} : (Std.HashSet.emptyWithCapacity c).contains a = false`
- **not_mem_emptyWithCapacity** [simp, grind ←]: `… {a : α} {c : Nat} : ¬a ∈ Std.HashSet.emptyWithCapacity c`
- **contains_empty** [simp, grind =]: `… {a : α} : ∅.contains a = false`
- **not_mem_empty** [simp]: `… {a : α} : ¬a ∈ ∅`
- **contains_of_isEmpty**: `… {m : Std.HashSet α} [EquivBEq α] [LawfulHashable α] {a : α} : m.isEmpty = true → m.contains a = false`
- **not_mem_of_isEmpty**: `… {m : Std.HashSet α} [EquivBEq α] [LawfulHashable α] {a : α} : m.isEmpty = true → ¬a ∈ m`
- **isEmpty_eq_false_iff_exists_contains_eq_true**: `… {m : Std.HashSet α} [EquivBEq α] [LawfulHashable α] : m.isEmpty = false ↔ ∃ a, m.contains a = true`
- **isEmpty_eq_false_iff_exists_mem**: `… {m : Std.HashSet α} [EquivBEq α] [LawfulHashable α] : m.isEmpty = false ↔ ∃ a, a ∈ m`
- **isEmpty_iff_forall_contains**: `… {m : Std.HashSet α} [EquivBEq α] [LawfulHashable α] : m.isEmpty = true ↔ ∀ (a : α), m.contains a = false`
- **isEmpty_iff_forall_not_mem**: `… {m : Std.HashSet α} [EquivBEq α] [LawfulHashable α] : m.isEmpty = true ↔ ∀ (a : α), ¬a ∈ m`

#### HashSet.Lemmas: insert: notation, contains, mem (11)

_scope: section@32_

- **insert_eq_insert** [simp]: `… {m : Std.HashSet α} {a : α} : insert a m = m.insert a`
- **singleton_eq_insert** [simp]: `… {a : α} : {a} = ∅.insert a`
- **contains_insert** [simp, grind =, cbv_eval]: `… {m : Std.HashSet α} [EquivBEq α] [LawfulHashable α] {k a : α} : (m.insert k).contains a = (k == a || m.contains a)`
- **mem_insert** [simp, grind =]: `… {m : Std.HashSet α} [EquivBEq α] [LawfulHashable α] {k a : α} : a ∈ m.insert k ↔ (k == a) = true ∨ a ∈ m`
- **contains_of_contains_insert**: `… {m : Std.HashSet α} [EquivBEq α] [LawfulHashable α] {k a : α} : (m.insert k).contains a = true → (k == a) = false → m.contains a = true`
- **mem_of_mem_insert**: `… {m : Std.HashSet α} [EquivBEq α] [LawfulHashable α] {k a : α} : a ∈ m.insert k → (k == a) = false → a ∈ m`
- **contains_of_contains_insert'**: `… {m : Std.HashSet α} [EquivBEq α] [LawfulHashable α] {k a : α} : (m.insert k).contains a = true → ¬((k == a) = true ∧ m.contains k = false) → m.contains a = true`
- **mem_of_mem_insert'**: `… {m : Std.HashSet α} [EquivBEq α] [LawfulHashable α] {k a : α} : a ∈ m.insert k → ¬((k == a) = true ∧ ¬k ∈ m) → a ∈ m`
- **contains_insert_self**: `… {m : Std.HashSet α} [EquivBEq α] [LawfulHashable α] {k : α} : (m.insert k).contains k = true`
- **mem_insert_self**: `… {m : Std.HashSet α} [EquivBEq α] [LawfulHashable α] {k : α} : k ∈ m.insert k`
- **mem_of_get_eq**: `… {m : Std.HashSet α} {k v : α} {w : k ∈ m} : m.get k w = v → k ∈ m`

#### HashSet.Lemmas: size; toList of empty; size of insert (8)

_scope: section@32_

- **size_emptyWithCapacity** [simp, grind =]: `… {c : Nat} : (Std.HashSet.emptyWithCapacity c).size = 0`
- **size_empty** [simp, grind =]: `… : ∅.size = 0`
- **isEmpty_eq_size_eq_zero**: `… {m : Std.HashSet α} : m.isEmpty = (m.size == 0)`
- **toList_emptyWithCapacity** [simp]: `… {c : Nat} : (Std.HashSet.emptyWithCapacity c).toList = []`
- **toList_empty** [simp]: `… : ∅.toList = []`
- **size_insert** [grind =]: `… {m : Std.HashSet α} [EquivBEq α] [LawfulHashable α] {k : α} : (m.insert k).size = if k ∈ m then m.size else m.size + 1`
- **size_le_size_insert**: `… {m : Std.HashSet α} [EquivBEq α] [LawfulHashable α] {k : α} : m.size ≤ (m.insert k).size`
- **size_insert_le**: `… {m : Std.HashSet α} [EquivBEq α] [LawfulHashable α] {k : α} : (m.insert k).size ≤ m.size + 1`

#### HashSet.Lemmas: erase: isEmpty, contains, mem, size (10)

_scope: section@32_

- **erase_emptyWithCapacity** [simp, grind =, cbv_eval]: `… {a : α} {c : Nat} : (Std.HashSet.emptyWithCapacity c).erase a = Std.HashSet.emptyWithCapacity c`
- **erase_empty** [simp, grind =]: `… {a : α} : ∅.erase a = ∅`
- **isEmpty_erase** [simp, grind =]: `… {m : Std.HashSet α} [EquivBEq α] [LawfulHashable α] {k : α} : (m.erase k).isEmpty = (m.isEmpty || m.size == 1 && m.contains k)`
- **contains_erase** [simp, grind =, cbv_eval]: `… {m : Std.HashSet α} [EquivBEq α] [LawfulHashable α] {k a : α} : (m.erase k).contains a = (!k == a && m.contains a)`
- **mem_erase** [simp, grind =]: `… {m : Std.HashSet α} [EquivBEq α] [LawfulHashable α] {k a : α} : a ∈ m.erase k ↔ (k == a) = false ∧ a ∈ m`
- **contains_of_contains_erase**: `… {m : Std.HashSet α} [EquivBEq α] [LawfulHashable α] {k a : α} : (m.erase k).contains a = true → m.contains a = true`
- **mem_of_mem_erase**: `… {m : Std.HashSet α} [EquivBEq α] [LawfulHashable α] {k a : α} : a ∈ m.erase k → a ∈ m`
- **size_erase** [grind =]: `… {m : Std.HashSet α} [EquivBEq α] [LawfulHashable α] {k : α} : (m.erase k).size = if k ∈ m then m.size - 1 else m.size`
- **size_erase_le**: `… {m : Std.HashSet α} [EquivBEq α] [LawfulHashable α] {k : α} : (m.erase k).size ≤ m.size`
- **size_le_size_erase**: `… {m : Std.HashSet α} [EquivBEq α] [LawfulHashable α] {k : α} : m.size ≤ (m.erase k).size + 1`

#### HashSet.Lemmas: get? (18)

_scope: section@32_

- **get?_emptyWithCapacity** [simp, grind =, cbv_eval]: `… {a : α} {c : Nat} : (Std.HashSet.emptyWithCapacity c).get? a = none`
- **get?_empty** [simp, grind =]: `… {a : α} : ∅.get? a = none`
- **get?_of_isEmpty**: `… {m : Std.HashSet α} [EquivBEq α] [LawfulHashable α] {a : α} : m.isEmpty = true → m.get? a = none`
- **get?_insert** [grind =, cbv_eval]: `… {m : Std.HashSet α} [EquivBEq α] [LawfulHashable α] {k a : α} : (m.insert k).get? a = if (k == a) = true ∧ ¬k ∈ m then some k else m.get? a`
- **contains_eq_isSome_get?**: `… {m : Std.HashSet α} [EquivBEq α] [LawfulHashable α] {a : α} : m.contains a = (m.get? a).isSome`
- **isSome_get?_eq_contains** [simp, grind =]: `… {m : Std.HashSet α} [EquivBEq α] [LawfulHashable α] {a : α} : (m.get? a).isSome = m.contains a`
- **mem_iff_isSome_get?**: `… {m : Std.HashSet α} [EquivBEq α] [LawfulHashable α] {a : α} : a ∈ m ↔ (m.get? a).isSome = true`
- **isSome_get?_iff_mem** [simp]: `… {m : Std.HashSet α} [EquivBEq α] [LawfulHashable α] {a : α} : (m.get? a).isSome = true ↔ a ∈ m`
- **get?_eq_some_iff**: `… {m : Std.HashSet α} [EquivBEq α] [LawfulHashable α] {k k' : α} : m.get? k = some k' ↔ ∃ h, m.get k h = k'`
- **mem_of_get?_eq_some**: `… {m : Std.HashSet α} [EquivBEq α] [LawfulHashable α] {k k' : α} (h : m.get? k = some k') : k' ∈ m`
- **get?_eq_none_of_contains_eq_false**: `… {m : Std.HashSet α} [EquivBEq α] [LawfulHashable α] {a : α} : m.contains a = false → m.get? a = none`
- **get?_eq_none**: `… {m : Std.HashSet α} [EquivBEq α] [LawfulHashable α] {a : α} : ¬a ∈ m → m.get? a = none`
- **get?_erase** [grind =, cbv_eval]: `… {m : Std.HashSet α} [EquivBEq α] [LawfulHashable α] {k a : α} : (m.erase k).get? a = if (k == a) = true then none else m.get? a`
- **get?_erase_self** [simp]: `… {m : Std.HashSet α} [EquivBEq α] [LawfulHashable α] {k : α} : (m.erase k).get? k = none`
- **get?_beq**: `… {m : Std.HashSet α} [EquivBEq α] [LawfulHashable α] {k : α} : Option.all (fun x => x == k) (m.get? k) = true`
- **get?_congr**: `… {m : Std.HashSet α} [EquivBEq α] [LawfulHashable α] {k k' : α} (h : (k == k') = true) : m.get? k = m.get? k'`
- **get?_eq_some_of_contains**: `… {m : Std.HashSet α} [LawfulBEq α] {k : α} (h : m.contains k = true) : m.get? k = some k`
- **get?_eq_some**: `… {m : Std.HashSet α} [LawfulBEq α] {k : α} (h : k ∈ m) : m.get? k = some k`

#### HashSet.Lemmas: get [also toList_insert_perm] (9)

_scope: section@32_

- **get_insert** [grind =]: `… {m : Std.HashSet α} [EquivBEq α] [LawfulHashable α] {k a : α} {h₁ : a ∈ m.insert k} : (m.insert k).get a h₁ = if h₂ : (k == a) = true ∧ ¬k ∈ m then k else m.get a ⋯`
- **toList_insert_perm**: `… {m : Std.HashSet α} [EquivBEq α] [LawfulHashable α] {k : α} : (m.insert k).toList.Perm (if k ∈ m then m.toList else k :: m.toList)`
- **get_erase** [simp, grind =]: `… {m : Std.HashSet α} [EquivBEq α] [LawfulHashable α] {k a : α} {h' : a ∈ m.erase k} : (m.erase k).get a h' = m.get a ⋯`
- **get?_eq_some_get**: `… {m : Std.HashSet α} [EquivBEq α] [LawfulHashable α] {a : α} (h' : a ∈ m) : m.get? a = some (m.get a h')`
- **get_eq_get_get?**: `… {m : Std.HashSet α} [EquivBEq α] [LawfulHashable α] {k : α} {h : k ∈ m} : m.get k h = (m.get? k).get ⋯`
- **get_get?** [grind =]: `… {m : Std.HashSet α} [EquivBEq α] [LawfulHashable α] {k : α} {h : (m.get? k).isSome = true} : (m.get? k).get h = m.get k ⋯`
- **get_beq**: `… {m : Std.HashSet α} [EquivBEq α] [LawfulHashable α] {k : α} (h : k ∈ m) : (m.get k h == k) = true`
- **get_congr**: `… {m : Std.HashSet α} [EquivBEq α] [LawfulHashable α] {k₁ k₂ : α} (h : (k₁ == k₂) = true) (h₁ : k₁ ∈ m) : m.get k₁ h₁ = m.get k₂ ⋯`
- **get_eq** [simp, grind =]: `… {m : Std.HashSet α} [LawfulBEq α] {k : α} (h : k ∈ m) : m.get k h = k`

#### HashSet.Lemmas: get! (15)

_scope: section@32_

- **get!_emptyWithCapacity** [simp, grind =, cbv_eval]: `… [Inhabited α] {a : α} {c : Nat} : (Std.HashSet.emptyWithCapacity c).get! a = default`
- **get!_empty** [simp, grind =]: `… [Inhabited α] {a : α} : ∅.get! a = default`
- **get!_of_isEmpty**: `… {m : Std.HashSet α} [Inhabited α] [EquivBEq α] [LawfulHashable α] {a : α} : m.isEmpty = true → m.get! a = default`
- **get!_insert** [grind =, cbv_eval]: `… {m : Std.HashSet α} [Inhabited α] [EquivBEq α] [LawfulHashable α] {k a : α} : (m.insert k).get! a = if (k == a) = true ∧ ¬k ∈ m then k else m.get! a`
- **get!_eq_default_of_contains_eq_false**: `… {m : Std.HashSet α} [Inhabited α] [EquivBEq α] [LawfulHashable α] {a : α} : m.contains a = false → m.get! a = default`
- **get!_eq_default**: `… {m : Std.HashSet α} [Inhabited α] [EquivBEq α] [LawfulHashable α] {a : α} : ¬a ∈ m → m.get! a = default`
- **get!_erase** [grind =, cbv_eval]: `… {m : Std.HashSet α} [Inhabited α] [EquivBEq α] [LawfulHashable α] {k a : α} : (m.erase k).get! a = if (k == a) = true then default else m.get! a`
- **get!_erase_self** [simp]: `… {m : Std.HashSet α} [Inhabited α] [EquivBEq α] [LawfulHashable α] {k : α} : (m.erase k).get! k = default`
- **get?_eq_some_get!_of_contains**: `… {m : Std.HashSet α} [EquivBEq α] [LawfulHashable α] [Inhabited α] {a : α} : m.contains a = true → m.get? a = some (m.get! a)`
- **get?_eq_some_get!**: `… {m : Std.HashSet α} [EquivBEq α] [LawfulHashable α] [Inhabited α] {a : α} : a ∈ m → m.get? a = some (m.get! a)`
- **get!_eq_get!_get?**: `… {m : Std.HashSet α} [EquivBEq α] [LawfulHashable α] [Inhabited α] {a : α} : m.get! a = (m.get? a).get!`
- **get_eq_get!**: `… {m : Std.HashSet α} [EquivBEq α] [LawfulHashable α] [Inhabited α] {a : α} {h' : a ∈ m} : m.get a h' = m.get! a`
- **get!_congr**: `… {m : Std.HashSet α} [EquivBEq α] [LawfulHashable α] [Inhabited α] {k k' : α} (h : (k == k') = true) : m.get! k = m.get! k'`
- **get!_eq_of_contains**: `… {m : Std.HashSet α} [LawfulBEq α] [Inhabited α] {k : α} (h : m.contains k = true) : m.get! k = k`
- **get!_eq_of_mem**: `… {m : Std.HashSet α} [LawfulBEq α] [Inhabited α] {k : α} (h : k ∈ m) : m.get! k = k`

#### HashSet.Lemmas: getD (16)

_scope: section@32_

- **getD_emptyWithCapacity** [simp, grind =, cbv_eval]: `… {a fallback : α} {c : Nat} : (Std.HashSet.emptyWithCapacity c).getD a fallback = fallback`
- **getD_empty** [simp, grind =]: `… {a fallback : α} : ∅.getD a fallback = fallback`
- **getD_of_isEmpty**: `… {m : Std.HashSet α} [EquivBEq α] [LawfulHashable α] {a fallback : α} : m.isEmpty = true → m.getD a fallback = fallback`
- **getD_insert** [grind =, cbv_eval]: `… {m : Std.HashSet α} [EquivBEq α] [LawfulHashable α] {k a fallback : α} : (m.insert k).getD a fallback = if (k == a) = true ∧ ¬k ∈ m then k else m.getD a fallback`
- **getD_eq_fallback_of_contains_eq_false**: `… {m : Std.HashSet α} [EquivBEq α] [LawfulHashable α] {a fallback : α} : m.contains a = false → m.getD a fallback = fallback`
- **getD_eq_fallback**: `… {m : Std.HashSet α} [EquivBEq α] [LawfulHashable α] {a fallback : α} : ¬a ∈ m → m.getD a fallback = fallback`
- **getD_erase** [grind =, cbv_eval]: `… {m : Std.HashSet α} [EquivBEq α] [LawfulHashable α] {k a fallback : α} : (m.erase k).getD a fallback = if (k == a) = true then fallback else m.getD a fallback`
- **getD_erase_self** [simp]: `… {m : Std.HashSet α} [EquivBEq α] [LawfulHashable α] {k fallback : α} : (m.erase k).getD k fallback = fallback`
- **get?_eq_some_getD_of_contains**: `… {m : Std.HashSet α} [EquivBEq α] [LawfulHashable α] {a fallback : α} : m.contains a = true → m.get? a = some (m.getD a fallback)`
- **get?_eq_some_getD**: `… {m : Std.HashSet α} [EquivBEq α] [LawfulHashable α] {a fallback : α} : a ∈ m → m.get? a = some (m.getD a fallback)`
- **getD_eq_getD_get?**: `… {m : Std.HashSet α} [EquivBEq α] [LawfulHashable α] {a fallback : α} : m.getD a fallback = (m.get? a).getD fallback`
- **get_eq_getD**: `… {m : Std.HashSet α} [EquivBEq α] [LawfulHashable α] {a fallback : α} {h' : a ∈ m} : m.get a h' = m.getD a fallback`
- **get!_eq_getD_default**: `… {m : Std.HashSet α} [EquivBEq α] [LawfulHashable α] [Inhabited α] {a : α} : m.get! a = m.getD a default`
- **getD_congr**: `… {m : Std.HashSet α} [EquivBEq α] [LawfulHashable α] {k k' fallback : α} (h : (k == k') = true) : m.getD k fallback = m.getD k' fallback`
- **getD_eq_of_contains**: `… {m : Std.HashSet α} [LawfulBEq α] {k fallback : α} (h : m.contains k = true) : m.getD k fallback = k`
- **getD_eq_of_mem**: `… {m : Std.HashSet α} [LawfulBEq α] {k fallback : α} (h : k ∈ m) : m.getD k fallback = k`

#### HashSet.Lemmas: containsThenInsert (2)

_scope: section@32_

- **containsThenInsert_fst** [simp, grind =]: `… {m : Std.HashSet α} {k : α} : (m.containsThenInsert k).fst = m.contains k`
- **containsThenInsert_snd** [simp, grind =]: `… {m : Std.HashSet α} {k : α} : (m.containsThenInsert k).snd = m.insert k`

#### HashSet.Lemmas: toList / toArray (14)

_scope: section@32_

- **length_toList** [simp, grind =]: `… {m : Std.HashSet α} [EquivBEq α] [LawfulHashable α] : m.toList.length = m.size`
- **isEmpty_toList** [simp, grind =]: `… {m : Std.HashSet α} [EquivBEq α] [LawfulHashable α] : m.toList.isEmpty = m.isEmpty`
- **contains_toList** [simp, grind =]: `… {m : Std.HashSet α} [EquivBEq α] [LawfulHashable α] {k : α} : m.toList.contains k = m.contains k`
- **mem_toList** [simp, grind =]: `… {m : Std.HashSet α} [LawfulBEq α] {k : α} : k ∈ m.toList ↔ k ∈ m`
- **mem_of_mem_toList**: `… {m : Std.HashSet α} [EquivBEq α] [LawfulHashable α] {k : α} : k ∈ m.toList → k ∈ m`
- **distinct_toList**: `… {m : Std.HashSet α} [EquivBEq α] [LawfulHashable α] : List.Pairwise (fun a b => (a == b) = false) m.toList`
- **toArray_toList** [simp]: `… {m : Std.HashSet α} : m.toList.toArray = m.toArray`
- **toList_toArray** [simp]: `… {m : Std.HashSet α} : m.toArray.toList = m.toList`
- **size_toArray** [simp]: `… {m : Std.HashSet α} [EquivBEq α] [LawfulHashable α] : m.toArray.size = m.size`
- **isEmpty_toArray** [simp]: `… {m : Std.HashSet α} [EquivBEq α] [LawfulHashable α] : m.toArray.isEmpty = m.isEmpty`
- **contains_toArray** [simp]: `… {m : Std.HashSet α} [EquivBEq α] [LawfulHashable α] {k : α} : m.toArray.contains k = m.contains k`
- **mem_toArray** [simp]: `… {m : Std.HashSet α} [LawfulBEq α] {k : α} : k ∈ m.toArray ↔ k ∈ m`
- **forall_mem_toArray_iff_forall_mem_get**: `… {m : Std.HashSet α} [EquivBEq α] [LawfulHashable α] {p : α → Prop} : (∀ (k : α), k ∈ m.toArray → p k) ↔ ∀ (k : α) (h : k ∈ m), p (m.get k h)`
- **contains_of_mem_toArray**: `… {m : Std.HashSet α} [EquivBEq α] [LawfulHashable α] {k : α} (h' : k ∈ m.toArray) : m.contains k = true`

#### HashSet.Lemmas: monadic: fold / foldM / forM / forIn (11)

_scope: section@32 › section monadic_

- **foldM_eq_foldlM_toList**: `… {m : Std.HashSet α} {δ : Type v} {m' : Type v → Type w} [Monad m'] [LawfulMonad m'] {f : δ → α → m' δ} {init : δ} : Std.HashSet.foldM f init m = List.foldlM f init m.toList`
- **fold_eq_foldl_toList**: `… {m : Std.HashSet α} {δ : Type v} {f : δ → α → δ} {init : δ} : Std.HashSet.fold f init m = List.foldl f init m.toList`
- **forM_eq_forM** [simp, grind =]: `… {m : Std.HashSet α} {m' : Type v → Type w} [Monad m'] [LawfulMonad m'] {f : α → m' PUnit} : Std.HashSet.forM f m = forM m f`
- **forM_eq_forM_toList**: `… {m : Std.HashSet α} {m' : Type v → Type w} [Monad m'] [LawfulMonad m'] {f : α → m' PUnit} : forM m f = forM m.toList f`
- **forIn_eq_forIn** [simp, grind =]: `… {m : Std.HashSet α} {δ : Type v} {m' : Type v → Type w} [Monad m'] [LawfulMonad m'] {f : α → δ → m' (ForInStep δ)} {init : δ} : forIn m init f = forIn m init f`
- **forIn_eq_forIn_toList**: `… {m : Std.HashSet α} {δ : Type v} {m' : Type v → Type w} [Monad m'] [LawfulMonad m'] {f : α → δ → m' (ForInStep δ)} {init : δ} : forIn m init f = forIn m.toList init f`
- **forIn_toList** [simp, grind =]: `… (c : Std.HashSet α) : ForIn.toList c = c.toList`
- **foldM_eq_foldlM_toArray**: `… {m : Std.HashSet α} {δ : Type v} {m' : Type v → Type w} [Monad m'] [LawfulMonad m'] {f : δ → α → m' δ} {init : δ} : Std.HashSet.foldM (fun d a => f d a) init m = Array.foldlM f init m.toArray`
- **fold_eq_foldl_toArray**: `… {m : Std.HashSet α} {δ : Type v} {f : δ → α → δ} {init : δ} : Std.HashSet.fold (fun d a => f d a) init m = Array.foldl f init m.toArray`
- **forM_eq_forM_toArray**: `… {m : Std.HashSet α} {m' : Type v → Type w} [Monad m'] [LawfulMonad m'] {f : α → m' PUnit} : Std.HashSet.forM (fun a => f a) m = Array.forM f m.toArray`
- **forIn_eq_forIn_toArray**: `… {m : Std.HashSet α} {δ : Type v} {m' : Type v → Type w} [Monad m'] [LawfulMonad m'] {f : α → δ → m' (ForInStep δ)} {init : δ} : Std.HashSet.forIn (fun a d => f a d) init m = forIn m.toArray init f`

#### HashSet.Lemmas: all / any (12)

_scope: section@32_

- **all_eq_not_any_not**: `… {m : Std.HashSet α} {p : α → Bool} : m.all p = !m.any fun a => !p a`
- **any_eq_not_all_not**: `… {m : Std.HashSet α} {p : α → Bool} : m.any p = !m.all fun a => !p a`
- **any_toList** [simp]: `… {m : Std.HashSet α} [LawfulHashable α] [EquivBEq α] {p : α → Bool} : m.toList.any p = m.any p`
- **any_eq_true_iff_exists_mem_get**: `… {m : Std.HashSet α} [LawfulHashable α] [EquivBEq α] {p : α → Bool} : m.any p = true ↔ ∃ a h, p (m.get a h) = true`
- **any_eq_true_iff_exists_mem**: `… {m : Std.HashSet α} [LawfulBEq α] {p : α → Bool} : m.any p = true ↔ ∃ a, a ∈ m ∧ p a = true`
- **any_eq_false_iff_forall_mem_get**: `… {m : Std.HashSet α} [LawfulHashable α] [EquivBEq α] {p : α → Bool} : m.any p = false ↔ ∀ (a : α) (h : a ∈ m), p (m.get a h) = false`
- **any_eq_false_iff_forall_mem**: `… {m : Std.HashSet α} [LawfulBEq α] {p : α → Bool} : m.any p = false ↔ ∀ (a : α), a ∈ m → p a = false`
- **all_toList** [simp]: `… {m : Std.HashSet α} [LawfulHashable α] [EquivBEq α] {p : α → Bool} : m.toList.all p = m.all p`
- **all_eq_true_iff_forall_mem_get**: `… {m : Std.HashSet α} [EquivBEq α] [LawfulHashable α] {p : α → Bool} : m.all p = true ↔ ∀ (a : α) (h : a ∈ m), p (m.get a h) = true`
- **all_eq_true_iff_forall_mem**: `… {m : Std.HashSet α} [LawfulBEq α] {p : α → Bool} : m.all p = true ↔ ∀ (a : α), a ∈ m → p a = true`
- **all_eq_false_iff_exists_mem_get**: `… {m : Std.HashSet α} [EquivBEq α] [LawfulHashable α] {p : α → Bool} : m.all p = false ↔ ∃ a h, p (m.get a h) = false`
- **all_eq_false_iff_exists_mem**: `… {m : Std.HashSet α} [LawfulBEq α] {p : α → Bool} : m.all p = false ↔ ∃ a, a ∈ m ∧ p a = false`

#### HashSet.Lemmas: insertMany (26)

_scope: section@32_

- **insertMany_nil** [simp, grind =, cbv_eval]: `… {m : Std.HashSet α} : m.insertMany [] = m`
- **insertMany_list_singleton** [simp, grind =]: `… {m : Std.HashSet α} {k : α} : m.insertMany [k] = m.insert k`
- **insertMany_cons** [grind _=_, cbv_eval]: `… {m : Std.HashSet α} {l : List α} {k : α} : m.insertMany (k :: l) = (m.insert k).insertMany l`
- **insertMany_append** [grind _=_]: `… {m : Std.HashSet α} {l₁ l₂ : List α} : m.insertMany (l₁ ++ l₂) = (m.insertMany l₁).insertMany l₂`
- **insertMany_ind** [elab_as_elim]: `… {ρ : Type v} [ForIn Id ρ α] {motive : Std.HashSet α → Prop} (m : Std.HashSet α) {l : ρ} (init : motive m) (insert : ∀ (m : Std.HashSet α) (a : α), motive m → motive (m.insert a)) : motive (m.insertMany l)`
- **contains_insertMany_list** [simp, grind =]: `… {m : Std.HashSet α} [EquivBEq α] [LawfulHashable α] {l : List α} {k : α} : (m.insertMany l).contains k = (m.contains k || l.contains k)`
- **mem_insertMany_list** [simp, grind =]: `… {m : Std.HashSet α} [EquivBEq α] [LawfulHashable α] {l : List α} {k : α} : k ∈ m.insertMany l ↔ k ∈ m ∨ l.contains k = true`
- **mem_of_mem_insertMany_list**: `… {m : Std.HashSet α} [EquivBEq α] [LawfulHashable α] {l : List α} {k : α} (contains_eq_false : l.contains k = false) : k ∈ m.insertMany l → k ∈ m`
- **mem_insertMany_of_mem**: `… {m : Std.HashSet α} {ρ : Type v} [ForIn Id ρ α] [EquivBEq α] [LawfulHashable α] {l : ρ} {k : α} : k ∈ m → k ∈ m.insertMany l`
- **get?_insertMany_list_of_not_mem_of_contains_eq_false**: `… {m : Std.HashSet α} [EquivBEq α] [LawfulHashable α] {l : List α} {k : α} (not_mem : ¬k ∈ m) (contains_eq_false : l.contains k = false) : (m.insertMany l).get? k = none`
- **get?_insertMany_list_of_not_mem_of_mem**: `… {m : Std.HashSet α} [EquivBEq α] [LawfulHashable α] {l : List α} {k k' : α} (k_beq : (k == k') = true) (not_mem : ¬k ∈ m) (distinct : List.Pairwise (fun a b => (a == b) = false) l) (mem : k ∈ l) : (m.insertMany l).get? k' = some k`
- **get?_insertMany_list_of_mem**: `… {m : Std.HashSet α} [EquivBEq α] [LawfulHashable α] {l : List α} {k : α} (mem : k ∈ m) : (m.insertMany l).get? k = m.get? k`
- **get_insertMany_list_of_not_mem_of_mem**: `… {m : Std.HashSet α} [EquivBEq α] [LawfulHashable α] {l : List α} {k k' : α} (k_beq : (k == k') = true) (not_mem : ¬k ∈ m) (distinct : List.Pairwise (fun a b => (a == b) = false) l) (mem : k ∈ l) {h : k' ∈ m.insertMany l} : (m.insertMany l).get k' h = k`
- **get_insertMany_list_of_mem**: `… {m : Std.HashSet α} [EquivBEq α] [LawfulHashable α] {l : List α} {k : α} (mem : k ∈ m) {h : k ∈ m.insertMany l} : (m.insertMany l).get k h = m.get k mem`
- **get!_insertMany_list_of_not_mem_of_contains_eq_false**: `… {m : Std.HashSet α} [EquivBEq α] [LawfulHashable α] [Inhabited α] {l : List α} {k : α} (not_mem : ¬k ∈ m) (contains_eq_false : l.contains k = false) : (m.insertMany l).get! k = default`
- **get!_insertMany_list_of_not_mem_of_mem**: `… {m : Std.HashSet α} [EquivBEq α] [LawfulHashable α] [Inhabited α] {l : List α} {k k' : α} (k_beq : (k == k') = true) (not_mem : ¬k ∈ m) (distinct : List.Pairwise (fun a b => (a == b) = false) l) (mem : k ∈ l) : (m.insertMany l).get! k' = k`
- **get!_insertMany_list_of_mem**: `… {m : Std.HashSet α} [EquivBEq α] [LawfulHashable α] [Inhabited α] {l : List α} {k : α} (mem : k ∈ m) : (m.insertMany l).get! k = m.get! k`
- **getD_insertMany_list_of_not_mem_of_contains_eq_false**: `… {m : Std.HashSet α} [EquivBEq α] [LawfulHashable α] {l : List α} {k fallback : α} (not_mem : ¬k ∈ m) (contains_eq_false : l.contains k = false) : (m.insertMany l).getD k fallback = fallback`
- **getD_insertMany_list_of_not_mem_of_mem**: `… {m : Std.HashSet α} [EquivBEq α] [LawfulHashable α] {l : List α} {k k' fallback : α} (k_beq : (k == k') = true) (not_mem : ¬k ∈ m) (distinct : List.Pairwise (fun a b => (a == b) = false) l) (mem : k ∈ l) : (m.insertMany l).getD k' fallback = k`
- **getD_insertMany_list_of_mem**: `… {m : Std.HashSet α} [EquivBEq α] [LawfulHashable α] {l : List α} {k fallback : α} (mem : k ∈ m) : (m.insertMany l).getD k fallback = m.getD k fallback`
- **size_insertMany_list**: `… {m : Std.HashSet α} [EquivBEq α] [LawfulHashable α] {l : List α} (distinct : List.Pairwise (fun a b => (a == b) = false) l) : (∀ (a : α), a ∈ m → l.contains a = false) → (m.insertMany l).size = m.size + l.length`
- **size_le_size_insertMany_list**: `… {m : Std.HashSet α} [EquivBEq α] [LawfulHashable α] {l : List α} : m.size ≤ (m.insertMany l).size`
- **size_le_size_insertMany** [grind_pattern (insertMany m l).size (l.779)]: `… {m : Std.HashSet α} {ρ : Type v} [ForIn Id ρ α] [EquivBEq α] [LawfulHashable α] {l : ρ} : m.size ≤ (m.insertMany l).size`
- **size_insertMany_list_le** [grind_pattern (insertMany m l).size (l.786)]: `… {m : Std.HashSet α} [EquivBEq α] [LawfulHashable α] {l : List α} : (m.insertMany l).size ≤ m.size + l.length`
- **isEmpty_insertMany_list** [simp, grind =]: `… {m : Std.HashSet α} [EquivBEq α] [LawfulHashable α] {l : List α} : (m.insertMany l).isEmpty = (m.isEmpty && l.isEmpty)`
- **isEmpty_of_isEmpty_insertMany**: `… {m : Std.HashSet α} {ρ : Type v} [ForIn Id ρ α] [EquivBEq α] [LawfulHashable α] {l : ρ} : (m.insertMany l).isEmpty = true → m.isEmpty = true`

#### HashSet.Lemmas: BEq vs Equiv (4)

_scope: section@800_

- **Equiv.beq**: `… {m₁ m₂ : Std.HashSet α} [EquivBEq α] [LawfulHashable α] (h : m₁.Equiv m₂) : (m₁ == m₂) = true`
- **equiv_of_beq**: `… {m₁ m₂ : Std.HashSet α} [LawfulBEq α] (h : (m₁ == m₂) = true) : m₁.Equiv m₂`
- **beq_iff_equiv**: `… {m₁ m₂ : Std.HashSet α} [LawfulBEq α] : (m₁ == m₂) = true ↔ m₁.Equiv m₂`
- **Equiv.beq_congr**: `… {m₁ m₂ : Std.HashSet α} [EquivBEq α] [LawfulHashable α] {m₃ m₄ : Std.HashSet α} (h₁ : m₁.Equiv m₃) (h₂ : m₂.Equiv m₄) : (m₁ == m₂) = (m₃ == m₄)`

#### HashSet.Lemmas: Union (27)

_scope: section Union_; subheadings: contains (1), mem (5), Equiv (3), get? (3), get (3), getD (3), get! (3), size (4), isEmpty (1)

- **union_eq** [simp]: `… {m₁ m₂ : Std.HashSet α} : m₁.union m₂ = m₁ ∪ m₂`
- **contains_union** [simp] {contains}: `… {m₁ m₂ : Std.HashSet α} [EquivBEq α] [LawfulHashable α] {k : α} : (m₁ ∪ m₂).contains k = (m₁.contains k || m₂.contains k)`
- **mem_union_of_left** {mem}: `… {m₁ m₂ : Std.HashSet α} [EquivBEq α] [LawfulHashable α] {k : α} : k ∈ m₁ → k ∈ m₁ ∪ m₂`
- **mem_union_of_right** {mem}: `… {m₁ m₂ : Std.HashSet α} [EquivBEq α] [LawfulHashable α] {k : α} : k ∈ m₂ → k ∈ m₁ ∪ m₂`
- **mem_union_iff** [simp] {mem}: `… {m₁ m₂ : Std.HashSet α} [EquivBEq α] [LawfulHashable α] {k : α} : (m₁ ∪ m₂).contains k = true ↔ m₁.contains k = true ∨ m₂.contains k = true`
- **mem_of_mem_union_of_not_mem_right** {mem}: `… {m₁ m₂ : Std.HashSet α} [EquivBEq α] [LawfulHashable α] {k : α} : k ∈ m₁ ∪ m₂ → ¬k ∈ m₂ → k ∈ m₁`
- **mem_of_mem_union_of_not_mem_left** {mem}: `… {m₁ m₂ : Std.HashSet α} [EquivBEq α] [LawfulHashable α] {k : α} : k ∈ m₁ ∪ m₂ → ¬k ∈ m₁ → k ∈ m₂`
- **Equiv.union_left** {Equiv}: `… {m₁ m₂ m₃ : Std.HashSet α} [EquivBEq α] [LawfulHashable α] (equiv : m₁.Equiv m₂) : (m₁ ∪ m₃).Equiv (m₂ ∪ m₃)`
- **Equiv.union_right** {Equiv}: `… {m₁ m₂ m₃ : Std.HashSet α} [EquivBEq α] [LawfulHashable α] (equiv : m₂.Equiv m₃) : (m₁ ∪ m₂).Equiv (m₁ ∪ m₃)`
- **Equiv.union_congr** {Equiv}: `… {m₁ m₂ m₃ m₄ : Std.HashSet α} [EquivBEq α] [LawfulHashable α] (equiv₁ : m₁.Equiv m₃) (equiv₂ : m₂.Equiv m₄) : (m₁ ∪ m₂).Equiv (m₃ ∪ m₄)`
- **get?_union** {get?}: `… {m₁ m₂ : Std.HashSet α} [EquivBEq α] [LawfulHashable α] {k : α} : (m₁ ∪ m₂).get? k = (m₂.get? k).or (m₁.get? k)`
- **get?_union_of_not_mem_left** {get?}: `… {m₁ m₂ : Std.HashSet α} [EquivBEq α] [LawfulHashable α] {k : α} (not_mem : ¬k ∈ m₁) : (m₁ ∪ m₂).get? k = m₂.get? k`
- **get?_union_of_not_mem_right** {get?}: `… {m₁ m₂ : Std.HashSet α} [EquivBEq α] [LawfulHashable α] {k : α} (not_mem : ¬k ∈ m₂) : (m₁ ∪ m₂).get? k = m₁.get? k`
- **get_union_of_mem_right** {get}: `… {m₁ m₂ : Std.HashSet α} [EquivBEq α] [LawfulHashable α] {k : α} (mem : k ∈ m₂) : (m₁ ∪ m₂).get k ⋯ = m₂.get k mem`
- **get_union_of_not_mem_left** {get}: `… {m₁ m₂ : Std.HashSet α} [EquivBEq α] [LawfulHashable α] {k : α} (not_mem : ¬k ∈ m₁) {h' : k ∈ m₁ ∪ m₂} : (m₁ ∪ m₂).get k h' = m₂.get k ⋯`
- **get_union_of_not_mem_right** {get}: `… {m₁ m₂ : Std.HashSet α} [EquivBEq α] [LawfulHashable α] {k : α} (not_mem : ¬k ∈ m₂) {h' : k ∈ m₁ ∪ m₂} : (m₁ ∪ m₂).get k h' = m₁.get k ⋯`
- **getD_union** {getD}: `… {m₁ m₂ : Std.HashSet α} [EquivBEq α] [LawfulHashable α] {k fallback : α} : (m₁ ∪ m₂).getD k fallback = m₂.getD k (m₁.getD k fallback)`
- **getD_union_of_not_mem_left** {getD}: `… {m₁ m₂ : Std.HashSet α} [EquivBEq α] [LawfulHashable α] {k fallback : α} (not_mem : ¬k ∈ m₁) : (m₁ ∪ m₂).getD k fallback = m₂.getD k fallback`
- **getD_union_of_not_mem_right** {getD}: `… {m₁ m₂ : Std.HashSet α} [EquivBEq α] [LawfulHashable α] {k fallback : α} (not_mem : ¬k ∈ m₂) : (m₁ ∪ m₂).getD k fallback = m₁.getD k fallback`
- **get!_union** {get!}: `… {m₁ m₂ : Std.HashSet α} [EquivBEq α] [LawfulHashable α] [Inhabited α] {k : α} : (m₁ ∪ m₂).get! k = m₂.getD k (m₁.get! k)`
- **get!_union_of_not_mem_left** {get!}: `… {m₁ m₂ : Std.HashSet α} [Inhabited α] [EquivBEq α] [LawfulHashable α] {k : α} (not_mem : ¬k ∈ m₁) : (m₁ ∪ m₂).get! k = m₂.get! k`
- **get!_union_of_not_mem_right** {get!}: `… {m₁ m₂ : Std.HashSet α} [Inhabited α] [EquivBEq α] [LawfulHashable α] {k : α} (not_mem : ¬k ∈ m₂) : (m₁ ∪ m₂).get! k = m₁.get! k`
- **size_union_of_not_mem** {size}: `… {m₁ m₂ : Std.HashSet α} [EquivBEq α] [LawfulHashable α] : (∀ (a : α), a ∈ m₁ → ¬a ∈ m₂) → (m₁ ∪ m₂).size = m₁.size + m₂.size`
- **size_left_le_size_union** {size}: `… {m₁ m₂ : Std.HashSet α} [EquivBEq α] [LawfulHashable α] : m₁.size ≤ (m₁ ∪ m₂).size`
- **size_right_le_size_union** {size}: `… {m₁ m₂ : Std.HashSet α} [EquivBEq α] [LawfulHashable α] : m₂.size ≤ (m₁ ∪ m₂).size`
- **size_union_le_size_add_size** {size}: `… {m₁ m₂ : Std.HashSet α} [EquivBEq α] [LawfulHashable α] : (m₁ ∪ m₂).size ≤ m₁.size + m₂.size`
- **isEmpty_union** [simp] {isEmpty}: `… {m₁ m₂ : Std.HashSet α} [EquivBEq α] [LawfulHashable α] : (m₁ ∪ m₂).isEmpty = (m₁.isEmpty && m₂.isEmpty)`

#### HashSet.Lemmas: Inter (30)

_scope: section Inter_; subheadings: contains (1), mem (3), Equiv (3), get? (4), get (1), getD (4), get! (4), size (5), isEmpty (4)

- **inter_eq** [simp]: `… {m₁ m₂ : Std.HashSet α} : m₁.inter m₂ = m₁ ∩ m₂`
- **contains_inter** [simp] {contains}: `… {m₁ m₂ : Std.HashSet α} [EquivBEq α] [LawfulHashable α] {k : α} : (m₁ ∩ m₂).contains k = (m₁.contains k && m₂.contains k)`
- **mem_inter_iff** [simp] {mem}: `… {m₁ m₂ : Std.HashSet α} [EquivBEq α] [LawfulHashable α] {k : α} : (m₁ ∩ m₂).contains k = true ↔ m₁.contains k = true ∧ m₂.contains k = true`
- **not_mem_inter_of_not_mem_left** {mem}: `… {m₁ m₂ : Std.HashSet α} [EquivBEq α] [LawfulHashable α] {k : α} (not_mem : ¬k ∈ m₁) : ¬k ∈ m₁ ∩ m₂`
- **not_mem_inter_of_not_mem_right** {mem}: `… {m₁ m₂ : Std.HashSet α} [EquivBEq α] [LawfulHashable α] {k : α} (not_mem : ¬k ∈ m₂) : ¬k ∈ m₁ ∩ m₂`
- **Equiv.inter_left** {Equiv}: `… {m₁ m₂ m₃ : Std.HashSet α} [EquivBEq α] [LawfulHashable α] (equiv : m₁.Equiv m₂) : (m₁ ∩ m₃).Equiv (m₂ ∩ m₃)`
- **Equiv.inter_right** {Equiv}: `… {m₁ m₂ m₃ : Std.HashSet α} [EquivBEq α] [LawfulHashable α] (equiv : m₂.Equiv m₃) : (m₁ ∩ m₂).Equiv (m₁ ∩ m₃)`
- **Equiv.inter_congr** {Equiv}: `… {m₁ m₂ m₃ m₄ : Std.HashSet α} [EquivBEq α] [LawfulHashable α] (equiv₁ : m₁.Equiv m₃) (equiv₂ : m₂.Equiv m₄) : (m₁ ∩ m₂).Equiv (m₃ ∩ m₄)`
- **get?_inter** {get?}: `… {m₁ m₂ : Std.HashSet α} [EquivBEq α] [LawfulHashable α] {k : α} : (m₁ ∩ m₂).get? k = if k ∈ m₂ then m₁.get? k else none`
- **get?_inter_of_mem_right** {get?}: `… {m₁ m₂ : Std.HashSet α} [EquivBEq α] [LawfulHashable α] {k : α} (mem : k ∈ m₂) : (m₁ ∩ m₂).get? k = m₁.get? k`
- **get?_inter_of_not_mem_left** {get?}: `… {m₁ m₂ : Std.HashSet α} [EquivBEq α] [LawfulHashable α] {k : α} (not_mem : ¬k ∈ m₁) : (m₁ ∩ m₂).get? k = none`
- **get?_inter_of_not_mem_right** {get?}: `… {m₁ m₂ : Std.HashSet α} [EquivBEq α] [LawfulHashable α] {k : α} (not_mem : ¬k ∈ m₂) : (m₁ ∩ m₂).get? k = none`
- **get_inter** [simp] {get}: `… {m₁ m₂ : Std.HashSet α} [EquivBEq α] [LawfulHashable α] {k : α} {h_mem : k ∈ m₁ ∩ m₂} : (m₁ ∩ m₂).get k h_mem = m₁.get k ⋯`
- **getD_inter** {getD}: `… {m₁ m₂ : Std.HashSet α} [EquivBEq α] [LawfulHashable α] {k fallback : α} : (m₁ ∩ m₂).getD k fallback = if k ∈ m₂ then m₁.getD k fallback else fallback`
- **getD_inter_of_mem_right** {getD}: `… {m₁ m₂ : Std.HashSet α} [EquivBEq α] [LawfulHashable α] {k fallback : α} (mem : k ∈ m₂) : (m₁ ∩ m₂).getD k fallback = m₁.getD k fallback`
- **getD_inter_of_not_mem_right** {getD}: `… {m₁ m₂ : Std.HashSet α} [EquivBEq α] [LawfulHashable α] {k fallback : α} (not_mem : ¬k ∈ m₂) : (m₁ ∩ m₂).getD k fallback = fallback`
- **getD_inter_of_not_mem_left** {getD}: `… {m₁ m₂ : Std.HashSet α} [EquivBEq α] [LawfulHashable α] {k fallback : α} (not_mem : ¬k ∈ m₁) : (m₁ ∩ m₂).getD k fallback = fallback`
- **get!_inter** {get!}: `… {m₁ m₂ : Std.HashSet α} [EquivBEq α] [LawfulHashable α] [Inhabited α] {k : α} : (m₁ ∩ m₂).get! k = if k ∈ m₂ then m₁.get! k else default`
- **get!_inter_of_mem_right** {get!}: `… {m₁ m₂ : Std.HashSet α} [EquivBEq α] [LawfulHashable α] [Inhabited α] {k : α} (mem : k ∈ m₂) : (m₁ ∩ m₂).get! k = m₁.get! k`
- **get!_inter_of_not_mem_right** {get!}: `… {m₁ m₂ : Std.HashSet α} [EquivBEq α] [LawfulHashable α] [Inhabited α] {k : α} (not_mem : ¬k ∈ m₂) : (m₁ ∩ m₂).get! k = default`
- **get!_inter_of_not_mem_left** {get!}: `… {m₁ m₂ : Std.HashSet α} [EquivBEq α] [LawfulHashable α] [Inhabited α] {k : α} (not_mem : ¬k ∈ m₁) : (m₁ ∩ m₂).get! k = default`
- **size_inter_le_size_left** {size}: `… {m₁ m₂ : Std.HashSet α} [EquivBEq α] [LawfulHashable α] : (m₁ ∩ m₂).size ≤ m₁.size`
- **size_inter_le_size_right** {size}: `… {m₁ m₂ : Std.HashSet α} [EquivBEq α] [LawfulHashable α] : (m₁ ∩ m₂).size ≤ m₂.size`
- **size_inter_eq_size_left** {size}: `… {m₁ m₂ : Std.HashSet α} [EquivBEq α] [LawfulHashable α] (h : ∀ (a : α), a ∈ m₁ → a ∈ m₂) : (m₁ ∩ m₂).size = m₁.size`
- **size_inter_eq_size_right** {size}: `… {m₁ m₂ : Std.HashSet α} [EquivBEq α] [LawfulHashable α] (h : ∀ (a : α), a ∈ m₂ → a ∈ m₁) : (m₁ ∩ m₂).size = m₂.size`
- **size_add_size_eq_size_union_add_size_inter** {size}: `… {m₁ m₂ : Std.HashSet α} [EquivBEq α] [LawfulHashable α] : m₁.size + m₂.size = (m₁ ∪ m₂).size + (m₁ ∩ m₂).size`
- **isEmpty_inter_left** [simp] {isEmpty}: `… {m₁ m₂ : Std.HashSet α} [EquivBEq α] [LawfulHashable α] (h : m₁.isEmpty = true) : (m₁ ∩ m₂).isEmpty = true`
- **isEmpty_inter_right** [simp] {isEmpty}: `… {m₁ m₂ : Std.HashSet α} [EquivBEq α] [LawfulHashable α] (h : m₂.isEmpty = true) : (m₁ ∩ m₂).isEmpty = true`
- **isEmpty_inter_iff** {isEmpty}: `… {m₁ m₂ : Std.HashSet α} [EquivBEq α] [LawfulHashable α] : (m₁ ∩ m₂).isEmpty = true ↔ ∀ (k : α), k ∈ m₁ → ¬k ∈ m₂`
- **isEmpty_inter_comm** {isEmpty}: `… {m₁ m₂ : Std.HashSet α} [EquivBEq α] [LawfulHashable α] : (m₁ ∩ m₂).isEmpty = (m₂ ∩ m₁).isEmpty`

#### HashSet.Lemmas: Diff (26)

_scope: section Diff_; subheadings: contains (1), mem (3), Equiv (3), get? (4), get (1), getD (4), get! (4), size (3), isEmpty (2)

- **diff_eq** [simp]: `… {m₁ m₂ : Std.HashSet α} : m₁.diff m₂ = m₁ \ m₂`
- **contains_diff** [simp] {contains}: `… {m₁ m₂ : Std.HashSet α} [EquivBEq α] [LawfulHashable α] {k : α} : (m₁ \ m₂).contains k = (m₁.contains k && !m₂.contains k)`
- **mem_diff_iff** [simp] {mem}: `… {m₁ m₂ : Std.HashSet α} [EquivBEq α] [LawfulHashable α] {k : α} : k ∈ m₁ \ m₂ ↔ k ∈ m₁ ∧ ¬k ∈ m₂`
- **not_mem_diff_of_not_mem_left** {mem}: `… {m₁ m₂ : Std.HashSet α} [EquivBEq α] [LawfulHashable α] {k : α} (not_mem : ¬k ∈ m₁) : ¬k ∈ m₁ \ m₂`
- **not_mem_diff_of_mem_right** {mem}: `… {m₁ m₂ : Std.HashSet α} [EquivBEq α] [LawfulHashable α] {k : α} (mem : k ∈ m₂) : ¬k ∈ m₁ \ m₂`
- **Equiv.diff_left** {Equiv}: `… {m₁ m₂ m₃ : Std.HashSet α} [EquivBEq α] [LawfulHashable α] (equiv : m₁.Equiv m₂) : (m₁ \ m₃).Equiv (m₂ \ m₃)`
- **Equiv.diff_right** {Equiv}: `… {m₁ m₂ m₃ : Std.HashSet α} [EquivBEq α] [LawfulHashable α] (equiv : m₂.Equiv m₃) : (m₁ \ m₂).Equiv (m₁ \ m₃)`
- **Equiv.diff_congr** {Equiv}: `… {m₁ m₂ m₃ m₄ : Std.HashSet α} [EquivBEq α] [LawfulHashable α] (equiv₁ : m₁.Equiv m₃) (equiv₂ : m₂.Equiv m₄) : (m₁ \ m₂).Equiv (m₃ \ m₄)`
- **get?_diff** {get?}: `… {m₁ m₂ : Std.HashSet α} [EquivBEq α] [LawfulHashable α] {k : α} : (m₁ \ m₂).get? k = if k ∈ m₂ then none else m₁.get? k`
- **get?_diff_of_not_mem_right** {get?}: `… {m₁ m₂ : Std.HashSet α} [EquivBEq α] [LawfulHashable α] {k : α} (not_mem : ¬k ∈ m₂) : (m₁ \ m₂).get? k = m₁.get? k`
- **get?_diff_of_not_mem_left** {get?}: `… {m₁ m₂ : Std.HashSet α} [EquivBEq α] [LawfulHashable α] {k : α} (not_mem : ¬k ∈ m₁) : (m₁ \ m₂).get? k = none`
- **get?_diff_of_mem_right** {get?}: `… {m₁ m₂ : Std.HashSet α} [EquivBEq α] [LawfulHashable α] {k : α} (mem : k ∈ m₂) : (m₁ \ m₂).get? k = none`
- **get_diff** [simp] {get}: `… {m₁ m₂ : Std.HashSet α} [EquivBEq α] [LawfulHashable α] {k : α} {h_mem : k ∈ m₁ \ m₂} : (m₁ \ m₂).get k h_mem = m₁.get k ⋯`
- **getD_diff** {getD}: `… {m₁ m₂ : Std.HashSet α} [EquivBEq α] [LawfulHashable α] {k fallback : α} : (m₁ \ m₂).getD k fallback = if k ∈ m₂ then fallback else m₁.getD k fallback`
- **getD_diff_of_not_mem_right** {getD}: `… {m₁ m₂ : Std.HashSet α} [EquivBEq α] [LawfulHashable α] {k fallback : α} (not_mem : ¬k ∈ m₂) : (m₁ \ m₂).getD k fallback = m₁.getD k fallback`
- **getD_diff_of_mem_right** {getD}: `… {m₁ m₂ : Std.HashSet α} [EquivBEq α] [LawfulHashable α] {k fallback : α} (mem : k ∈ m₂) : (m₁ \ m₂).getD k fallback = fallback`
- **getD_diff_of_not_mem_left** {getD}: `… {m₁ m₂ : Std.HashSet α} [EquivBEq α] [LawfulHashable α] {k fallback : α} (not_mem : ¬k ∈ m₁) : (m₁ \ m₂).getD k fallback = fallback`
- **get!_diff** {get!}: `… {m₁ m₂ : Std.HashSet α} [EquivBEq α] [LawfulHashable α] [Inhabited α] {k : α} : (m₁ \ m₂).get! k = if k ∈ m₂ then default else m₁.get! k`
- **get!_diff_of_not_mem_right** {get!}: `… {m₁ m₂ : Std.HashSet α} [EquivBEq α] [LawfulHashable α] [Inhabited α] {k : α} (not_mem : ¬k ∈ m₂) : (m₁ \ m₂).get! k = m₁.get! k`
- **get!_diff_of_mem_right** {get!}: `… {m₁ m₂ : Std.HashSet α} [EquivBEq α] [LawfulHashable α] [Inhabited α] {k : α} (mem : k ∈ m₂) : (m₁ \ m₂).get! k = default`
- **get!_diff_of_not_mem_left** {get!}: `… {m₁ m₂ : Std.HashSet α} [EquivBEq α] [LawfulHashable α] [Inhabited α] {k : α} (not_mem : ¬k ∈ m₁) : (m₁ \ m₂).get! k = default`
- **size_diff_le_size_left** {size}: `… {m₁ m₂ : Std.HashSet α} [EquivBEq α] [LawfulHashable α] : (m₁ \ m₂).size ≤ m₁.size`
- **size_diff_eq_size_left** {size}: `… {m₁ m₂ : Std.HashSet α} [EquivBEq α] [LawfulHashable α] (h : ∀ (a : α), a ∈ m₁ → ¬a ∈ m₂) : (m₁ \ m₂).size = m₁.size`
- **size_diff_add_size_inter_eq_size_left** {size}: `… {m₁ m₂ : Std.HashSet α} [EquivBEq α] [LawfulHashable α] : (m₁ \ m₂).size + (m₁ ∩ m₂).size = m₁.size`
- **isEmpty_diff_left** [simp] {isEmpty}: `… {m₁ m₂ : Std.HashSet α} [EquivBEq α] [LawfulHashable α] (h : m₁.isEmpty = true) : (m₁ \ m₂).isEmpty = true`
- **isEmpty_diff_iff** {isEmpty}: `… {m₁ m₂ : Std.HashSet α} [EquivBEq α] [LawfulHashable α] : (m₁ \ m₂).isEmpty = true ↔ ∀ (k : α), k ∈ m₁ → k ∈ m₂`

#### HashSet.Lemmas: ofList / ofArray (17)

_scope: section@1265_

- **ofArray_eq_ofList** [simp, grind =, cbv_eval]: `… (a : Array α) : Std.HashSet.ofArray a = Std.HashSet.ofList a.toList`
- **ofList_nil** [simp, grind =]: `… : Std.HashSet.ofList [] = ∅`
- **ofList_singleton** [simp, grind =]: `… {k : α} : Std.HashSet.ofList [k] = ∅.insert k`
- **ofList_cons** [grind _=_]: `… {hd : α} {tl : List α} : Std.HashSet.ofList (hd :: tl) = (∅.insert hd).insertMany tl`
- **ofList_eq_insertMany_empty** [cbv_eval]: `… {l : List α} : Std.HashSet.ofList l = ∅.insertMany l`
- **contains_ofList** [simp, grind =]: `… [EquivBEq α] [LawfulHashable α] {l : List α} {k : α} : (Std.HashSet.ofList l).contains k = l.contains k`
- **mem_ofList** [simp, grind =]: `… [EquivBEq α] [LawfulHashable α] {l : List α} {k : α} : k ∈ Std.HashSet.ofList l ↔ l.contains k = true`
- **get?_ofList_of_contains_eq_false**: `… [EquivBEq α] [LawfulHashable α] {l : List α} {k : α} (contains_eq_false : l.contains k = false) : (Std.HashSet.ofList l).get? k = none`
- **get?_ofList_of_mem**: `… [EquivBEq α] [LawfulHashable α] {l : List α} {k k' : α} (k_beq : (k == k') = true) (distinct : List.Pairwise (fun a b => (a == b) = false) l) (mem : k ∈ l) : (Std.HashSet.ofList l).get? k' = some k`
- **get_ofList_of_mem**: `… [EquivBEq α] [LawfulHashable α] {l : List α} {k k' : α} (k_beq : (k == k') = true) (distinct : List.Pairwise (fun a b => (a == b) = false) l) (mem : k ∈ l) {h : k' ∈ Std.HashSet.ofList l} : (Std.HashSet.ofList l).get k' h = k`
- **get!_ofList_of_contains_eq_false**: `… [EquivBEq α] [LawfulHashable α] [Inhabited α] {l : List α} {k : α} (contains_eq_false : l.contains k = false) : (Std.HashSet.ofList l).get! k = default`
- **get!_ofList_of_mem**: `… [EquivBEq α] [LawfulHashable α] [Inhabited α] {l : List α} {k k' : α} (k_beq : (k == k') = true) (distinct : List.Pairwise (fun a b => (a == b) = false) l) (mem : k ∈ l) : (Std.HashSet.ofList l).get! k' = k`
- **getD_ofList_of_contains_eq_false**: `… [EquivBEq α] [LawfulHashable α] {l : List α} {k fallback : α} (contains_eq_false : l.contains k = false) : (Std.HashSet.ofList l).getD k fallback = fallback`
- **getD_ofList_of_mem**: `… [EquivBEq α] [LawfulHashable α] {l : List α} {k k' fallback : α} (k_beq : (k == k') = true) (distinct : List.Pairwise (fun a b => (a == b) = false) l) (mem : k ∈ l) : (Std.HashSet.ofList l).getD k' fallback = k`
- **size_ofList**: `… [EquivBEq α] [LawfulHashable α] {l : List α} (distinct : List.Pairwise (fun a b => (a == b) = false) l) : (Std.HashSet.ofList l).size = l.length`
- **size_ofList_le** [grind_pattern (ofList l).size (l.1361)]: `… [EquivBEq α] [LawfulHashable α] {l : List α} : (Std.HashSet.ofList l).size ≤ l.length`
- **isEmpty_ofList** [simp, grind =]: `… [EquivBEq α] [LawfulHashable α] {l : List α} : (Std.HashSet.ofList l).isEmpty = l.isEmpty`

#### HashSet.Lemmas: namespace Equiv (Equiv.* lemmas) (24)

_scope: namespace Equiv_

- **Equiv.refl** [refl, simp]: `… (m : Std.HashSet α) : m.Equiv m`
- **Equiv.rfl**: `… {m : Std.HashSet α} : m.Equiv m`
- **Equiv.symm** [symm]: `… {m₁ m₂ : Std.HashSet α} : m₁.Equiv m₂ → m₂.Equiv m₁`
- **Equiv.trans**: `… {m₁ m₂ m₃ : Std.HashSet α} : m₁.Equiv m₂ → m₂.Equiv m₃ → m₁.Equiv m₃`
- **Equiv.comm**: `… {m₁ m₂ : Std.HashSet α} : m₁.Equiv m₂ ↔ m₂.Equiv m₁`
- **Equiv.congr_left**: `… {m₁ m₂ m₃ : Std.HashSet α} (h : m₁.Equiv m₂) : m₁.Equiv m₃ ↔ m₂.Equiv m₃`
- **Equiv.congr_right**: `… {m₁ m₂ m₃ : Std.HashSet α} (h : m₁.Equiv m₂) : m₃.Equiv m₁ ↔ m₃.Equiv m₂`
- **Equiv.isEmpty_eq**: `… {m₁ m₂ : Std.HashSet α} [EquivBEq α] [LawfulHashable α] (h : m₁.Equiv m₂) : m₁.isEmpty = m₂.isEmpty`
- **Equiv.size_eq**: `… {m₁ m₂ : Std.HashSet α} [EquivBEq α] [LawfulHashable α] (h : m₁.Equiv m₂) : m₁.size = m₂.size`
- **Equiv.contains_eq**: `… {m₁ m₂ : Std.HashSet α} [EquivBEq α] [LawfulHashable α] {k : α} (h : m₁.Equiv m₂) : m₁.contains k = m₂.contains k`
- **Equiv.mem_iff**: `… {m₁ m₂ : Std.HashSet α} [EquivBEq α] [LawfulHashable α] {k : α} (h : m₁.Equiv m₂) : k ∈ m₁ ↔ k ∈ m₂`
- **Equiv.toList_perm**: `… {m₁ m₂ : Std.HashSet α} (h : m₁.Equiv m₂) : m₁.toList.Perm m₂.toList`
- **Equiv.of_toList_perm**: `… {m₁ m₂ : Std.HashSet α} (h : m₁.toList.Perm m₂.toList) : m₁.Equiv m₂`
- **Equiv.get?_eq**: `… {m₁ m₂ : Std.HashSet α} [EquivBEq α] [LawfulHashable α] {k : α} (h : m₁.Equiv m₂) : m₁.get? k = m₂.get? k`
- **Equiv.get_eq**: `… {m₁ m₂ : Std.HashSet α} [EquivBEq α] [LawfulHashable α] {k : α} (hk : k ∈ m₁) (h : m₁.Equiv m₂) : m₁.get k hk = m₂.get k ⋯`
- **Equiv.get!_eq**: `… {m₁ m₂ : Std.HashSet α} [EquivBEq α] [LawfulHashable α] [Inhabited α] {k : α} (h : m₁.Equiv m₂) : m₁.get! k = m₂.get! k`
- **Equiv.getD_eq**: `… {m₁ m₂ : Std.HashSet α} [EquivBEq α] [LawfulHashable α] {k fallback : α} (h : m₁.Equiv m₂) : m₁.getD k fallback = m₂.getD k fallback`
- **Equiv.insert**: `… {m₁ m₂ : Std.HashSet α} [EquivBEq α] [LawfulHashable α] (k : α) (h : m₁.Equiv m₂) : (m₁.insert k).Equiv (m₂.insert k)`
- **Equiv.erase**: `… {m₁ m₂ : Std.HashSet α} [EquivBEq α] [LawfulHashable α] (k : α) (h : m₁.Equiv m₂) : (m₁.erase k).Equiv (m₂.erase k)`
- **Equiv.insertMany_list**: `… {m₁ m₂ : Std.HashSet α} [EquivBEq α] [LawfulHashable α] (l : List α) (h : m₁.Equiv m₂) : (m₁.insertMany l).Equiv (m₂.insertMany l)`
- **Equiv.filter**: `… {m₁ m₂ : Std.HashSet α} (f : α → Bool) (h : m₁.Equiv m₂) : (Std.HashSet.filter f m₁).Equiv (Std.HashSet.filter f m₂)`
- **Equiv.of_forall_get?_eq**: `… {m₁ m₂ : Std.HashSet α} [EquivBEq α] [LawfulHashable α] (h : ∀ (k : α), m₁.get? k = m₂.get? k) : m₁.Equiv m₂`
- **Equiv.of_forall_contains_eq**: `… {m₁ m₂ : Std.HashSet α} [LawfulBEq α] (h : ∀ (k : α), m₁.contains k = m₂.contains k) : m₁.Equiv m₂`
- **Equiv.of_forall_mem_iff**: `… {m₁ m₂ : Std.HashSet α} [LawfulBEq α] (h : ∀ (k : α), k ∈ m₁ ↔ k ∈ m₂) : m₁.Equiv m₂`

#### HashSet.Lemmas: Equiv characterisations (section Equiv) (9)

_scope: section Equiv_

- **equiv_emptyWithCapacity_iff_isEmpty** [simp]: `… {m : Std.HashSet α} [EquivBEq α] [LawfulHashable α] {c : Nat} : m.Equiv (Std.HashSet.emptyWithCapacity c) ↔ m.isEmpty = true`
- **equiv_empty_iff_isEmpty** [simp]: `… {m : Std.HashSet α} [EquivBEq α] [LawfulHashable α] : m.Equiv ∅ ↔ m.isEmpty = true`
- **inter_equiv_empty_comm**: `… [EquivBEq α] [LawfulHashable α] {m₁ m₂ : Std.HashSet α} : (m₁ ∩ m₂).Equiv ∅ ↔ (m₂ ∩ m₁).Equiv ∅`
- **emptyWithCapacity_equiv_iff_isEmpty** [simp]: `… {m : Std.HashSet α} [EquivBEq α] [LawfulHashable α] {c : Nat} : (Std.HashSet.emptyWithCapacity c).Equiv m ↔ m.isEmpty = true`
- **empty_equiv_iff_isEmpty** [simp]: `… {m : Std.HashSet α} [EquivBEq α] [LawfulHashable α] : ∅.Equiv m ↔ m.isEmpty = true`
- **equiv_iff_toList_perm**: `… {m₁ m₂ : Std.HashSet α} [EquivBEq α] [LawfulHashable α] : m₁.Equiv m₂ ↔ m₁.toList.Perm m₂.toList`
- **equiv_iff_forall_mem_iff**: `… {m₁ m₂ : Std.HashSet α} [LawfulBEq α] : m₁.Equiv m₂ ↔ ∀ (k : α), k ∈ m₁ ↔ k ∈ m₂`
- **insertMany_list_equiv_foldl**: `… {m : Std.HashSet α} {l : List α} : (m.insertMany l).Equiv (List.foldl (fun acc a => acc.insert a) m l)`
- **ofList_equiv_foldl**: `… {l : List α} : (Std.HashSet.ofList l).Equiv (List.foldl (fun acc a => acc.insert a) ∅ l)`

#### HashSet.Lemmas: filter (13)

_scope: section filter_

- **toList_filter**: `… {m : Std.HashSet α} {f : α → Bool} : (Std.HashSet.filter f m).toList.Perm (List.filter f m.toList)`
- **isEmpty_filter_iff** [grind =]: `… {m : Std.HashSet α} [EquivBEq α] [LawfulHashable α] {f : α → Bool} : (Std.HashSet.filter f m).isEmpty = true ↔ ∀ (k : α) (h : k ∈ m), f (m.get k h) = false`
- **isEmpty_filter_eq_false_iff**: `… {m : Std.HashSet α} [EquivBEq α] [LawfulHashable α] {f : α → Bool} : (Std.HashSet.filter f m).isEmpty = false ↔ ∃ k h, f (m.get k h) = true`
- **mem_filter** [simp, grind =]: `… {m : Std.HashSet α} [EquivBEq α] [LawfulHashable α] {f : α → Bool} {k : α} : k ∈ Std.HashSet.filter f m ↔ ∃ h, f (m.get k h) = true`
- **contains_of_contains_filter**: `… {m : Std.HashSet α} [EquivBEq α] [LawfulHashable α] {f : α → Bool} {k : α} : (Std.HashSet.filter f m).contains k = true → m.contains k = true`
- **mem_of_mem_filter**: `… {m : Std.HashSet α} [EquivBEq α] [LawfulHashable α] {f : α → Bool} {k : α} : k ∈ Std.HashSet.filter f m → k ∈ m`
- **size_filter_le_size** [grind_pattern (m.filter f).size (l.1545)]: `… {m : Std.HashSet α} [EquivBEq α] [LawfulHashable α] {f : α → Bool} : (Std.HashSet.filter f m).size ≤ m.size`
- **size_filter_eq_size_iff**: `… {m : Std.HashSet α} [EquivBEq α] [LawfulHashable α] {f : α → Bool} : (Std.HashSet.filter f m).size = m.size ↔ ∀ (k : α) (h : k ∈ m), f (m.get k h) = true`
- **filter_equiv_self_iff**: `… {m : Std.HashSet α} [EquivBEq α] [LawfulHashable α] {f : α → Bool} : (Std.HashSet.filter f m).Equiv m ↔ ∀ (k : α) (h : k ∈ m), f (m.get k h) = true`
- **get?_filter** [simp, grind =]: `… {m : Std.HashSet α} [EquivBEq α] [LawfulHashable α] {f : α → Bool} {k : α} : (Std.HashSet.filter f m).get? k = Option.filter f (m.get? k)`
- **get_filter** [simp, grind =]: `… {m : Std.HashSet α} [EquivBEq α] [LawfulHashable α] {f : α → Bool} {k : α} {h : k ∈ Std.HashSet.filter f m} : (Std.HashSet.filter f m).get k h = m.get k ⋯`
- **get!_filter** [grind =]: `… {m : Std.HashSet α} [EquivBEq α] [LawfulHashable α] [Inhabited α] {f : α → Bool} {k : α} : (Std.HashSet.filter f m).get! k = (Option.filter f (m.get? k)).get!`
- **getD_filter** [grind =]: `… {m : Std.HashSet α} [EquivBEq α] [LawfulHashable α] {f : α → Bool} {k fallback : α} : (Std.HashSet.filter f m).getD k fallback = (Option.filter f (m.get? k)).getD fallback`

#### HashSet.IteratorLemmas: (top level) (3)

_scope: (top level)_

- **toList_iter** [simp]: `{α : Type u} [BEq α] [Hashable α] {m : Std.HashSet α} [EquivBEq α] [LawfulHashable α] : m.iter.toList = m.toList`
- **toListRev_iter** [simp]: `{α : Type u} [BEq α] [Hashable α] {m : Std.HashSet α} [EquivBEq α] [LawfulHashable α] : m.iter.toListRev = m.toList.reverse`
- **toArray_iter** [simp]: `{α : Type u} [BEq α] [Hashable α] {m : Std.HashSet α} [EquivBEq α] [LawfulHashable α] : m.iter.toArray = m.toArray`

## External API that mentions Std.HashMap / Std.HashSet

- `Array.groupByKey` (def, Std.Data.HashMap.Basic): `Array.groupByKey.{u, v} {α : Type u} {β : Type v} [BEq α] [Hashable α] (key : β → α) (xs : Array β) : Std.HashMap α (Array β)`
- `List.groupByKey` (def, Std.Data.HashMap.Basic): `List.groupByKey.{u, v} {α : Type u} {β : Type v} [BEq α] [Hashable α] (key : β → α) (xs : List β) : Std.HashMap α (List β)`
- `Std.Iter.Total.toHashSet` (def, Std.Data.Iterators.Consumers.Set): `Std.Iter.Total.toHashSet.{w} {α β : Type w} [BEq β] [Hashable β] [Std.Iterator α Id β] [Std.Iterators.Finite α Id] [Std.IteratorLoop α Id Id] (it : Std.Iter.Total β) : Std.HashSet β`
- `Std.Iter.toHashSet` (def, Std.Data.Iterators.Consumers.Set): `Std.Iter.toHashSet.{w} {α β : Type w} [BEq β] [Hashable β] [Std.Iterator α Id β] [Std.IteratorLoop α Id Id] (it : Std.Iter β) : Std.HashSet β`
- `Std.IterM.Total.toHashSet` (def, Std.Data.Iterators.Consumers.Monadic.Set): `Std.IterM.Total.toHashSet.{w, w'} {α β : Type w} [BEq β] [Hashable β] {m : Type w → Type w'} [Monad m] [Std.Iterator α m β] [Std.Iterators.Finite α m] [Std.IteratorLoop α m m] (it : Std.IterM.Total m β) : m (Std.HashSet β)`
- `Std.IterM.toHashSet` (def, Std.Data.Iterators.Consumers.Monadic.Set): `Std.IterM.toHashSet.{w, w'} {α β : Type w} [BEq β] [Hashable β] {m : Type w → Type w'} [Monad m] [Std.Iterator α m β] [Std.IteratorLoop α m m] (it : Std.IterM m β) : m (Std.HashSet β)`
- `Std.IterM.toHashSet_eq_fold` (theorem, Std.Data.Iterators.Lemmas.Consumers.Monadic.Set): `Std.IterM.toHashSet_eq_fold.{w, w'} {α β : Type w} {x✝ : BEq β} {x✝¹ : Hashable β} {m : Type w → Type w'} [Monad m] [Std.Iterator α m β] [Std.IteratorLoop α m m] {it : Std.IterM m β} : it.toHashSet = Std.IterM.fold (fun acc a => acc.insert a) ∅ it`

Internal users (not API): Std.Async.System, Std.Http.Internal.IndexMultiMap, Std.Sat.AIG.Basic, Std.Sat.AIG.RelabelNat, Std.Tactic.BVDecide.LRAT.Internal.Assignment

## Constants referenced by statements (outside Std.HashMap / Std.HashSet)

Count = number of HashMap/HashSet declarations (definitions, instances, theorems) whose type mentions the constant.

- **core (Init)** (99): `Eq` (839), `Membership.mem` (518), `Bool` (459), `Bool.true` (260), `Inhabited` (142), `Not` (142), `Nat` (131), `Prod` (131), `Bool.false` (126), `Iff` (125), `Id` (122), `GetElem?.getElem?` (115), `Id.instMonad` (107), `Membership` (95), `inferInstance` (93), `instForInOfForIn'` (93), `ite` (78), `Inter.inter` (77), `Prod.fst` (71), `Union.union` (70), `SDiff.sdiff` (65), `Unit` (65), `instDecidableEqBool` (59), `GetElem.getElem` (57), `GetElem?.toGetElem` (57), `Inhabited.default` (54), `GetElem?.getElem!` (48), `EmptyCollection.emptyCollection` (46), `LE.le` (39), `instLENat` (39), `And` (37), `OfNat.ofNat` (35), `instOfNatNat` (35), `Monad` (34), `Prod.mk` (27), `Prod.snd` (26), `HAdd.hAdd` (25), `instAddNat` (25), `instHAdd` (25), `LawfulMonad` (24), `Exists` (23), `Iff.mp` (21), `ForIn` (17), `Applicative.toFunctor` (16), `Applicative.toPure` (16), `Monad.toApplicative` (16), `MonadLiftT.monadLift` (16), `Pure.pure` (16), `Sigma` (16), `instMonadLiftT` (16), `Bool.and` (15), `Unit.unit` (15), `Iff.mpr` (14), `instDecidableNot` (14), `instDecidableAnd` (13), `Sigma.fst` (12), `Bool.or` (11), `ForInStep` (10), `PUnit` (10), `Or` (9), `Bool.not` (8), `ForIn.forIn` (8), `Sigma.snd` (8), `dite` (8), `And.left` (6), `ForM.forM` (5), `HSub.hSub` (5), `instDecidableEqNat` (5), `instHSub` (5), `instSubNat` (5), `Decidable` (4), `Bool.not_eq_true` (2), `EmptyCollection` (2), `Eq.rec` (2), `ForIn.toList` (2), `ForM` (2), `HAppend.hAppend` (2), `Insert` (2), `Insert.insert` (2), `Inter` (2), `Repr` (2), `SDiff` (2), `Singleton` (2), `Singleton.singleton` (2), `Trans` (2), `Union` (2), `instEquivBEqOfLawfulBEq` (2), `instHAppendOfAppend` (2), `instInhabitedPUnit` (2), `instLawfulHashableOfLawfulBEq` (2), `optParam` (2), `Bool.eq_false_iff` (1), `Decidable.decide` (1), `GetElem?` (1), `LawfulGetElem` (1), `LawfulSingleton` (1), `Ne` (1), `Subtype` (1), `instDecidableOr` (1)
- **Array** (12): `Array` (30), `Array.instMembership` (12), `Array.size` (12), `Array.toList` (6), `Array.foldl` (3), `Array.foldlM` (3), `Array.forM` (3), `Array.instForIn'InferInstanceMembershipOfMonad` (3), `Array.isEmpty` (3), `Array.contains` (2), `Array.find?` (2), `Array.map` (1)
- **BEq / Hashable classes** (8): `BEq` (1131), `Hashable` (1131), `EquivBEq` (762), `LawfulHashable` (762), `BEq.beq` (157), `LawfulBEq` (51), `instBEqOfDecidableEq` (5), `ReflBEq` (1)
- **List** (27): `List` (181), `List.instMembership` (114), `List.instForIn'InferInstanceMembershipOfMonad` (90), `List.contains` (48), `List.Pairwise` (41), `List.map` (33), `List.nil` (20), `List.Perm` (19), `List.cons` (15), `List.length` (15), `List.foldl` (9), `List.isEmpty` (9), `List.filter` (5), `List.reverse` (4), `List.toArray` (4), `List.all` (3), `List.any` (3), `List.find?` (3), `List.foldlM` (3), `List.instAppend` (2), `List.instForMOfMonad` (2), `List.Nodup` (1), `List.attach` (1), `List.filterMap` (1), `List.findSomeRev?` (1), `List.forM` (1), `List.unattach` (1)
- **Option** (19): `Option` (221), `Option.some` (80), `Option.none` (58), `Option.isSome` (50), `Option.get!` (20), `Option.getD` (20), `Option.map` (13), `Option.filter` (12), `Option.get` (10), `Option.pfilter` (9), `Option.isSome_of_eq_some` (8), `Option.bind` (6), `Option.isNone` (5), `Option.or` (4), `Option.pbind` (3), `Option.pmap` (3), `Option.all` (2), `Option.guard` (1), `Option.isSome_of_mem` (1)
- **Std hash-map internals (DHashMap / Raw)** (4): `Std.DHashMap.Internal.AssocList` (16), `Std.DHashMap.Internal.AssocList.AssocListIterator` (16), `Std.DHashMap.Internal.AssocList.iter` (16), `Std.DHashMap.Internal.AssocList.instIteratorAssocListIteratorIdSigma` (12)
- **Std.Internal** (1): `Std.Internal.PureForIn` (2)
- **Std iterators** (14): `Std.Iter.toIterM` (16), `Std.IterM` (16), `Std.Iterators.PostconditionT` (16), `Std.Iterators.Types.ArrayIterator` (16), `Std.Iterators.Types.Flatten` (16), `Std.Iterators.Types.Map` (16), `Std.Iterators.instMonadPostconditionT` (16), `Std.Iterators.Types.ArrayIterator.instIterator` (12), `Std.Iterators.Types.Flatten.instIterator` (12), `Std.Iterators.Types.Map.instIterator` (12), `Std.Iter` (4), `Std.Iter.toArray` (4), `Std.Iter.toList` (4), `Std.Iter.toListRev` (4)

## Source cross-check

- Std.Data.HashMap.Basic: 49 named source declarations found in the environment
- Std.Data.HashMap.AdditionalOperations: 2 named source declarations found in the environment
- Std.Data.HashMap.Iterator: 3 named source declarations found in the environment
- Std.Data.HashMap.DecidableEquiv: 0 named source declarations found in the environment
- Std.Data.HashMap.Lemmas: 679 named source declarations found in the environment; not exported: Std.HashMap.ext (l.38, private)
- Std.Data.HashMap.IteratorLemmas: 9 named source declarations found in the environment; not exported: Std.HashMap.toList_inner (l.106, non-public (module-local)), Std.HashMap.keys_inner (l.130, non-public (module-local))
- Std.Data.HashSet.Basic: 31 named source declarations found in the environment
- Std.Data.HashSet.Iterator: 1 named source declarations found in the environment
- Std.Data.HashSet.DecidableEquiv: 0 named source declarations found in the environment
- Std.Data.HashSet.Lemmas: 321 named source declarations found in the environment; not exported: Std.HashSet.ext (l.36, private)
- Std.Data.HashSet.IteratorLemmas: 3 named source declarations found in the environment

Anonymous instances are matched through the environment, not by keyword. Every exported environment declaration of the two families has a source location except the structure-generated, auto-generated and notation constants.
