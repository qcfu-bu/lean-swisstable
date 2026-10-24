module

public import OAMap.HashMap.Model
public meta import Std.Data.HashMap.Basic

/-!
# The `simp_to_model` tactic

Std's `simp_to_model` (`Std/Data/DHashMap/Internal/RawLemmas.lean`) with the changes of
`docs/ARCHITECTURE.md` §6.1 and `docs/proofs.md` §5:

* the lemma tables are keyed by user-facing names (`getElem?`, `mem`, `insert`, ...) and point to
  the bridge lemmas of `OAMap.Model`;
* the discharger is `wf_trivial` (`assumption` or `apply Model.distinctKeys`: the invariant is
  bundled, so the only side goals are `DistinctKeys (toListModel m)`);
* `Bool.not_eq_true` is in the simp set, so `¬k ∈ m` becomes `containsKey k l = false`, the normal
  form of the list lemmas. When the conclusion of the `using` lemma is stated with
  `¬containsKey k l = true` instead, `apply` is retried after undoing that normal form;
* an optional location (`at h`, `at *`), with the finisher `wf_finish`, which also closes a goal
  `containsKey k l = b` from a hypothesis `k ∈ m`, `k ∉ m` or `m.contains k = b` that was not
  rewritten (because `simp … at *` could not rewrite it in place, or because no location was given).

Std's `beq` query (`m₁ == m₂` to `Const.beqModel`) has no row: there is no such bridge lemma
(see `OAMap.HashMap.Model`), and `simp_to_model [beq]` ignores the name, as for any unknown name.

Std's `empty` macro (`intros; simp_all [List.isEmpty_iff]`) is not provided: the ported proofs
use its expansion `{ intros; simp_all [List.isEmpty_iff] }` instead, so nothing needs it. (A
scoped tactic token would not reserve the identifier `empty`, so it could be added if wanted.)

Usage (inside `namespace OAMap.HashMap`, where the syntax is active):

```
simp_to_model [insert, getElem?] using List.getValue?_insertEntry
simp_to_model [mem, getKey?, diff] at * using List.getKey?_filter_not_contains_map_fst_of_containsKey_eq_false_left
simp_to_model [Equiv, insert] using List.insertEntry_of_perm _ h.1
simp_to_model                       -- every query lemma, no operation lemma
```

The names in the list are *query* names (rewritten by their bridge lemma, with congruence lemmas
for permutations) and *operation* names (whose `toListModel_*` permutation is pushed through
every congruence lemma of the listed queries). Unknown names are ignored, as in Std. With no query
name, all query lemmas are used.

The three tactics are `scoped` in `OAMap.HashMap`: they are available in the `Lemmas` files,
which are inside that namespace, and their tokens are keywords only where `OAMap.HashMap` is open,
never globally. Their syntax kinds live in `OAMap.Model` and the lemma tables are private, so
`OAMap.HashMap` contains only Std's names (the parity report has no extras). The quotation
layout (with the `apply` step on its own line) is `Mock2.lean`'s; a one-line variant does not
parse. The `meta import` provides `Std.HashMap` for the tables, which are used at
macro-expansion time.

Owner: API, Wave 1.
-/

public section

namespace OAMap.HashMap

open Lean Std.Internal.List

/-- Query names: the bridge lemma that rewrites the query to the model, and the congruence lemmas
(applied to an operation's `toListModel_*` permutation) that push the rewrite through it. -/
private meta def queryMap : Std.HashMap Name (Name × Array (MacroM (TSyntax `term))) :=
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
     ⟨`toList, (``Model.toList_eq_toListModel_map, #[`(Model.perm_map_congr_left)])⟩,
     ⟨`keys, (``Model.keys_eq_keys_toListModel, #[`(Model.perm_keys_congr_left)])⟩,
     ⟨`values, (``Model.values_eq_values_toListModel, #[])⟩,
     ⟨`toArray, (``Model.toArray_eq_toArray_map_toListModel, #[])⟩,
     ⟨`keysArray, (``Model.keysArray_eq_toArray_keys_toListModel, #[])⟩,
     ⟨`valuesArray, (``Model.valuesArray_eq_toArray_values_toListModel, #[])⟩,
     ⟨`fold, (``Model.fold_eq_foldl_toListModel, #[])⟩,
     ⟨`foldM, (``Model.foldM_eq_foldlM_toListModel, #[])⟩,
     ⟨`forM, (``Model.forM_eq_forM_toListModel, #[])⟩,
     ⟨`forIn, (``Model.forIn_eq_forIn_toListModel, #[])⟩,
     ⟨`all, (``Model.all_eq_all_toListModel, #[])⟩,
     ⟨`any, (``Model.any_eq_any_toListModel, #[])⟩,
     ⟨`Equiv, (``Model.equiv_iff_toListModel_perm,
       #[`(_root_.List.Perm.congr_left), `(_root_.List.Perm.congr_right)])⟩]

/-- Operation names: the permutation lemma describing the model of the result. -/
private meta def modifyMap : Std.HashMap Name Name :=
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
     ⟨`insertManyIfNewUnit, ``Model.toListModel_insertManyIfNewUnit_list⟩,
     ⟨`ofList, ``Model.toListModel_ofList⟩,
     ⟨`unitOfList, ``Model.toListModel_unitOfList⟩]

/-- Closes the side goals of the model lemmas: a hypothesis, or the bundled invariant
`DistinctKeys (toListModel m)` of any map `m`. -/
scoped syntax (name := _root_.OAMap.Model.wfTrivialTac) "wf_trivial" : tactic

scoped macro_rules
  | `(tactic| wf_trivial) => `(tactic| first | assumption | apply Model.distinctKeys)

/-- The closing step of `simp_to_model`: a side condition, or a hypothesis (`k ∈ m`, `k ∉ m`,
`m.contains k = b`) that was not rewritten to the model, either because `simp … at *` could not
rewrite it in place or because no location was given. -/
scoped syntax (name := _root_.OAMap.Model.wfFinishTac) "wf_finish" : tactic

scoped macro_rules
  | `(tactic| wf_finish) => `(tactic| first
      | wf_trivial
      | (simp only [Bool.not_eq_true, Model.mem_iff_containsKey, Model.contains_eq_containsKey]
          at *; assumption))

/-- `simp_to_model [names] (at loc)? (using t)?` rewrites the queries and operations named in
`names` to the list model (`OAMap.Model.toListModel`) and then applies `t`, a lemma about
`Std.Internal.List`; remaining side goals are closed by `wf_finish`. See the module docstring. -/
scoped syntax (name := _root_.OAMap.Model.simpToModelTac) "simp_to_model"
  (" [" (ident,*) "]")? (Lean.Parser.Tactic.location)? ("using" term)? : tactic

scoped macro_rules
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
  -- `apply t`; if the conclusion of `t` is stated with `¬b = true` where the rewritten goal has
  -- `b = false` (the `Bool.not_eq_true` normal form), retry after undoing that normal form; the
  -- last alternative repeats `apply t` so that a genuine failure reports `apply`'s own error.
  let applyTac? ← using?.mapM fun t =>
    `(tactic| first
      | apply $t
      | (simp only [← Bool.not_eq_true]; apply $t)
      | apply $t)
  `(tactic|
    (simp (discharger := wf_trivial) only
      [Bool.not_eq_true, $[$(Array.map Lean.mkIdent queryNames ++ congrModify):term],*] $[$loc]?
     $[$(applyTac?.toArray):tactic];*)
    <;> try wf_finish)

end OAMap.HashMap
