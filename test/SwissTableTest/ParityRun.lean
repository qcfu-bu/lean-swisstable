import Std
import SwissTable
import Parity

/-!
# Statement parity of SwissTable against `Std.HashMap`/`Std.HashSet` (v4.35.0)

`docs/ARCHITECTURE.md` §9.1 and `docs/parity.md`. Only `Raw` (deferred) is excluded, so the
`Internal` namespace is checked, and so are the structure internals (constructors, projections,
recursors, `noConfusion`, `mk.inj…`). The `ignore` list has 30 entries that necessarily differ:

* the 16 iterator declarations, whose elaborated state types expose Std's `AssocList`;
  `tools/srccheck.py` checks their source text instead;
* the 14 internals of `HashMap` and `HashMap.Equiv` that mention the `inner` field, which is a core
  table rather than a `DHashMap` (`docs/ARCHITECTURE.md` §1). HashSet's internals (its `inner`
  is a `HashMap α Unit`, as in Std), `HashMap.ctorIdx` and `HashMap.noConfusionType` are checked.

**Gate (on since the Merge).** Any difference from Std outside the `ignore` list fails
`lake test`: a missing declaration, a statement, binder, attribute or notation difference, a
theorem that depends on `sorry` or on an axiom beyond the standard three (errors and, with
`failOnWarning`, warnings), and any public declaration of ours with no Std counterpart (extras).

Standalone run: `lake build SwissTable Parity && lake env lean test/SwissTableTest/ParityRun.lean`
(set `showMissingStatements := true` locally for the translated Std statement of every missing
declaration).
-/

#eval Parity.run {
  ignore := #[
    -- elaborated iterator state types expose Std's AssocList; text-checked by tools/srccheck.py
    `Std.HashMap.iter, `Std.HashMap.keysIter, `Std.HashMap.valuesIter, `Std.HashSet.iter,
    `Std.HashMap.toList_iter, `Std.HashMap.toListRev_iter, `Std.HashMap.toArray_iter,
    `Std.HashMap.toList_keysIter, `Std.HashMap.toListRev_keysIter, `Std.HashMap.toArray_keysIter,
    `Std.HashMap.toList_valuesIter_eq_toList_map_snd, `Std.HashMap.toListRev_valuesIter,
    `Std.HashMap.toArray_valuesIter,
    `Std.HashSet.toList_iter, `Std.HashSet.toListRev_iter, `Std.HashSet.toArray_iter,
    -- HashMap's `inner` field is a core table, not a `DHashMap` (ARCHITECTURE §1)
    `Std.HashMap.inner, `Std.HashMap.mk, `Std.HashMap.rec, `Std.HashMap.recOn,
    `Std.HashMap.casesOn, `Std.HashMap.mk.noConfusion, `Std.HashMap.mk.inj,
    `Std.HashMap.mk.injEq, `Std.HashMap.mk.sizeOf_spec,
    `Std.HashMap.Equiv.inner, `Std.HashMap.Equiv.mk, `Std.HashMap.Equiv.rec,
    `Std.HashMap.Equiv.recOn, `Std.HashMap.Equiv.casesOn],
  exclude := #[`Std.HashMap.Raw, `Std.HashSet.Raw],
  checkStructureInternals := true,
  jsonOut := some ".lake/parity.json",
  failOnWarning := true }
