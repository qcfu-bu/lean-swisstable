import Std
import OAMap
import Parity

/-!
# Statement parity of OAMap against `Std.HashMap`/`Std.HashSet` (v4.35.0)

`docs/ARCHITECTURE.md` §9.1 and `docs/parity.md`. The 16 iterator declarations are ignored
because their elaborated state types necessarily differ; `tools/srccheck.py` checks their source
text instead.

**Gate (until the Merge phase).** The two fields under `-- GATE` keep this check from failing
`lake test` while the library is incomplete: `failOnError := false` turns every finding into a
report line, and `maxShow := 5` keeps the report short. At the Merge, delete those two lines;
from then on any parity error, and any theorem that depends on `sorry`, fails `lake test`.

Standalone run, with the full to-do list:
`lake build OAMap Parity && lake env lean test/OAMapTest/ParityRun.lean`
(set `maxShow := 0` and `showMissingStatements := true` locally for the translated Std statement
of every missing declaration).
-/

#eval Parity.run {
  ignore := #[
    -- elaborated iterator state types expose Std's AssocList; text-checked by tools/srccheck.py
    `Std.HashMap.iter, `Std.HashMap.keysIter, `Std.HashMap.valuesIter, `Std.HashSet.iter,
    `Std.HashMap.toList_iter, `Std.HashMap.toListRev_iter, `Std.HashMap.toArray_iter,
    `Std.HashMap.toList_keysIter, `Std.HashMap.toListRev_keysIter, `Std.HashMap.toArray_keysIter,
    `Std.HashMap.toList_valuesIter_eq_toList_map_snd, `Std.HashMap.toListRev_valuesIter,
    `Std.HashMap.toArray_valuesIter,
    `Std.HashSet.toList_iter, `Std.HashSet.toListRev_iter, `Std.HashSet.toArray_iter],
  jsonOut := some ".lake/parity.json",
  -- GATE (until Merge): delete the next two lines to make parity a hard `lake test` gate.
  failOnError := false,
  maxShow := 5 }
