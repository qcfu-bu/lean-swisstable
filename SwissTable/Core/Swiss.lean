module

public import SwissTable.Core.Swiss.Proofs.Query
public import SwissTable.Core.Swiss.Proofs.Update
public import SwissTable.Core.Swiss.Proofs.Traverse

/-!
# The Swiss core

The core module that `tools/select-core.sh swiss` selects: the 23 definitions of
`SwissTable/Core/Swiss/Table.lean` (on `Defs.lean`, `Loops.lean`, `Build.lean`) and the 22 contract
lemmas of `docs/ARCHITECTURE.md` §3.3, stated exactly as `test/SwissTableTest/CoreSpec.lean` uses them
in `Proofs/Query.lean` (1–11), `Proofs/Update.lean` (12–16) and `Proofs/Traverse.lean` (17–22).

All of them are proved, in the eight proof files under `SwissTable/Core/Swiss/Proofs/` (`Table.lean`,
"Proof structure", lists them), and depend only on `propext`, `Classical.choice` and
`Quot.sound`.
-/
