import OAMapTest.CoreSpec
import OAMapTest.SealCheck
import OAMapTest.Audit
import OAMapTest.ParityRun
import OAMapTest.Cbv
import OAMapTest.Unverified
import OAMapTest.Semantics
import OAMapTest.SwissGroupUse

/-!
# The OAMap test library

`lake test` builds this library; each module logs an error, and so fails the build, when its
check fails (`docs/ARCHITECTURE.md` §9.2):

| module          | check                                                                          |
|-----------------|--------------------------------------------------------------------------------|
| `CoreSpec`      | the selected core implements the 45-name contract (§3.4)                       |
| `SealCheck`     | the layers above the core use only the contract names                          |
| `Audit`         | no axioms beyond the standard three, no unsafe/partial/extern                  |
| `ParityRun`     | statement, attribute and axiom parity with Std (§9.1)                          |
| `Cbv`           | `by cbv` closes the same goals as on Std                                       |
| `Unverified`    | `#guard` tests for functions without Std lemmas                                |
| `Semantics`     | `#guard` tests of kept keys/values, traversal order, `~m` scope                |
| `SwissGroupUse` | a lookup and an erase step from the Swiss group lemmas, as an importing module |

The library has a second root, `OAMapTest.CoreSpecListRef` (not imported here, because the
reference core `OAMap.Core.ListRef` and the selected core define the same names): `CoreSpec`'s
text against the reference core.

Since the Merge, `ParityRun` fails on any difference from Std outside its `ignore` list, and
`Audit` on any dependency on `sorryAx`.
-/
