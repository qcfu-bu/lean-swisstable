import OAMapTest.CoreSpec
import OAMapTest.SealCheck
import OAMapTest.Audit
import OAMapTest.ParityRun
import OAMapTest.Cbv
import OAMapTest.Unverified

/-!
# The OAMap test library

`lake test` builds this library; each module logs an error, and so fails the build, when its
check fails (`docs/ARCHITECTURE.md` §9.2):

| module       | check                                                       |
|--------------|-------------------------------------------------------------|
| `CoreSpec`   | the selected core implements the 45-name contract (§3.4)    |
| `SealCheck`  | the layers above the core use only the contract names       |
| `Audit`      | no axioms beyond the standard three, no unsafe/partial/extern |
| `ParityRun`  | statement, attribute and axiom parity with Std (§9.1)       |
| `Cbv`        | `by cbv` closes the same goals as on Std                    |
| `Unverified` | `#guard` tests for functions without Std lemmas             |

Until the Merge phase, `ParityRun` and `Audit` report without failing on missing declarations and
on `sorry`; their docstrings say which line to change.
-/
