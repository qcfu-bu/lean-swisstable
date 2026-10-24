import OAMapTest.AuditLib
import OAMap.Core.ListRef

/-!
# Kernel-level audit of the reference core

`OAMap.Core.ListRef` is no longer in the library's import closure (the selected core is
`OAMap.Core.Swiss`), so `Audit.lean` does not see it; this file runs the same checks
(`OAMapTest.Audit.run`, `AuditLib.lean`) on its constants. It is a separate root of the test
library, like `CoreSpecListRef.lean`, because the reference core and the selected core define the
same names.
-/

#eval OAMapTest.Audit.run (· == `OAMap.Core.ListRef) "OAMap.Core.ListRef"
