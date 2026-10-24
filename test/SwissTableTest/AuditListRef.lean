import SwissTableTest.AuditLib
import SwissTable.Core.ListRef

/-!
# Kernel-level audit of the reference core

`SwissTable.Core.ListRef` is no longer in the library's import closure (the selected core is
`SwissTable.Core.Swiss`), so `Audit.lean` does not see it; this file runs the same checks
(`SwissTableTest.Audit.run`, `AuditLib.lean`) on its constants. It is a separate root of the test
library, like `CoreSpecListRef.lean`, because the reference core and the selected core define the
same names.
-/

#eval SwissTableTest.Audit.run (· == `SwissTable.Core.ListRef) "SwissTable.Core.ListRef"
