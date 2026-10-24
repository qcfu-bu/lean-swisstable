module

public import SwissTable.Core.Swiss

/-!
# Core selector

The ONE line above chooses the table core that every layer of SwissTable is built on. Layers above
the core import this module, never a core directly, and use only the 45 contract names of
`docs/ARCHITECTURE.md` §3 (checked by `test/SwissTableTest/SealCheck.lean`). Switch cores with
`tools/select-core.sh <core>`; a core is eligible when `test/SwissTableTest/CoreSpec.lean` builds
against it.
-/
