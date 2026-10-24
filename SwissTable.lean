module

public import SwissTable.HashMap
public import SwissTable.HashSet

/-!
# SwissTable: verified drop-in replacements for `Std.HashMap` and `Std.HashSet`

Importing `SwissTable` gives `SwissTable.HashMap α β` and `SwissTable.HashSet α`, with the declarations,
statements and attributes of `Std.HashMap` and `Std.HashSet` (v4.35.0). Replace
`import Std.Data.HashMap` by `import SwissTable.HashMap` and `Std.HashMap` by `SwissTable.HashMap`.
The design is in `docs/ARCHITECTURE.md`.
-/
