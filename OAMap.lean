module

public import OAMap.HashMap
public import OAMap.HashSet

/-!
# OAMap: verified drop-in replacements for `Std.HashMap` and `Std.HashSet`

Importing `OAMap` gives `OAMap.HashMap α β` and `OAMap.HashSet α`, with the declarations,
statements and attributes of `Std.HashMap` and `Std.HashSet` (v4.35.0). Replace
`import Std.Data.HashMap` by `import OAMap.HashMap` and `Std.HashMap` by `OAMap.HashMap`.
The design is in `docs/ARCHITECTURE.md`.
-/
