import OAMap

/-!
# `by cbv` behaves as on Std

`by cbv` examples on concrete maps, copied from their Std counterparts (for instance
`((∅ : HashMap Nat Nat).insert 1 2).contains 1 = true`), which `decide` and `rfl` cannot close on
Std either (`docs/ARCHITECTURE.md` §6.4, §9.2).

Stub (Wave 0). Owner: ITER, Wave 3.
-/
