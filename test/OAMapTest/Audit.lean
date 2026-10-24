import OAMapTest.AuditLib
import OAMap

/-!
# Kernel-level audit of the library

Every constant defined in a module of `OAMap` passes the checks of `OAMapTest.Audit.run`
(`AuditLib.lean`): it depends on no axiom beyond `propext`, `Classical.choice` and `Quot.sound`
(so no `sorry`, `native_decide` or `bv_decide`), is no `axiom`, `opaque` constant or `partial`
definition, is not `unsafe` (except the compiler's `f._unsafe_rec` helper of a safe definition `f`
by well-founded recursion, in the same module), and carries no `@[implemented_by]` or `@[extern]`.

It complements Parity's axiom check, which only sees the declarations that have a Std
counterpart, and the text-level audit `tools/audit.py`. The reference core `OAMap.Core.ListRef`,
which the library does not import, is audited by `AuditListRef.lean`.

A constant that depends on `sorryAx` fails the check too (`failOnSorry`, on since the Merge).
-/

#eval OAMapTest.Audit.run (`OAMap).isPrefixOf "OAMap"
