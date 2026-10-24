import OAMap

/-!
# `#guard` tests for the functions that have no Std lemmas

`partition`, `values`, `valuesArray`, `Repr` and `Internal.numBuckets` are not pinned by any Std
statement, so their behaviour is checked by `#guard` (`docs/ARCHITECTURE.md` §9.2). Everything
else is covered by the proofs and by parity.

Stub (Wave 0). Owner: ITER, Wave 3.
-/
