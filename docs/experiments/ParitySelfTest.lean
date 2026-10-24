import Std
import Parity

/-! Self-test: Std against itself (identity renaming). Every declaration must pass; this
exercises the alignment, attribute and instance code on all of Std's real statements. -/
#eval Parity.run { nsMap := #[(`Std.HashMap, `Std.HashMap), (`Std.HashSet, `Std.HashSet)],
                   reportExtras := false, checkAxioms := false, maxShow := 20 }
