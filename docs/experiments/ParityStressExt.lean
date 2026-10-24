import Std
import Parity

/-! Stress test on real data: `Std.HashMap` against `Std.ExtHashMap`, which mirrors its API but
needs `EquivBEq`/`LawfulHashable` almost everywhere, so most entries genuinely differ. -/
#eval Parity.run {
  nsMap := #[(`Std.HashMap, `Std.ExtHashMap)], checkAxioms := false,
  reportExtras := false, failOnError := false, jsonOut := some "parity-stress-ext.json" }
