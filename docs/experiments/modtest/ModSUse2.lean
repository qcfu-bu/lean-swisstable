module

import Lean
import all ModS
open Lean Elab Command
#eval show CommandElabM Unit from do
  let env ← getEnv
  let some ci := env.find? `barS | throwError "no"
  logInfo m!"value? present: {ci.value?.isSome}; uses: {(ci.value?.map Expr.getUsedConstants).getD #[]}"
