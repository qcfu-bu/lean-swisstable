import Lean
import ModS
open Lean Elab Command
#eval show CommandElabM Unit from do
  let env ← getEnv
  let some ci := env.find? `barS | throwError "no"
  logInfo m!"value?(allowOpaque) present: {(ci.value? (allowOpaque := true)).isSome}"
  match ci with
  | .thmInfo t => logInfo m!"thm value uses: {t.value.getUsedConstants}"
  | _ => pure ()
