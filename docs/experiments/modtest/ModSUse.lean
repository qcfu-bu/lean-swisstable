import Lean
import ModS
open Lean Elab Command
#print axioms barS
#eval show CommandElabM Unit from do
  let env ← getEnv
  let some ci := env.find? `barS | throwError "no"
  logInfo m!"value? present: {ci.value?.isSome}"
  let axs ← liftCoreM (Lean.collectAxioms `barS)
  logInfo m!"collectAxioms: {axs}"
