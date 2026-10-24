import Lean
import Std
open Lean Meta Elab Command
#eval show CommandElabM Unit from do
  let env ← getEnv
  let mut out : Array Name := #[]
  for (n, ci) in env.constants.toList do
    if (n.getPrefix == `Std.HashMap || n.getPrefix == `Std.HashSet ||
        n.getPrefix == `Std.HashMap.Equiv || n.getPrefix == `Std.HashSet.Equiv) && ci matches .thmInfo _ then
      if defeqAttr.hasTag env n then out := out.push n
  let sorted := out.qsort (·.toString < ·.toString)
  logInfo m!"{sorted.size}: {sorted.toList}"
