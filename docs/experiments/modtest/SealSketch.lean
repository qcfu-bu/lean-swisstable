import Lean
import Std
open Lean Elab Command

def contract : NameSet := .ofList [``Std.DHashMap.Internal.Raw₀]

def isLayoutModule (m : Name) : Bool :=
  [`Std.Data.DHashMap.Internal].any (·.isPrefixOf m)

#eval show CommandElabM Unit from do
  let env ← getEnv
  let modOf (n : Name) : Option Name :=
    (env.getModuleIdxFor? n).map fun i => env.allImportedModuleNames[i.toNat]!
  let mut bad : Array (Name × Name) := #[]
  for (n, ci) in env.constants.toList do
    let some m := modOf n | continue
    unless (`Std.Data.HashMap.Lemmas).isPrefixOf m && !isLayoutModule m do continue
    let used := ci.type.getUsedConstants ++ (((ci.value? (allowOpaque := true)).map Expr.getUsedConstants).getD #[])
    for c in used do
      if let some mc := modOf c then
        if isLayoutModule mc && !contract.contains c && !c.isInternal then bad := bad.push (n, c)
  logInfo m!"{bad.size} uses of layout constants outside the contract, e.g. {bad.toList.take 2}"
