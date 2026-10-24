import Lean
import OAMap

/-!
# Seal check: the layers above the core use only the contract names

`docs/ARCHITECTURE.md` §3.4. A *layout module* is any module under `OAMap.Core` other than the
selector `OAMap.Core.Table` and the layout-free `OAMap.Core.Derived` and `OAMap.Core.Bulk`
(today `OAMap.Core.ListRef`; later the bake-off cores). Every other `OAMap` module is *above the
core*. The check fails (logs an error) when

1. a declaration above the core mentions, in its type or its value (theorem bodies included), a
   constant defined in a layout module that is not one of the 45 contract names of §3.2/§3.3
   (compiler-internal names such as `_sizeOf_inst` are allowed, private names are not);
2. a module above the core imports a layout module directly (only `OAMap.Core.Table` may);
3. a module of `OAMap` uses `import all` on another `OAMap` module.

Then any core that passes `CoreSpec` can replace the selected one without breaking a proof above
it. This is a plain (non-`module`) file, so it sees the bodies of non-exposed definitions and
of theorems.
-/

open Lean Elab Command

namespace OAMapTest.SealCheck

/-- The 45 contract names: 23 definitions (§3.2) and 22 lemmas (§3.3). -/
def contract : NameSet := .ofList [
  -- definitions
  ``OAMap.Core.Table, ``OAMap.Core.Table.toListModel, ``OAMap.Core.Table.emptyWithCapacity,
  ``OAMap.Core.Table.size, ``OAMap.Core.Table.numBuckets, ``OAMap.Core.Table.markLinear,
  ``OAMap.Core.Table.lookup, ``OAMap.Core.Table.contains, ``OAMap.Core.Table.lookupMem,
  ``OAMap.Core.Table.insert, ``OAMap.Core.Table.insertIfNew,
  ``OAMap.Core.Table.containsThenInsert, ``OAMap.Core.Table.containsThenInsertIfNew,
  ``OAMap.Core.Table.getThenInsertIfNew?, ``OAMap.Core.Table.erase, ``OAMap.Core.Table.alter,
  ``OAMap.Core.Table.modify, ``OAMap.Core.Table.filter, ``OAMap.Core.Table.filterMap,
  ``OAMap.Core.Table.map, ``OAMap.Core.Table.foldM, ``OAMap.Core.Table.foldRev,
  ``OAMap.Core.Table.forIn,
  -- lemmas
  ``OAMap.Core.Table.distinctKeys, ``OAMap.Core.Table.size_eq_length,
  ``OAMap.Core.Table.toListModel_emptyWithCapacity, ``OAMap.Core.Table.lookup_emptyWithCapacity,
  ``OAMap.Core.Table.erase_emptyWithCapacity, ``OAMap.Core.Table.contains_eq_lookup,
  ``OAMap.Core.Table.lookup_eq, ``OAMap.Core.Table.lookupMem_eq,
  ``OAMap.Core.Table.containsThenInsert_eq, ``OAMap.Core.Table.containsThenInsertIfNew_eq,
  ``OAMap.Core.Table.getThenInsertIfNew?_eq, ``OAMap.Core.Table.toListModel_insert,
  ``OAMap.Core.Table.toListModel_insertIfNew, ``OAMap.Core.Table.toListModel_erase,
  ``OAMap.Core.Table.toListModel_alter, ``OAMap.Core.Table.toListModel_modify,
  ``OAMap.Core.Table.toListModel_filter, ``OAMap.Core.Table.toListModel_filterMap,
  ``OAMap.Core.Table.toListModel_map, ``OAMap.Core.Table.foldM_eq_foldlM_toListModel,
  ``OAMap.Core.Table.foldRev_eq_foldr_toListModel, ``OAMap.Core.Table.forIn_eq_forIn_toListModel]

/-- Modules under `OAMap.Core` that are not layout-specific. -/
def layoutFree : List Name := [`OAMap.Core.Table, `OAMap.Core.Derived, `OAMap.Core.Bulk]

def isLayoutModule (m : Name) : Bool :=
  (`OAMap.Core).isPrefixOf m && !(layoutFree.contains m)

def isOAMapModule (m : Name) : Bool :=
  (`OAMap).isPrefixOf m

/-- A used layout constant is allowed if it is a contract name or a compiler-internal
auxiliary (`_sizeOf_inst`, ...). Private names of a layout module are never allowed. -/
def allowed (c : Name) : Bool :=
  contract.contains c || (c.isInternal && !isPrivateName c)

#eval show CommandElabM Unit from do
  let env ← getEnv
  unless contract.size == 45 do
    logError m!"the contract list has {contract.size} names, expected 45"
  let names := env.header.moduleNames
  let modOf (n : Name) : Option Name := (env.getModuleIdxFor? n).map fun i => names[i.toNat]!
  let mut bad : Array MessageData := #[]
  let mut nDecls : Nat := 0
  let mut nMods : Nat := 0
  let mut usedContract : NameSet := {}
  for h : i in [0:names.size] do
    let m := names[i]
    unless isOAMapModule m do continue
    let data := env.header.moduleData[i]!
    -- 3. no `import all` of an OAMap module
    for imp in data.imports do
      if imp.importAll && isOAMapModule imp.module then
        bad := bad.push m!"{m}: `import all {imp.module}`"
    if isLayoutModule m then continue
    nMods := nMods + 1
    -- 2. only the selector imports a layout module
    if m != `OAMap.Core.Table then
      for imp in data.imports do
        if isLayoutModule imp.module then
          bad := bad.push m!"{m}: imports the layout module {imp.module} directly"
    -- 1. declarations above the core use only contract names
    for n in data.constNames do
      let some ci := env.find? n | continue
      nDecls := nDecls + 1
      let used := ci.type.getUsedConstants ++
        (((ci.value? (allowOpaque := true)).map Expr.getUsedConstants).getD #[])
      for c in used do
        let some mc := modOf c | continue
        unless isLayoutModule mc do continue
        if allowed c then
          usedContract := usedContract.insert c
        else
          bad := bad.push m!"{n} (in {m}) uses {c} (from {mc}), which is not a contract name"
  if bad.isEmpty then
    logInfo m!"seal ok: {nDecls} declarations in {nMods} modules above the core use \
      {usedContract.size} of the {contract.size} contract names and nothing else from a layout module"
  else
    logError m!"seal broken ({bad.size} findings):\n{MessageData.joinSep bad.toList "\n"}"

end OAMapTest.SealCheck
