import Lean
import SwissTable

/-!
# Seal check: the layers above the core use only the contract names

`docs/ARCHITECTURE.md` §3.4. A *layout module* is any module under `SwissTable.Core` other than the
selector `SwissTable.Core.Table` and the layout-free `SwissTable.Core.Derived` and
`SwissTable.Core.Bulk` (the selected Swiss core `SwissTable.Core.Swiss` and its modules, and the
reference core `SwissTable.Core.ListRef`). Every other `SwissTable` module is *above the core*. The
check fails (logs an error) when

1. a declaration above the core mentions, in its type or its value (theorem bodies included), a
   constant defined in a layout module that is not one of the 45 contract names of §3.2/§3.3
   (compiler-internal names such as `_sizeOf_inst` are allowed, private names are not);
2. a module above the core imports a layout module directly (only `SwissTable.Core.Table` may);
3. a module of `SwissTable` uses `import all` on another `SwissTable` module.

Then any core that passes `CoreSpec` can replace the selected one without breaking a proof above
it. This is a plain (non-`module`) file, so it sees the bodies of non-exposed definitions and
of theorems.
-/

open Lean Elab Command

namespace SwissTableTest.SealCheck

/-- The 45 contract names: 23 definitions (§3.2) and 22 lemmas (§3.3). -/
def contract : NameSet := .ofList [
  -- definitions
  ``SwissTable.Core.Table, ``SwissTable.Core.Table.toListModel, ``SwissTable.Core.Table.emptyWithCapacity,
  ``SwissTable.Core.Table.size, ``SwissTable.Core.Table.numBuckets, ``SwissTable.Core.Table.markLinear,
  ``SwissTable.Core.Table.lookup, ``SwissTable.Core.Table.contains, ``SwissTable.Core.Table.lookupMem,
  ``SwissTable.Core.Table.insert, ``SwissTable.Core.Table.insertIfNew,
  ``SwissTable.Core.Table.containsThenInsert, ``SwissTable.Core.Table.containsThenInsertIfNew,
  ``SwissTable.Core.Table.getThenInsertIfNew?, ``SwissTable.Core.Table.erase, ``SwissTable.Core.Table.alter,
  ``SwissTable.Core.Table.modify, ``SwissTable.Core.Table.filter, ``SwissTable.Core.Table.filterMap,
  ``SwissTable.Core.Table.map, ``SwissTable.Core.Table.foldM, ``SwissTable.Core.Table.foldRev,
  ``SwissTable.Core.Table.forIn,
  -- lemmas
  ``SwissTable.Core.Table.distinctKeys, ``SwissTable.Core.Table.size_eq_length,
  ``SwissTable.Core.Table.toListModel_emptyWithCapacity, ``SwissTable.Core.Table.lookup_emptyWithCapacity,
  ``SwissTable.Core.Table.erase_emptyWithCapacity, ``SwissTable.Core.Table.contains_eq_lookup,
  ``SwissTable.Core.Table.lookup_eq, ``SwissTable.Core.Table.lookupMem_eq,
  ``SwissTable.Core.Table.containsThenInsert_eq, ``SwissTable.Core.Table.containsThenInsertIfNew_eq,
  ``SwissTable.Core.Table.getThenInsertIfNew?_eq, ``SwissTable.Core.Table.toListModel_insert,
  ``SwissTable.Core.Table.toListModel_insertIfNew, ``SwissTable.Core.Table.toListModel_erase,
  ``SwissTable.Core.Table.toListModel_alter, ``SwissTable.Core.Table.toListModel_modify,
  ``SwissTable.Core.Table.toListModel_filter, ``SwissTable.Core.Table.toListModel_filterMap,
  ``SwissTable.Core.Table.toListModel_map, ``SwissTable.Core.Table.foldM_eq_foldlM_toListModel,
  ``SwissTable.Core.Table.foldRev_eq_foldr_toListModel, ``SwissTable.Core.Table.forIn_eq_forIn_toListModel]

/-- Modules under `SwissTable.Core` that are not layout-specific. -/
def layoutFree : List Name := [`SwissTable.Core.Table, `SwissTable.Core.Derived, `SwissTable.Core.Bulk]

def isLayoutModule (m : Name) : Bool :=
  (`SwissTable.Core).isPrefixOf m && !(layoutFree.contains m)

def isSwissTableModule (m : Name) : Bool :=
  (`SwissTable).isPrefixOf m

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
    unless isSwissTableModule m do continue
    let data := env.header.moduleData[i]!
    -- 3. no `import all` of an SwissTable module
    for imp in data.imports do
      if imp.importAll && isSwissTableModule imp.module then
        bad := bad.push m!"{m}: `import all {imp.module}`"
    if isLayoutModule m then continue
    nMods := nMods + 1
    -- 2. only the selector imports a layout module
    if m != `SwissTable.Core.Table then
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
          -- count only contract names (an allowed internal name such as `_sizeOf_inst` is not one)
          if contract.contains c then usedContract := usedContract.insert c
        else
          bad := bad.push m!"{n} (in {m}) uses {c} (from {mc}), which is not a contract name"
  if bad.isEmpty then
    logInfo m!"seal ok: {nDecls} declarations in {nMods} modules above the core use \
      {usedContract.size} of the {contract.size} contract names and nothing else from a layout module"
  else
    logError m!"seal broken ({bad.size} findings):\n{MessageData.joinSep bad.toList "\n"}"

end SwissTableTest.SealCheck
