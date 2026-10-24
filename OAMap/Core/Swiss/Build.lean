module

public import OAMap.Core.Swiss.Proofs.Rebuild

/-!
# The SwissTable core: the table, allocation and rebuild (executable code, frozen)

`Table` bundles the arrays and counters with their invariant `Swiss.WF` (`Defs.lean`) as the
field `wf`, a `Prop` the compiler erases: the runtime layout is the eight data fields, as before.
This file defines the table and what the later operations take as given about rebuilt tables:
`emptyTable`, `rebuild`, and `reserveTable`, the table an insert that found no room writes into.
Their invariants come from `Proofs/Rebuild.lean`; what `reserveInsert` needs to know of
`reserveTable` is proved after this file, in `Proofs/Write.lean`. Layout, algorithms and
measurements: `OAMap/Core/Swiss/Table.lean`.
-/

-- Elaborated `let`s stay `let`s instead of becoming `have`s, the setting of the SwissF prototype
-- and of the bake-off harness that measured the frozen code. It changes no generated C in this
-- file today, but it does in `Table.lean`, and every code file is compiled under the same setting.
set_option cleanup.letToHave false

@[expose] public section

universe u v w w'

namespace OAMap.Core

/-- The SwissTable: control bytes, keys and values in slot order (the layout of `Table.lean`),
the counters, and the invariant. The fields are core internals: code above the core reaches a
table only through the contract names (checked by `test/OAMapTest/SealCheck.lean`). -/
structure Table (α : Type u) (β : Type v) [BEq α] [Hashable α] : Type (max u v) where
  /-- The control bytes: `cap` slots, then the mirror of the first 8. -/
  ctrl : ByteArray
  /-- The key of each slot, then the placeholder key. -/
  slotKeys : Array α
  /-- The value of each slot, then the placeholder value. -/
  slotVals : Array β
  /-- The number of entries. -/
  size : Nat
  /-- How many EMPTY slots may still be filled before a rebuild. -/
  growthLeft : Nat
  /-- `cap - 1` (`0` for the unallocated table). -/
  mask : USize
  /-- `57 - log₂ cap`: `hashBits` keeps the top `log₂ cap + 7` bits of the product. -/
  shift : UInt64
  /-- The capacity asked for by `emptyWithCapacity`, used by the first insert. -/
  reqCap : Nat
  /-- The invariant (erased at runtime). -/
  wf : Swiss.WF ⟨ctrl, slotKeys, slotVals⟩ size growthLeft mask shift

/-- The arrays of a table, as the model sees them. -/
@[inline] def Table.slots {α : Type u} {β : Type v} [BEq α] [Hashable α] (t : Table α β) :
    Swiss.Slots α β :=
  ⟨t.ctrl, t.slotKeys, t.slotVals⟩

namespace Swiss

variable {α : Type u} {β : Type v}

/-- An empty table of `2 ^ lg` slots (`lg ≥ 3`) with placeholders `k0` and `v0`. -/
def emptyTable [BEq α] [Hashable α] (lg : Nat) (k0 : α) (v0 : β) (req : Nat) (h : 3 ≤ lg) :
    Table α β :=
  let cap := 2 ^ lg
  ⟨emptyCtrl cap, Array.replicate (cap + 1) k0, Array.replicate (cap + 1) v0, 0, capacityOf cap,
    (cap - 1).toUSize, (57 - lg).toUInt64, req, WF.empty k0 v0 h⟩

/-- Rebuild into a fresh table of `2 ^ lg` slots holding the same entries, with placeholders `k0`
and `v0` (the pair being inserted). -/
@[specialize] def rebuild [BEq α] [Hashable α] (t : Table α β) (lg : Nat) (k0 : α) (v0 : β)
    (h : RebuildPre t.slots t.size lg) : Table α β :=
  let ⟨ctrl, keys, vals, size, _, mask, _, req, wf⟩ := t
  let cap := 2 ^ lg
  let nmask := (cap - 1).toUSize
  let nshift := (57 - lg).toUInt64
  let nc := ctrl.propagateMark (emptyCtrl cap)
  let nk := keys.propagateMark (Array.replicate (cap + 1) k0)
  let nv := vals.propagateMark (Array.replicate (cap + 1) v0)
  match hm : (if hs : smallMask nmask then
      moveLoop ctrl keys vals mask 0 nc nk nv nmask nshift (wf.moveSrcU h hs)
        (moveDstU h.three_le hs) freeBound
    else
      moveLoopN ctrl keys vals (ctrl.size - 8) 0 nc nk nv cap nshift wf.moveSrcN
        (moveDstN h.three_le) freeBoundN) with
  | (nc, nk, nv) =>
    ⟨nc, nk, nv, size, capacityOf cap - size, nmask, nshift, req, WF.rebuild wf h hm⟩

/-- The table an insert of a new key `a ↦ b` writes into when no EMPTY slot may be filled: the
unallocated table allocated, or the table rebuilt at the same capacity (when
`size + 1 ≤ capacity / 2`) or at twice it. -/
@[inline] def reserveTable [BEq α] [Hashable α] (t : Table α β) (a : α) (b : β) : Table α β :=
  if hz : t.slotKeys.size == 0 then
    emptyTable (lgFor (max t.reqCap 1)) a b t.reqCap (three_le_lgFor _)
  else
    let full := capacityOf (t.ctrl.size - 8)
    if hh : t.size + 1 ≤ full / 2 then rebuild t (lgFor full) a b (t.wf.rebuildPre_same hz hh)
    else rebuild t (lgFor (max (t.size + 1) (full + 1))) a b (t.wf.rebuildPre_grow hz)

end Swiss

end OAMap.Core
