import Std
import ParityMock
import Parity

/-! Parity check of the mock library against the Std declarations it copies. -/
#eval Parity.run {
  only := #[
    -- type
    `Std.HashMap,
    -- instances
    `Std.HashMap.instEmptyCollection, `Std.HashMap.instInhabited, `Std.HashMap.instMembership,
    `Std.HashMap.instDecidableMem, `Std.HashMap.instGetElem?Mem,
    -- definitions
    `Std.HashMap.emptyWithCapacity, `Std.HashMap.insert, `Std.HashMap.get?,
    `Std.HashMap.contains, `Std.HashMap.get, `Std.HashMap.get!, `Std.HashMap.getD,
    `Std.HashMap.size, `Std.HashMap.isEmpty,
    -- theorems
    `Std.HashMap.isEmpty_empty, `Std.HashMap.mem_iff_contains, `Std.HashMap.get?_eq_getElem?,
    `Std.HashMap.getElem?_empty, `Std.HashMap.size_empty, `Std.HashMap.contains_insert,
    `Std.HashMap.getElem?_insert, `Std.HashMap.size_insert, `Std.HashMap.getElem?_insert_self,
    `Std.HashMap.getElem?_congr, `Std.HashMap.isEmpty_insert],
  verbose := true,
  jsonOut := some "parity-mock-report.json" }
