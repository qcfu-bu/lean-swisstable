import Std.Data.HashMap
import Std.Data.HashSet
import SwissTable

/-!
# `by cbv` behaves as on Std

`docs/ARCHITECTURE.md` §6.4 and §9.2. Std's maps are evaluated by `cbv` through the `@[cbv_eval]`
lemmas (58) and the `@[cbv_opaque]` operations (10) that its `Lemmas.lean` and `Basic.lean`
declare, not by unfolding the table: on Std, `decide` and `rfl` fail on
`((∅ : HashMap Nat Nat).insert 1 2).contains 1 = true` and `cbv` proves it (`modtest/StdDecide.lean`).
SwissTable copies those attributes with Std's text, so `cbv` must prove the same goals.

Each `cbv_example T` elaborates `example : T := by cbv` twice: with `HashMap` and `HashSet` naming
Std's types, and with them naming SwissTable's. The Std half keeps the claim "as on Std" checked: an
example that Std's `cbv` stops proving fails here too.

The goals are ones `cbv` proves on Std: the queries `contains`, `get?`, `[·]?`, `[·]!`, `get!`
and `getD`, whose `@[cbv_eval]` lemmas rewrite them through the `@[cbv_opaque]` constructors
(`∅`, `emptyWithCapacity`, `insert`, `erase`, `filter`) and through `filterMap` and `map`, on maps
built by those constructors and by `ofList`, `ofArray` and `insertMany` (whose `cbv_eval`
lemmas turn them into insertions). These go through SwissTable's map-level lemmas only, so they hold
for every core. The last section is the one goal Std proves by unfolding its table (`isEmpty` of
the empty map), which here depends on the selected core.

Not tested: goals `cbv` does not prove on Std, such as `size`, `toList`, `keys`, `iter`, `alter`,
`modify` and `insertIfNew` of an insertion, `getKey?` (also through `map` and `filter`),
`size` and `isEmpty` of `map`, and `HashSet.get?` of an insertion. Against the list-backed
reference core `SwissTable.Core.ListRef`, `cbv` proved those too, because this plain file can unfold
the core's list operations; that depends on the core and is not Std's behaviour, so none is
tested.

Owner: ITER, Wave 3.
-/

namespace SwissTableTest.Cbv

open Lean in
/-- `cbv_example T` checks that `by cbv` proves `T` with `HashMap`/`HashSet` naming Std's types
(`open Std`) and with them naming SwissTable's (`open SwissTable`). -/
macro "cbv_example " t:term : command =>
  `(open $(mkIdent `Std):ident in example : $t := by cbv
    open $(mkIdent `SwissTable):ident in example : $t := by cbv)

/-! ## `HashMap`: queries on the empty map, insertions and erasures -/

cbv_example (∅ : HashMap Nat Nat).contains 1 = false
cbv_example (∅ : HashMap Nat Nat)[1]? = none
cbv_example (∅ : HashMap Nat Nat).get? 1 = none
cbv_example (∅ : HashMap Nat Nat)[1]! = 0
cbv_example (∅ : HashMap Nat Nat).getD 1 5 = 5

cbv_example ((∅ : HashMap Nat Nat).insert 1 2).contains 1 = true
cbv_example ((∅ : HashMap Nat Nat).insert 1 2).contains 3 = false
cbv_example ((HashMap.emptyWithCapacity 16 : HashMap Nat Nat).insert 1 2).contains 1 = true
cbv_example ((∅ : HashMap Nat Nat).insert 1 2)[1]? = some 2
cbv_example ((∅ : HashMap Nat Nat).insert 1 2)[3]? = none
cbv_example (((∅ : HashMap Nat Nat).insert 1 2).insert 1 5)[1]? = some 5
cbv_example ((∅ : HashMap Nat Nat).insert 1 2).get? 1 = some 2
cbv_example ((∅ : HashMap Nat Nat).insert 1 2)[1]! = 2
cbv_example ((∅ : HashMap Nat Nat).insert 1 2).get! 1 = 2
cbv_example ((∅ : HashMap Nat Nat).insert 1 2).getD 1 0 = 2
cbv_example ((∅ : HashMap Nat Nat).insert 1 2).getD 5 0 = 0
cbv_example (((∅ : HashMap Nat Nat).insert 1 2).erase 1).contains 1 = false
cbv_example (((∅ : HashMap Nat Nat).insert 1 2).erase 1)[1]? = none
cbv_example (((∅ : HashMap Nat Nat).insert 1 2).erase 3)[1]? = some 2
cbv_example (((∅ : HashMap Nat Nat).insert 1 2).erase 1).get? 1 = none
cbv_example (((∅ : HashMap Nat Nat).insert 1 2).erase 1)[1]! = 0
cbv_example (((∅ : HashMap Nat Nat).insert 1 2).erase 1).get! 1 = 0
cbv_example (((∅ : HashMap Nat Nat).insert 1 2).erase 1).getD 1 7 = 7
cbv_example ((∅ : HashMap Nat Nat).erase 1) = ∅
cbv_example (HashMap.emptyWithCapacity 3 : HashMap Nat Nat).erase 1 = HashMap.emptyWithCapacity 3

/-! ## `HashMap`: `ofList`, `ofArray`, `insertMany` -/

cbv_example (HashMap.ofList [(1, 2), (3, 4)])[3]? = some 4
cbv_example (HashMap.ofList [(1, 2), (1, 4)])[1]? = some 4
cbv_example (HashMap.ofList [(1, 2), (3, 4)]).contains 3 = true
cbv_example (HashMap.ofList [(1, 2), (3, 4)]).getD 3 0 = 4
cbv_example ((HashMap.ofList [(1, 2), (3, 4)]).erase 3)[3]? = none
cbv_example (HashMap.ofArray #[(1, 2), (3, 4)])[1]? = some 2
cbv_example ((∅ : HashMap Nat Nat).insertMany [(1, 2), (3, 4)])[3]? = some 4

/-! ## `HashMap`: `filter`, `filterMap`, `map` -/

cbv_example (((∅ : HashMap Nat Nat).insert 1 2).filter fun k _ => k == 1)[1]? = some 2
cbv_example (((∅ : HashMap Nat Nat).insert 1 2).filter fun k _ => k == 3)[1]? = none
cbv_example (((∅ : HashMap Nat Nat).insert 1 2).filter fun k _ => k == 1)[1]! = 2
cbv_example (((∅ : HashMap Nat Nat).insert 1 2).filter fun k _ => k == 1).getD 1 0 = 2
cbv_example (((∅ : HashMap Nat Nat).insert 1 2).filterMap fun _ v => some (v + 1))[1]? = some 3
cbv_example
  (((∅ : HashMap Nat Nat).insert 1 2).filterMap fun _ v => if v = 2 then none else some v)[1]? =
    none
cbv_example (((∅ : HashMap Nat Nat).insert 1 2).filterMap fun _ v => some (v + 1))[1]! = 3
cbv_example (((∅ : HashMap Nat Nat).insert 1 2).filterMap fun _ v => some (v + 1)).getD 1 0 = 3
cbv_example (((∅ : HashMap Nat Nat).insert 1 2).map fun _ v => v + 1)[1]? = some 3
cbv_example (((∅ : HashMap Nat Nat).insert 1 2).map fun _ v => v + 1).contains 1 = true
cbv_example (((∅ : HashMap Nat Nat).insert 1 2).map fun _ v => v + 1).getD 1 0 = 3
cbv_example (((∅ : HashMap Nat Nat).insert 1 2).map fun _ v => v + 1)[1]! = 3
cbv_example ((∅ : HashMap Nat Nat).map fun _ v => v + 1)[1]? = none

/-! ## `HashSet` -/

cbv_example (∅ : HashSet Nat).contains 1 = false
cbv_example (∅ : HashSet Nat).get? 1 = none
cbv_example (∅ : HashSet Nat).get! 1 = 0
cbv_example (∅ : HashSet Nat).getD 1 3 = 3

cbv_example ((∅ : HashSet Nat).insert 1).contains 1 = true
cbv_example ((∅ : HashSet Nat).insert 1).contains 2 = false
cbv_example (((∅ : HashSet Nat).insert 1).erase 1).contains 1 = false
cbv_example ((∅ : HashSet Nat).insert 1).getD 2 7 = 7
cbv_example (((∅ : HashSet Nat).insert 1).erase 1).get? 1 = none
cbv_example (((∅ : HashSet Nat).insert 1).erase 1).get! 1 = 0
cbv_example (((∅ : HashSet Nat).insert 1).erase 1).getD 1 7 = 7
cbv_example ((∅ : HashSet Nat).erase 1) = ∅
cbv_example (HashSet.ofList [1, 2, 3]).contains 2 = true
cbv_example (HashSet.ofList [1, 2, 1]).contains 1 = true
cbv_example ((HashSet.ofList [1, 2]).erase 1).contains 1 = false
cbv_example (HashSet.ofArray #[1, 2, 3]).contains 4 = false
cbv_example ((∅ : HashSet Nat).insertMany [1, 2]).contains 2 = true

/-! ## Through the table

Std's `cbv` proves this goal by unfolding `isEmpty` down to the size field of its table, as
there is no `@[cbv_eval]` lemma for it. Ours unfolds `isEmpty` through `SwissTable.Core.Derived` to
`Core.Table.size` of the selected core, which this plain file can see: for the Swiss core,
the `size` field of the unallocated table `Swiss.emptyImpl 8`, which is `0`. (It also held against
the reference core `SwissTable.Core.ListRef`.) -/

cbv_example (∅ : HashMap Nat Nat).isEmpty = true

end SwissTableTest.Cbv
