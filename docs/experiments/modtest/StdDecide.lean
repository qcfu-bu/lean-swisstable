import Std
example : ((∅ : Std.HashMap Nat Nat).insert 1 2).contains 1 = true := by decide
example : ((∅ : Std.HashMap Nat Nat).insert 1 2).contains 1 = true := rfl
example : ((∅ : Std.HashMap Nat Nat).insert 1 2)[1]? = some 2 := by decide
example : ((∅ : Std.HashMap Nat Nat).insert 1 2).contains 1 = true := by cbv
example : ((∅ : Std.HashMap Nat Nat).insert 1 2).size = 1 := by decide
example : (Std.HashMap.ofList [(1,2),(3,4)]).toList.length = 2 := by decide
