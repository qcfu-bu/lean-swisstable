module

public import SwissTable.HashMap.Model

/-!
# Decidable equivalence for `HashMap`

Std's `Std/Data/HashMap/DecidableEquiv.lean`: the instance has Std's binders and statement, so its
auto-generated name (`instDecidableEquivOfLawfulBEq`) is Std's. Std decides `m₁ ~m m₂` through
`DHashMap`'s instance; ours decides it by `m₁ == m₂` (`SwissTable.Core.Table.beq`, Std's algorithm)
and `Model.beq_iff_equiv` (`docs/ARCHITECTURE.md` §6.4), not through `Const.beqModel`. Like Std's
file, this one needs the model lemmas but none of the user lemmas, so it imports
`SwissTable.HashMap.Model` rather than `SwissTable.HashMap.Lemmas`.

Owner: API, Wave 1.
-/

public section

universe u v

namespace SwissTable.HashMap

instance {α : Type u} {β : Type v} [BEq α] [LawfulBEq α] [Hashable α] [BEq β] [LawfulBEq β] (m₁ m₂ : HashMap α β) : Decidable (m₁ ~m m₂) :=
  decidable_of_iff _ Model.beq_iff_equiv

end SwissTable.HashMap
