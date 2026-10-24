/-
Copyright (c) 2024 Lean FRO, LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Markus Himmel
-/
module

public import SwissTable.HashMap.Basic

@[expose] public section

/-!
# Additional hash map operations

This module defines the operations `map` and `filterMap` on `SwissTable.HashMap`.
Lemmas about these operations are found in `SwissTable.HashMap.Lemmas`.

Implementation notes: Std's `Std/Data/HashMap/AdditionalOperations.lean`, generated from Std's
text (`docs/ARCHITECTURE.md` §4.3) without the `Raw` part (deferred); the bodies call
`SwissTable.Core.Table.filterMap` and `SwissTable.Core.Table.map`.

Owner: API, Wave 1.
-/

set_option linter.missingDocs true
set_option autoImplicit false

universe u v w

variable {α : Type u} {β : Type v} {γ : Type w}

namespace SwissTable

namespace HashMap

/--
Updates the values of the hash map by applying the given function to all mappings, keeping
only those mappings where the function returns `some` value.
-/
@[cbv_opaque, inline] def filterMap [BEq α] [Hashable α] (f : α → β → Option γ)
    (m : HashMap α β) : HashMap α γ :=
  ⟨m.inner.filterMap f⟩

/--
Updates the values of the hash map by applying the given function to all mappings. 
-/
@[cbv_opaque, inline] def map [BEq α] [Hashable α] (f : α → β → γ) (m : HashMap α β) :
    HashMap α γ :=
  ⟨m.inner.map f⟩

end HashMap

end SwissTable
