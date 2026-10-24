/-!
# Mock candidate library for the parity checker

A few declarations of `Std.HashMap`, copied into namespace `SwissTable.HashMap` over a mock
structure whose model is a list of entries. Most copies are faithful; the ones marked
DELIBERATE differ from Std in one way each, to show that the checker reports it.
-/

set_option autoImplicit false
set_option linter.unusedVariables false

universe u v w w'

variable {α : Type u} {β : Type v} {_ : BEq α} {_ : Hashable α}

namespace SwissTable

/-- Mock map: the list of entries, newest first (no open addressing at all). -/
structure HashMap (α : Type u) (β : Type v) [BEq α] [Hashable α] where
  entries : List (α × β)

namespace HashMap

-- DELIBERATE (definition signature): default capacity 16, Std's default is 8.
@[cbv_opaque, inline] def emptyWithCapacity [BEq α] [Hashable α] (capacity := 16) :
    HashMap α β :=
  ⟨[]⟩

instance [BEq α] [Hashable α] : EmptyCollection (HashMap α β) where
  emptyCollection := emptyWithCapacity

-- DELIBERATE (missing instance): no `Inhabited (HashMap α β)`.

@[cbv_opaque, inline] def insert (m : HashMap α β) (a : α) (b : β) : HashMap α β :=
  ⟨(a, b) :: m.entries⟩

@[inline] def get? (m : HashMap α β) (a : α) : Option β :=
  (m.entries.find? (fun p => p.1 == a)).map (·.2)

@[inline] def contains (m : HashMap α β) (a : α) : Bool :=
  m.entries.any (fun p => p.1 == a)

instance [BEq α] [Hashable α] : Membership α (HashMap α β) where
  mem m a := m.contains a

instance [BEq α] [Hashable α] {m : HashMap α β} {a : α} : Decidable (a ∈ m) :=
  inferInstanceAs (Decidable (m.contains a = true))

@[inline] def get (m : HashMap α β) (a : α) (h : a ∈ m) : β :=
  have h' : (m.entries.any fun p => p.1 == a) = true := h
  ((m.entries.find? (fun p => p.1 == a)).get (List.find?_isSome.mpr (List.any_eq_true.mp h'))).2

@[inline] def get! [Inhabited β] (m : HashMap α β) (a : α) : β :=
  (m.get? a).getD default

-- DELIBERATE (instance name): Std calls it `instGetElem?Mem`.
instance instGetElemOpt [BEq α] [Hashable α] :
    GetElem? (HashMap α β) α β (fun m a => a ∈ m) where
  getElem m a h := m.get a h
  getElem? m a := m.get? a
  getElem! m a := m.get! a

-- DELIBERATE (missing definition): no `getD`.

@[inline] def size (m : HashMap α β) : Nat :=
  m.entries.length

@[inline] def isEmpty (m : HashMap α β) : Bool :=
  m.entries.isEmpty

section

variable {m : HashMap α β}

@[simp, grind =]
theorem isEmpty_empty : (∅ : HashMap α β).isEmpty := (rfl)

theorem mem_iff_contains {a : α} : a ∈ m ↔ m.contains a := Iff.rfl

@[simp, grind =] theorem get?_eq_getElem? {a : α} : get? m a = m[a]? := rfl

@[simp] theorem getElem?_empty {a : α} : (∅ : HashMap α β)[a]? = none := (rfl)

@[simp, grind =]
theorem size_empty : (∅ : HashMap α β).size = 0 := (rfl)

-- DELIBERATE (attributes): Std's also has `cbv_eval`.
@[simp, grind =]
theorem contains_insert [EquivBEq α] [LawfulHashable α] {k a : α} {v : β} :
    (m.insert k v).contains a = (k == a || m.contains a) := (rfl)

-- DELIBERATE (statement): `a == k` where Std has `k == a`.
@[grind =, cbv_eval] theorem getElem?_insert [EquivBEq α] [LawfulHashable α] {k a : α} {v : β} :
    (m.insert k v)[a]? = if a == k then some v else m[a]? := by
  show (((k, v) :: m.entries).find? (fun p => p.1 == a)).map (·.2) = _
  rw [List.find?_cons, BEq.comm (a := a) (b := k)]
  cases k == a <;> rfl

-- DELIBERATE (extra hypothesis): `[Inhabited α]`. Its proof is `sorry` (the mock's `size`
-- counts shadowed entries), which the axiom check reports too.
@[grind =] theorem size_insert [Inhabited α] [EquivBEq α] [LawfulHashable α] {k : α} {v : β} :
    (m.insert k v).size = if k ∈ m then m.size else m.size + 1 :=
  sorry

-- DELIBERATE (missing theorem): no `getElem?_insert_self`.

-- DELIBERATE (binder name): `h` where Std has `hab`.
theorem getElem?_congr [EquivBEq α] [LawfulHashable α] {a b : α} (h : a == b) :
    m[a]? = m[b]? := by
  show (m.entries.find? (fun p => p.1 == a)).map (·.2) = (m.entries.find? (fun p => p.1 == b)).map (·.2)
  have : (fun p : α × β => p.1 == a) = (fun p => p.1 == b) := funext fun _ => BEq.congr_right h
  rw [this]

/-- Not in Std: the checker lists it as an extra. -/
theorem getElem?_eq_find? {a : α} :
    m[a]? = (m.entries.find? (fun p => p.1 == a)).map (·.2) := rfl

end

-- DELIBERATE (binder info): `BEq`/`Hashable` are instance-implicit here; Std has them implicit.
@[simp, grind =]
theorem isEmpty_insert {α : Type u} {β : Type v} [BEq α] [Hashable α] {m : HashMap α β}
    [EquivBEq α] [LawfulHashable α] {k : α} {v : β} :
    (m.insert k v).isEmpty = false := (rfl)

end HashMap

end SwissTable
