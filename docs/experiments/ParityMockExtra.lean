import Std
import Parity

/-!
# More difference kinds, in one self-contained file

A second mock `SwissTable.HashMap` defined in this file, then checked in this file. Each
declaration differs from Std in the way its comment says (proofs are `sorry`; the axiom
check is off).
-/

set_option autoImplicit false
set_option linter.unusedVariables false

-- universes declared in another order than Std's `universe u v w w'`
universe w' w v u

variable {α : Type u} {β : Type v} {_ : BEq α} {_ : Hashable α}

namespace SwissTable

structure HashMap (α : Type u) (β : Type v) [BEq α] [Hashable α] where
  entries : List (α × β)

namespace HashMap

def insert (m : HashMap α β) (a : α) (b : β) : HashMap α β := ⟨(a, b) :: m.entries⟩
def contains (m : HashMap α β) (a : α) : Bool := m.entries.any (fun p => p.1 == a)
instance [BEq α] [Hashable α] : Membership α (HashMap α β) where
  mem m a := m.contains a

-- reducibility: `abbrev` where Std has a plain `def`
abbrev isEmpty (m : HashMap α β) : Bool := m.entries.isEmpty

-- universe parameters in another order (Std: `fold.{w, u, v}`)
def fold {γ : Type w} (f : γ → α → β → γ) (init : γ) (b : HashMap α β) : γ :=
  b.entries.foldl (fun acc p => f acc p.1 p.2) init

def get (m : HashMap α β) (a : α) (h : a ∈ m) : β := sorry
def get? (m : HashMap α β) (a : α) : Option β := (m.entries.find? (fun p => p.1 == a)).map (·.2)
def get! [Inhabited β] (m : HashMap α β) (a : α) : β := (m.get? a).getD default
instance [BEq α] [Hashable α] : GetElem? (HashMap α β) α β (fun m a => a ∈ m) where
  getElem m a h := m.get a h
  getElem? m a := m.get? a
  getElem! m a := m.get! a
def filter (f : α → β → Bool) (m : HashMap α β) : HashMap α β :=
  ⟨m.entries.filter fun p => f p.1 p.2⟩
def keys (m : HashMap α β) : List α := m.entries.map (·.1)

-- a `match` of the same shape as the one in `keys_filter`, declared first, so that Lean reuses
-- its matcher `SwissTable.HashMap.aux.match_1` there: matchers must be compared by definition
def aux (m : HashMap α β) (l : List {x // x ∈ m.keys}) : List {x // x ∈ m.keys} :=
  l.filter (fun ⟨x, h'⟩ => true)

section
variable {m : HashMap α β}

theorem mem_of_mem_keys [EquivBEq α] [LawfulHashable α] {k : α} (h : k ∈ m.keys) : k ∈ m := sorry

-- statement with a `match` and a proof term inside (`mem_of_mem_keys h'`): must pass
theorem keys_filter [EquivBEq α] [LawfulHashable α] {f : α → β → Bool} :
    (m.filter f).keys.Perm
      (m.keys.attach.filter (fun ⟨x, h'⟩ => f x (m[x]'(mem_of_mem_keys h')))).unattach := sorry

-- grind kind: `grind =` where Std has `grind _=_`
@[simp, grind =] theorem contains_iff_mem {a : α} : m.contains a ↔ a ∈ m := Iff.rfl

-- attribute: no `@[simp]` (Std has `@[simp, grind =]`)
@[grind =] theorem mem_insert [EquivBEq α] [LawfulHashable α] {k a : α} {v : β} :
    a ∈ m.insert k v ↔ k == a ∨ a ∈ m := sorry

-- dropped instance hypothesis `[LawfulHashable α]` (a weaker lemma: warning)
theorem contains_congr [EquivBEq α] {a b : α} (hab : a == b) :
    m.contains a = m.contains b := sorry

-- instance hypotheses in the other order
theorem mem_congr [LawfulHashable α] [EquivBEq α] {a b : α} (hab : a == b) :
    a ∈ m ↔ b ∈ m := sorry

-- dropped explicit hypothesis `(k == a) = false →` (error)
theorem contains_of_contains_insert [EquivBEq α] [LawfulHashable α] {k a : α} {v : β} :
    (m.insert k v).contains a → m.contains a := sorry

-- unfolded statement: defeq to Std's at instance transparency, not syntactically equal
theorem mem_insert_self [EquivBEq α] [LawfulHashable α] {k : α} {v : β} :
    (m.insert k v).contains k = true := sorry

end
end HashMap
end SwissTable

#eval Parity.run {
  only := #[`Std.HashMap.isEmpty, `Std.HashMap.fold, `Std.HashMap.contains_iff_mem,
    `Std.HashMap.keys_filter, `Std.HashMap.mem_of_mem_keys, `Std.HashMap.filter, `Std.HashMap.keys,
    `Std.HashMap.mem_insert, `Std.HashMap.contains_congr, `Std.HashMap.mem_congr,
    `Std.HashMap.contains_of_contains_insert, `Std.HashMap.mem_insert_self],
  checkAxioms := false, reportExtras := false, failOnError := false }
