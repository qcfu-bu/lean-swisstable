module

/-!
# The interface the benchmarked maps implement

A map kind is a type `M : (α : Type u) → (β : Type v) → [BEq α] → [Hashable α] → Type _`, the
shape of `Std.HashMap`, with these operations, in `M`'s namespace and with Std's signatures and
semantics (`insert` replaces the stored key and the value when the key is present):

    M.emptyWithCapacity (capacity := 8) : M α β
    instance : EmptyCollection (M α β)
    M.insert (m : M α β) (a : α) (b : β) : M α β
    M.get? (m : M α β) (a : α) : Option β
    M.getD (m : M α β) (a : α) (fallback : β) : β
    M.contains (m : M α β) (a : α) : Bool
    M.getThenInsertIfNew? (m : M α β) (a : α) (b : β) : Option β × M α β
    M.erase (m : M α β) (a : α) : M α β
    M.size (m : M α β) : Nat
    M.fold {γ : Type w} (f : γ → α → β → γ) (init : γ) (m : M α β) : γ

for every `{α : Type u} {β : Type v} [BEq α] [Hashable α]` and nothing more (no `Inhabited`, no
lawfulness). `bench_map M` checks exactly these signatures at universe-polymorphic `α β γ` that
carry only `BEq α` and `Hashable α`, so a map kind needing anything more does not compile, and
then derives the instance of `BenchMap` the workloads run on.

The workloads (`Bench/Loops.lean`) are written once against the class `BenchMap` and marked
`@[specialize]`; `bench/Main.lean` instantiates them at `Std.HashMap` and at `OAMap.HashMap`
(`Bench.mainFor`, `Bench/Run.lean`), so the compiler specialises every loop to the map's own
functions with the key type's `hash` and `==` called directly.
-/

@[expose] public section

namespace Bench

/-- The operations the workloads call, at one concrete map type `M` with keys `α` and values `β`.
Derive it with `bench_map`. -/
class BenchMap (M : Type) (α β : outParam Type) where
  /-- `∅`. A function, so that every use builds its own map. -/
  empty : Unit → M
  emptyWithCapacity : Nat → M
  insert : M → α → β → M
  get? : M → α → Option β
  getD : M → α → β → β
  contains : M → α → Bool
  getThenInsertIfNew? : M → α → β → Option β × M
  erase : M → α → M
  size : M → Nat
  fold : {γ : Type} → (γ → α → β → γ) → γ → M → γ

/-- `bench_map M`: check that `M` has the interface's signatures with nothing but `BEq α` and
`Hashable α`, and derive `BenchMap (M α β) α β` from them. -/
syntax (name := benchMapCmd) "bench_map " ident : command

open Lean in
macro_rules
  | `(bench_map $M:ident) => do
    let op (s : String) : Ident := mkIdent (M.getId ++ Name.mkSimple s)
    `(section
      universe u_1 u_2 u_3
      variable {α : Type u_1} {β : Type u_2} {γ : Type u_3} [BEq α] [Hashable α]
      /- The interface, at universe-polymorphic `α β γ` with only `BEq α` and `Hashable α`. -/
      example : $M α β := $(op "emptyWithCapacity")
      example (capacity : Nat) : $M α β := $(op "emptyWithCapacity") capacity
      example : $M α β := ∅
      example : $M α β → α → β → $M α β := $(op "insert")
      example : $M α β → α → Option β := $(op "get?")
      example : $M α β → α → β → β := $(op "getD")
      example : $M α β → α → Bool := $(op "contains")
      example : $M α β → α → β → Option β × $M α β := $(op "getThenInsertIfNew?")
      example : $M α β → α → $M α β := $(op "erase")
      example : $M α β → Nat := $(op "size")
      example : (γ → α → β → γ) → γ → $M α β → γ := $(op "fold")
      end
      instance {α β : Type} [BEq α] [Hashable α] : Bench.BenchMap ($M α β) α β where
        empty _ := ∅
        emptyWithCapacity n := $(op "emptyWithCapacity") n
        insert m a b := $(op "insert") m a b
        get? m a := $(op "get?") m a
        getD m a d := $(op "getD") m a d
        contains m a := $(op "contains") m a
        getThenInsertIfNew? m a b := $(op "getThenInsertIfNew?") m a b
        erase m a := $(op "erase") m a
        size m := $(op "size") m
        fold g init m := $(op "fold") g init m)

end Bench
