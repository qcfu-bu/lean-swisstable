import Lean

/-!
# The kernel-level audit, as a command

`SwissTableTest.Audit.run inScope what` checks every constant defined in a module whose name
satisfies `inScope` (statements, definitions, instances and the auxiliary declarations Lean
generates for them), and logs an error, failing the build, when

* the constant depends on an axiom other than `propext`, `Classical.choice` and `Quot.sound`
  (this catches `native_decide` and `bv_decide`, through `Lean.ofReduceBool`, and declared
  axioms), or on `sorryAx` (`failOnSorry`);
* the constant is an `axiom`, an `opaque` constant or the result of a `partial def`, or is
  `unsafe`;
* the constant carries `@[implemented_by]` or `@[extern]`.

One kind of generated constant is exempt from the `partial`/`unsafe` test: `f._unsafe_rec`, the
helper that the compiler generates for a definition `f` by well-founded recursion (the loops of
the core) and runs in place of `f`. It is exempt only when it is that helper (`isWfUnsafeRec`):
`f` is a safe definition in the same module whose value is a well-founded fixpoint
(`WellFounded.fix` or `WellFounded.Nat.fix`, directly or through `f._unary` or `f._mutual`, also
safe and in the same module). So the helpers of a `partial def` (whose `f` is an `opaque`
constant) are still reported, through `f`, and so would be a hand-written `unsafe def
f._unsafe_rec` for any other `f`. The exempt helpers are counted in the report, and their axioms
are checked like every other constant's.

`Audit.lean` runs it on the library `SwissTable`, and `AuditListRef.lean` on the reference core
`SwissTable.Core.ListRef`, which the library no longer imports.
-/

open Lean Elab Command

namespace SwissTableTest.Audit

/-- The axioms a declaration of the library may depend on. -/
def standardAxioms : List Name := [``propext, ``Classical.choice, ``Quot.sound]

/-- Whether a dependency on `sorryAx` fails the check (on since the Merge). -/
def failOnSorry : Bool := true

/-- `d` is a safe definition, in module `mod`, whose value uses a well-founded fixpoint. -/
def isWfFix (env : Environment) (mod : Option ModuleIdx) (d : Name) : Bool :=
  match env.find? d with
  | some (.defnInfo v) =>
    v.safety == .safe && env.getModuleIdxFor? d == mod &&
      (v.value.getUsedConstants.any fun u => u == ``WellFounded.fix || u == ``WellFounded.Nat.fix)
  | _ => false

/-- `c` is the compiler's helper `f._unsafe_rec` of a safe definition `f` by well-founded
recursion, in the same module (see the module docstring). -/
def isWfUnsafeRec (env : Environment) (c : Name) : Bool :=
  match Compiler.isUnsafeRecName? c with
  | none => false
  | some f =>
    let mod := env.getModuleIdxFor? c
    match env.find? f with
    | some (.defnInfo v) =>
      v.safety == .safe && env.getModuleIdxFor? f == mod &&
        (isWfFix env mod f ||
          (v.value.getUsedConstants.any fun u =>
            (u == f ++ `_unary || u == f ++ `_mutual) && isWfFix env mod u))
    | _ => false

/-- The audit of every constant defined in a module whose name satisfies `inScope`; `what` names
the checked modules in the report. -/
def run (inScope : Name → Bool) (what : String) : CommandElabM Unit := do
  let env ← getEnv
  let names := env.header.moduleNames
  let mut errors : Array MessageData := #[]
  let mut sorries : Array Name := #[]
  let mut nConsts : Nat := 0
  let mut nUnsafeRec : Nat := 0
  for h : i in [0:names.size] do
    let m := names[i]
    unless inScope m do continue
    for c in env.header.moduleData[i]!.constNames do
      let some ci := env.find? c | continue
      nConsts := nConsts + 1
      let exempt := isWfUnsafeRec env c
      if exempt then nUnsafeRec := nUnsafeRec + 1
      match ci with
      | .axiomInfo _ => errors := errors.push m!"{c} (in {m}) is an axiom"
      | .opaqueInfo _ =>
        errors := errors.push m!"{c} (in {m}) is an opaque constant (`opaque` or `partial def`)"
      | _ => pure ()
      if ci.isUnsafe && !exempt then errors := errors.push m!"{c} (in {m}) is unsafe"
      if ci.isPartial && !exempt then errors := errors.push m!"{c} (in {m}) is partial"
      if (Compiler.implementedByAttr.getParam? env c).isSome then
        errors := errors.push m!"{c} (in {m}) has @[implemented_by]"
      if isExtern env c then errors := errors.push m!"{c} (in {m}) has @[extern]"
      for ax in ← liftCoreM (collectAxioms c) do
        if ax == ``sorryAx then
          sorries := sorries.push c
        else if !standardAxioms.contains ax then
          errors := errors.push m!"{c} (in {m}) depends on the axiom {ax}"
  let sorryMsg := m!"{sorries.size} declarations depend on sorryAx\
    {if sorries.isEmpty then m!"" else m!":\n{MessageData.joinSep (sorries.toList.map toMessageData) "\n"}"}"
  if nConsts == 0 then
    logError m!"audit failed: no constant in {what}"
  else if !errors.isEmpty then
    logError m!"audit failed ({errors.size} findings):\n{MessageData.joinSep errors.toList "\n"}\n\
      {sorryMsg}"
  else if failOnSorry && !sorries.isEmpty then
    logError m!"audit failed: {sorryMsg}"
  else
    logInfo m!"audit ok: {nConsts} constants in {what} use only {standardAxioms} \
      ({nUnsafeRec} of them the compiler's `_unsafe_rec` helpers of safe definitions by \
      well-founded recursion); {sorryMsg}"

end SwissTableTest.Audit
