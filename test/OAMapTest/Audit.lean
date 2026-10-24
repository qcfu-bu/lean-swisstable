import Lean
import OAMap
-- The Swiss bake-off core's modules are not imported by `OAMap` yet; audit them too.
import OAMap.Core.Swiss.Group

/-!
# Kernel-level audit of the library

For every constant defined in a module of `OAMap` (statements, definitions, instances and the
auxiliary declarations Lean generates for them), this check fails (logs an error) when

* the constant depends on an axiom other than `propext`, `Classical.choice` and `Quot.sound`
  (this catches `native_decide`, through `Lean.ofReduceBool`, and declared axioms);
* the constant is an `axiom`, an `opaque` constant or the result of a `partial def`, or is
  `unsafe`;
* the constant carries `@[implemented_by]` or `@[extern]`.

It complements Parity's axiom check, which only sees the declarations that have a Std
counterpart, and the text-level audit `tools/audit.py`.

A constant that depends on `sorryAx` fails the check too (`failOnSorry`, on since the Merge).
-/

open Lean Elab Command

namespace OAMapTest.Audit

/-- The axioms a declaration of the library may depend on. -/
def standardAxioms : List Name := [``propext, ``Classical.choice, ``Quot.sound]

/-- Whether a dependency on `sorryAx` fails the check (on since the Merge). -/
def failOnSorry : Bool := true

#eval show CommandElabM Unit from do
  let env ← getEnv
  let names := env.header.moduleNames
  let mut errors : Array MessageData := #[]
  let mut sorries : Array Name := #[]
  let mut nConsts : Nat := 0
  for h : i in [0:names.size] do
    let m := names[i]
    unless (`OAMap).isPrefixOf m do continue
    for c in env.header.moduleData[i]!.constNames do
      let some ci := env.find? c | continue
      nConsts := nConsts + 1
      match ci with
      | .axiomInfo _ => errors := errors.push m!"{c} (in {m}) is an axiom"
      | .opaqueInfo _ =>
        errors := errors.push m!"{c} (in {m}) is an opaque constant (`opaque` or `partial def`)"
      | _ => pure ()
      if ci.isUnsafe then errors := errors.push m!"{c} (in {m}) is unsafe"
      if ci.isPartial then errors := errors.push m!"{c} (in {m}) is partial"
      if (Compiler.implementedByAttr.getParam? env c).isSome then
        errors := errors.push m!"{c} (in {m}) has @[implemented_by]"
      if isExtern env c then errors := errors.push m!"{c} (in {m}) has @[extern]"
      for ax in ← collectAxioms c do
        if ax == ``sorryAx then
          sorries := sorries.push c
        else if !standardAxioms.contains ax then
          errors := errors.push m!"{c} (in {m}) depends on the axiom {ax}"
  let sorryMsg := m!"{sorries.size} declarations depend on sorryAx\
    {if sorries.isEmpty then m!"" else m!":\n{MessageData.joinSep (sorries.toList.map toMessageData) "\n"}"}"
  if !errors.isEmpty then
    logError m!"audit failed ({errors.size} findings):\n{MessageData.joinSep errors.toList "\n"}\n\
      {sorryMsg}"
  else if failOnSorry && !sorries.isEmpty then
    logError m!"audit failed: {sorryMsg}"
  else
    logInfo m!"audit ok: {nConsts} constants in OAMap use only {standardAxioms}; {sorryMsg}"

end OAMapTest.Audit
