module

public import Std.Data.HashMap.Basic
public meta import Std.Data.HashMap.Basic

public section

open Lean in
meta def queryMap2 : Std.HashMap Name (Name × Array (MacroM (TSyntax `term))) :=
  .ofList [⟨`size, (``Nat.add_zero, #[`(Nat.zero_add)])⟩]

macro "wf_trivial2" : tactic => `(tactic| first | assumption | rfl)

syntax "my_tac2" (" [" (ident,*) "]")? (Lean.Parser.Tactic.location)? ("using" term)? : tactic

macro_rules
| `(tactic| my_tac2 $[[$names,*]]? $[$loc]? $[using $using?]?) => do
  let mut qs : Array Lean.Name := #[]
  let mut cs : Array Lean.Term := #[]
  if let some names := names then
    for q in names.getElems do
      let some (q, c) := queryMap2.get? q.getId | continue
      qs := qs.push q
      for c' in c do cs := cs.push (← c')
  `(tactic|
    (simp (discharger := wf_trivial2) only
      [Nat.add_zero, $[$(Array.map Lean.mkIdent qs ++ cs):term],*] $[$loc]?
     $[apply $(using?.toArray):term];*)
    <;> try wf_trivial2)

end
