module

public import Std.Data.HashMap.Basic
public meta import Std.Data.HashMap.Basic
public meta import Lean.Parser.Tactic

public section

open Lean in
meta def queryMapT : Std.HashMap Name Name :=
  .ofList [⟨`size, ``Nat.add_zero⟩]

syntax "my_tac" (" [" (ident,*) "]")? : tactic

macro_rules
| `(tactic| my_tac $[[$names,*]]?) => do
  let mut qs : Array Lean.Name := #[]
  if let some names := names then
    for q in names.getElems do
      let some q := queryMapT.get? q.getId | continue
      qs := qs.push q
  `(tactic| simp only [$[$(Array.map Lean.mkIdent qs):term],*])

end
