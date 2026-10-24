module

public import OAMap.HashMap
public import OAMap.HashSet

/-!
# Monomorphic instances for the C check

`tools/check_c.py` reads the C that Lean generates for this module (`.lake/build/ir/Bench/CCheck.c`,
built by `lake build Bench.CCheck`). Each definition below is one operation of the public API at
`Nat` or `String` keys, so its C is the operation as a user's program gets it: the core's
`@[inline]` and `@[specialize]` code copied in at the key type. The script checks that

* no closure is called (`lean_apply_*`) by any of them or anything they call: `hash`, `==` and
  the loops are specialised;
* the lookups allocate nothing on the machine-word path (tables below `2 ^ 31` slots): only the
  `Nat`-indexed probes of larger tables (`findN`, which returns an `Option`) may allocate;
* the updates write their arrays in place: no array is shared (`lean_inc`) right before it is
  updated (the bug-A pattern of the bake-off), and the updated table reuses its argument's cell
  when that is unshared.

It is not part of the benchmark executable.
-/

public section

namespace Bench.CCheck

/-! ## Lookups -/

def getDNat (m : OAMap.HashMap Nat Nat) (a : Nat) : Nat := m.getD a 0
def getDStr (m : OAMap.HashMap String Nat) (a : String) : Nat := m.getD a 0
def getBangNat (m : OAMap.HashMap Nat Nat) (a : Nat) : Nat := m[a]!
def containsNat (m : OAMap.HashMap Nat Nat) (a : Nat) : Bool := m.contains a
def containsStr (m : OAMap.HashMap String Nat) (a : String) : Bool := m.contains a
def getKeyDStr (m : OAMap.HashMap String Nat) (a : String) : String := m.getKeyD a ""
def setContainsNat (s : OAMap.HashSet Nat) (a : Nat) : Bool := s.contains a
def setContainsStr (s : OAMap.HashSet String) (a : String) : Bool := s.contains a

/-! ## Updates -/

def insertNat (m : OAMap.HashMap Nat Nat) (a b : Nat) : OAMap.HashMap Nat Nat := m.insert a b
def insertStr (m : OAMap.HashMap String Nat) (a : String) (b : Nat) : OAMap.HashMap String Nat :=
  m.insert a b
def insertIfNewNat (m : OAMap.HashMap Nat Nat) (a b : Nat) : OAMap.HashMap Nat Nat :=
  m.insertIfNew a b
def getThenInsertIfNewStr (m : OAMap.HashMap String Nat) (a : String) (b : Nat) :
    Option Nat × OAMap.HashMap String Nat :=
  m.getThenInsertIfNew? a b
def containsThenInsertNat (m : OAMap.HashMap Nat Nat) (a b : Nat) : Bool × OAMap.HashMap Nat Nat :=
  m.containsThenInsert a b
def eraseNat (m : OAMap.HashMap Nat Nat) (a : Nat) : OAMap.HashMap Nat Nat := m.erase a
def eraseStr (m : OAMap.HashMap String Nat) (a : String) : OAMap.HashMap String Nat := m.erase a
def modifyNat (m : OAMap.HashMap Nat Nat) (a : Nat) : OAMap.HashMap Nat Nat := m.modify a (· + 1)
def alterStr (m : OAMap.HashMap String Nat) (a : String) : OAMap.HashMap String Nat :=
  m.alter a fun | some v => some (v + 1) | none => some 0
def setInsertStr (s : OAMap.HashSet String) (a : String) : OAMap.HashSet String := s.insert a

/-! ## Traversal -/

def foldNat (m : OAMap.HashMap Nat Nat) : Nat := m.fold (fun acc _ v => acc + v) 0

end Bench.CCheck
