module

public import SwissTable.HashMap
public import SwissTable.HashSet

/-!
# Monomorphic instances for the C check

`tools/check_c.py` reads the C that Lean generates for this module (`.lake/build/ir/Bench/CCheck.c`,
built by `lake build Bench.CCheck`). Each definition below is one operation of the public API at
`Nat` or `String` keys, so its C is the operation as a user's program gets it: the core's
`@[inline]` and `@[specialize]` code copied in at the key type. The script checks that

* no closure is called (`lean_apply_*`) by any of them or anything they call: `hash`, `==` and
  the loops are specialised;
* the lookups allocate nothing on the machine-word path (tables of at most `2 ^ 31` slots): only
  the `Nat`-indexed probes of larger tables (`findN`, which returns an `Option`) may allocate;
* the updates write their arrays in place: no array is shared (`lean_inc`) right before it is
  updated (the bug-A pattern of the bake-off), and the updated table reuses its argument's cell
  when that is unshared.

It is not part of the benchmark executable.
-/

public section

namespace Bench.CCheck

/-! ## Lookups -/

def getDNat (m : SwissTable.HashMap Nat Nat) (a : Nat) : Nat := m.getD a 0
def getDStr (m : SwissTable.HashMap String Nat) (a : String) : Nat := m.getD a 0
def getBangNat (m : SwissTable.HashMap Nat Nat) (a : Nat) : Nat := m[a]!
def containsNat (m : SwissTable.HashMap Nat Nat) (a : Nat) : Bool := m.contains a
def containsStr (m : SwissTable.HashMap String Nat) (a : String) : Bool := m.contains a
def getKeyDStr (m : SwissTable.HashMap String Nat) (a : String) : String := m.getKeyD a ""
def setContainsNat (s : SwissTable.HashSet Nat) (a : Nat) : Bool := s.contains a
def setContainsStr (s : SwissTable.HashSet String) (a : String) : Bool := s.contains a

/-! ## Updates -/

def insertNat (m : SwissTable.HashMap Nat Nat) (a b : Nat) : SwissTable.HashMap Nat Nat := m.insert a b
def insertStr (m : SwissTable.HashMap String Nat) (a : String) (b : Nat) : SwissTable.HashMap String Nat :=
  m.insert a b
def insertIfNewNat (m : SwissTable.HashMap Nat Nat) (a b : Nat) : SwissTable.HashMap Nat Nat :=
  m.insertIfNew a b
def getThenInsertIfNewStr (m : SwissTable.HashMap String Nat) (a : String) (b : Nat) :
    Option Nat × SwissTable.HashMap String Nat :=
  m.getThenInsertIfNew? a b
def containsThenInsertNat (m : SwissTable.HashMap Nat Nat) (a b : Nat) : Bool × SwissTable.HashMap Nat Nat :=
  m.containsThenInsert a b
def eraseNat (m : SwissTable.HashMap Nat Nat) (a : Nat) : SwissTable.HashMap Nat Nat := m.erase a
def eraseStr (m : SwissTable.HashMap String Nat) (a : String) : SwissTable.HashMap String Nat := m.erase a
def modifyNat (m : SwissTable.HashMap Nat Nat) (a : Nat) : SwissTable.HashMap Nat Nat := m.modify a (· + 1)
def alterStr (m : SwissTable.HashMap String Nat) (a : String) : SwissTable.HashMap String Nat :=
  m.alter a fun | some v => some (v + 1) | none => some 0
def setInsertStr (s : SwissTable.HashSet String) (a : String) : SwissTable.HashSet String := s.insert a

/-! ## Traversal -/

def foldNat (m : SwissTable.HashMap Nat Nat) : Nat := m.fold (fun acc _ v => acc + v) 0

end Bench.CCheck
