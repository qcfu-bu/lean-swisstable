module

public import OAMap.Core.Swiss.Group

/-!
# The SwissTable core: hashing, control arrays, the model and the invariant

The first of the core's code files (`OAMap/Core/Swiss/Table.lean` documents the layout, the
algorithms and the measurements; its "Proof structure" section lists the files). This one holds
the definitions everything else is stated with:

* hashing (`hashBits`, `homeU`, `homeN`, `tagOf`), the control arrays (`emptyGroup`, `emptyCtrl`,
  `ctrlWordN`, `setCtrlN`, the erase rule on `Nat` indices `eraseCtrlN`), the guards
  (`smallShift`, `smallMask`: at most `2 ^ 31` slots) and the capacity (`capacityOf`, `lgFor`);
* the model: `Slots` (the three arrays of a table), the entry of a slot (`Slots.entryAt`) and the
  entries in slot order (`Slots.entries`, which `Table.toListModel` is);
* the invariant `WF`, bundled in `Table` as its field `wf`: the shape (unallocated, or `2 ^ lg`
  slots with the mirror), byte classes, the tag invariant, the counts, and, under
  `[EquivBEq α] [LawfulHashable α]` only, distinct keys and the probe (window) invariant;
* the specification predicates the probe lemmas conclude (`Slots.Hit`, `Slots.Absent`,
  `Slots.FreeSlot`, `NewSlot`, ...);
* the erased hypotheses of the loops (`ArrU`, `LoopU`, `ArrN`, ...): the bounds facts their array
  reads and termination measures need, threaded as `Prop` arguments (the compiler drops them).

Everything here is exposed (`@[expose]`), so that the proof files can unfold it; the layers above
the core never see it (they use only the contract names, `test/OAMapTest/SealCheck.lean`).
-/

-- Elaborated `let`s stay `let`s instead of becoming `have`s, the setting of the SwissF prototype
-- and of the bake-off harness that measured the frozen code. It changes no generated C in this
-- file today, but it does in `Table.lean`, and every code file is compiled under the same setting.
set_option cleanup.letToHave false

@[expose] public section

universe u v w w'

namespace OAMap.Core.Swiss

variable {α : Type u} {β : Type v}

/-! ## Hashing -/

/-- `⌊2^64 / φ⌋`, the multiplier of Fibonacci hashing. -/
@[inline] def fibMul : UInt64 := 0x9E3779B97F4A7C15

/-- The top `log₂ cap + 7` bits of the Fibonacci product of the hash: home slot and tag. -/
@[inline] def hashBits [Hashable α] (shift : UInt64) (a : α) : UInt64 :=
  (hash a * fibMul) >>> shift

/-- The home slot, on machine words. -/
@[inline] def homeU (q : UInt64) (mask : USize) : USize := (q >>> 7).toUSize &&& mask

/-- The home slot, on `Nat`. -/
@[inline] def homeN (q : UInt64) (cap : Nat) : Nat := (q >>> 7).toNat % cap

/-- The control byte of a full slot: the 7-bit tag. -/
@[inline] def tagOf (q : UInt64) : UInt8 := (q &&& 0x7F).toUInt8

/-! ## Control arrays -/

/-- 8 EMPTY bytes: the control array of the unallocated table (shared), and the seed of
`emptyCtrl`. -/
def emptyGroup : ByteArray := ⟨#[0xFF, 0xFF, 0xFF, 0xFF, 0xFF, 0xFF, 0xFF, 0xFF]⟩

/-- Double `b` (by appending it to itself) until it has at least `n` bytes. -/
def dblTo (n : Nat) (b : ByteArray) : ByteArray :=
  if b.size < n ∧ 0 < b.size then dblTo n (b ++ b) else b
termination_by n - b.size
decreasing_by rw [ByteArray.size_append]; omega

/-- The control array of an empty table of `cap` slots, a power of two at least 8: `cap + 8`
EMPTY bytes, built by doubling appends. -/
def emptyCtrl (cap : Nat) : ByteArray := dblTo cap emptyGroup ++ emptyGroup

/-- `ByteArray.set` keeps the size. -/
theorem size_set (c : ByteArray) (i : Nat) (b : UInt8) (h : i < c.size) :
    (c.set i b h).size = c.size := by
  cases c; simp [ByteArray.set, ByteArray.size]

/-- The 8 bytes from `i`, little-endian, at a `Nat` index: `ctrlWord` for tables beyond `2 ^ 31`
slots. -/
@[inline] def ctrlWordN (c : @& ByteArray) (i : Nat) (h : i + 8 ≤ c.size) : UInt64 :=
  (c[i]'(by omega)).toUInt64 |||
  ((c[i + 1]'(by omega)).toUInt64 <<< 8) |||
  ((c[i + 2]'(by omega)).toUInt64 <<< 16) |||
  ((c[i + 3]'(by omega)).toUInt64 <<< 24) |||
  ((c[i + 4]'(by omega)).toUInt64 <<< 32) |||
  ((c[i + 5]'(by omega)).toUInt64 <<< 40) |||
  ((c[i + 6]'(by omega)).toUInt64 <<< 48) |||
  ((c[i + 7]'(by omega)).toUInt64 <<< 56)

/-- `setCtrl` at `Nat` indices: write slot `i` and its mirror `((i + cap - 8) % cap) + 8`
(`i + cap` when `i < 8`, `i` itself otherwise). -/
@[inline] def setCtrlN (c : ByteArray) (cap i : Nat) (b : UInt8) (hi : i < c.size)
    (hm : cap + 8 ≤ c.size) (hc : 0 < cap) : ByteArray :=
  (c.set i b hi).set (((i + cap - 8) % cap) + 8) b
    (by rw [size_set]; have := Nat.mod_lt (i + cap - 8) hc; omega)

/-! ## Guards and capacity -/

/-- The machine-word guard read off `shift = 57 - log₂ cap` (`57` for the unallocated table): at
most `2 ^ 31` slots. The lookups, `erase`, `modify`, `getThenInsertIfNew?` and the traversals test
this form. -/
@[inline] def smallShift (shift : UInt64) : Bool := shift ≥ 26

/-- The machine-word guard read off `mask = cap - 1`: bit 31 clear, i.e. at most `2 ^ 31` slots.
`containsThenInsert`, `alter`, `insertFresh` and `rebuild` test this form. (The two forms are
equivalent on every table, `WF.smallMask_eq`; each operation uses the one that measured best, see
"Code shape" in `Table.lean`.) -/
@[inline] def smallMask (mask : USize) : Bool := mask &&& 0x80000000 == 0

/-- The capacity of a table of `cap` slots: `7/8` of them. -/
@[inline] def capacityOf (cap : Nat) : Nat := cap / 8 * 7

/-- `⌈log₂ n⌉`, `0` for `n ≤ 1`. -/
def clog2 (n : Nat) : Nat := if n ≤ 1 then 0 else (n - 1).log2 + 1

/-- `log₂` of the least table (at least 8 slots) whose capacity `cap / 8 * 7` holds `n`
entries. -/
def lgFor (n : Nat) : Nat := 3 + clog2 ((n + 6) / 7)

/-- The new control byte of the full slot `i` at its erasure (`needsTombstone`) and the new
`growthLeft`, on `Nat` indices: `eraseAtU`'s rule. -/
@[inline] def eraseCtrlN (ctrl : ByteArray) (size gl cap i : Nat) (hi : i < cap)
    (hc : cap + 8 ≤ ctrl.size) : ByteArray × Nat :=
  let ea := matchEmpty (ctrlWordN ctrl i (by omega))
  let eb := matchEmpty (ctrlWordN ctrl ((i + cap - 8) % cap)
    (by have := Nat.mod_lt (i + cap - 8) (show 0 < cap by omega); omega))
  let del := needsTombstone ea eb
  let ctrl := setCtrlN ctrl cap i (if del then DELETED else EMPTY) (by omega) hc (by omega)
  let full := capacityOf cap
  (ctrl, if del then (if size - 1 + gl + full / 4 < full then 0 else gl) else gl + 1)

/-! ## The model -/

/-- The three arrays of a table: control bytes (`cap` slots and the mirror of the first 8), keys
and values (`cap` slots and the placeholder cell). -/
structure Slots (α : Type u) (β : Type v) where
  /-- The control bytes. -/
  ctrl : ByteArray
  /-- The key cells. -/
  keys : Array α
  /-- The value cells. -/
  vals : Array β

namespace Slots

variable (s : Slots α β)

/-- The number of slots: the control bytes but the mirror (`0` for the unallocated table). -/
def cap : Nat := s.ctrl.size - 8

/-- The entry of slot `i`: its key and value when its control byte is FULL. -/
def entryAt (i : Nat) : Option ((_ : α) × β) :=
  match s.ctrl[i]? with
  | some c =>
    if c < 0x80 then s.keys[i]?.bind fun k => s.vals[i]?.map fun v => ⟨k, v⟩ else none
  | none => none

/-- The entries: the full slots in slot order. -/
def entries : List ((_ : α) × β) := (List.range s.cap).filterMap s.entryAt

/-- The number of DELETED slots (tombstones). -/
def numDeleted : Nat := (List.range s.cap).countP fun i => s.ctrl[i]! == DELETED

/-- Slot `i` is full: a slot whose control byte is a tag. -/
def IsFull (i : Nat) : Prop := i < s.cap ∧ s.ctrl[i]! < 0x80

/-- Every slot holds a control byte: EMPTY, DELETED or a tag. -/
def CtrlOK : Prop := ∀ i < s.cap, IsCtrl s.ctrl[i]!

/-- The tag invariant: the control byte of a full slot is the tag of its key. Unconditional: a
key is written only with its own tag, and replaced only after an exact tag match. -/
def TagInv [Hashable α] (shift : UInt64) : Prop :=
  ∀ i k, s.IsFull i → s.keys[i]? = some k → s.ctrl[i]! = tagOf (hashBits shift k)

/-- Slot `i` is lane `j` of group `k` of the triangular probe from slot `p₀`, a group the probe
reaches: none of the groups before it has an EMPTY slot. -/
def Reach (p₀ i : Nat) : Prop :=
  ∃ k < s.cap / 8, ∃ j < 8, (probePos s.cap p₀ k + j) % s.cap = i ∧
    ∀ k' < k, ∀ j' < 8, s.ctrl[(probePos s.cap p₀ k' + j') % s.cap]! ≠ EMPTY

/-- The probe (window) invariant: the probe from the home slot of every stored key reaches the
slot of that key. A lookup stops only at a group with an EMPTY slot, after its tag matches. -/
def ProbeInv [Hashable α] (shift : UInt64) : Prop :=
  ∀ i k, s.IsFull i → s.keys[i]? = some k → s.Reach (homeN (hashBits shift k) s.cap) i

/-- The stored keys are pairwise distinct (not `==`). -/
def Distinct [BEq α] : Prop :=
  ∀ i j k k', s.IsFull i → s.IsFull j → s.keys[i]? = some k → s.keys[j]? = some k' →
    (k == k') = true → i = j

/-- No stored key is `==` to `a`. -/
def Absent [BEq α] (a : α) : Prop :=
  ∀ i k, s.IsFull i → s.keys[i]? = some k → (k == a) = false

/-- Slot `i` is a hit of the probe for `a`: full, with the tag of `a`, and its key `== a` (the
stored key on the left, as Std compares). -/
def Hit [BEq α] [Hashable α] (shift : UInt64) (a : α) (i : Nat) : Prop :=
  s.IsFull i ∧ s.ctrl[i]! = tagOf (hashBits shift a) ∧ ∃ k, s.keys[i]? = some k ∧ (k == a) = true

/-- Slot `i` is a free (EMPTY or DELETED) slot that the probe from `p₀` reaches: writing a key
there keeps the probe invariant for it. -/
structure FreeSlot (p₀ i : Nat) : Prop where
  lt : i < s.cap
  free : s.ctrl[i]! = EMPTY ∨ s.ctrl[i]! = DELETED
  reach : s.Reach p₀ i

end Slots

/-- The table of `2 ^ lg` slots (`lg ≥ 3`): the control array mirrored, a key and a value cell
per slot and the placeholder cells, `mask = cap - 1` and `shift = 57 - lg`. -/
structure Alloc (s : Slots α β) (mask : USize) (shift : UInt64) (lg : Nat) : Prop where
  three_le : 3 ≤ lg
  mirrored : Mirrored s.ctrl (2 ^ lg)
  keys_size : s.keys.size = 2 ^ lg + 1
  vals_size : s.vals.size = 2 ^ lg + 1
  mask_eq : mask = (2 ^ lg - 1).toUSize
  shift_eq : shift = (57 - lg).toUInt64

/-- The unallocated table: the shared 8 EMPTY bytes, no cells, `mask = 0`, `shift = 57`. -/
structure Unalloc (s : Slots α β) (mask : USize) (shift : UInt64) : Prop where
  ctrl_eq : s.ctrl = emptyGroup
  keys_size : s.keys.size = 0
  vals_size : s.vals.size = 0
  mask_eq : mask = 0
  shift_eq : shift = 57

/-- **The invariant** of a table with arrays `s`, `size` entries, `gl` EMPTY slots that may still
be filled, slot mask `mask` and hash shift `shift`. The last two fields hold for lawful instances
only: a probe passes slots of other tags without comparing keys, so an unlawful `==` or `hash`
could break them; everything the U lemmas of the contract need is unconditional. -/
structure WF [BEq α] [Hashable α] (s : Slots α β) (size gl : Nat) (mask : USize)
    (shift : UInt64) : Prop where
  /-- Unallocated, or `2 ^ lg` slots. -/
  shape : Unalloc s mask shift ∨ ∃ lg, Alloc s mask shift lg
  /-- Every slot holds a control byte. -/
  ctrl : s.CtrlOK
  /-- Every full slot carries the tag of its key. -/
  tag : s.TagInv shift
  /-- `size` is the number of entries. -/
  size_eq : size = s.entries.length
  /-- The load bound: `growthLeft + size + #DELETED ≤ capacity`. -/
  room : gl + size + s.numDeleted ≤ capacityOf s.cap
  /-- The stored keys are distinct, for lawful instances. -/
  distinct [EquivBEq α] [LawfulHashable α] : s.Distinct
  /-- The probe invariant, for lawful instances. -/
  probe [EquivBEq α] [LawfulHashable α] : s.ProbeInv shift

/-- Where an insert writes the new key `a` with hash bits `q` (`hashBits shift a`): a free slot
that the probe of `a` reaches, or, in the unallocated table, a slot below 8 (that table has
`growthLeft = 0`, so the insert allocates first). For lawful instances `a` is absent. -/
structure NewSlot [BEq α] [Hashable α] (s : Slots α β) (shift : UInt64) (a : α) (q : UInt64)
    (i : Nat) : Prop where
  hash_eq : q = hashBits shift a
  slot : s.FreeSlot (homeN q s.cap) i ∨ (s.cap = 0 ∧ i < 8)
  absent [EquivBEq α] [LawfulHashable α] : s.Absent a

/-- What `insertFresh` needs: room for one EMPTY write, and `a` absent (for lawful instances). -/
structure FreshPre [BEq α] [Hashable α] (s : Slots α β) (gl : Nat) (a : α) : Prop where
  room : 0 < gl
  absent [EquivBEq α] [LawfulHashable α] : s.Absent a

/-- What `rebuild` into `2 ^ lg` slots needs: an allocated table that fits. -/
structure RebuildPre (s : Slots α β) (size lg : Nat) : Prop where
  alloc : 0 < s.cap
  three_le : 3 ≤ lg
  cap_le : s.cap ≤ 2 ^ lg
  size_le : size ≤ capacityOf (2 ^ lg)

/-! ## The erased hypotheses of the loops -/

/-- The group reads of a machine-word probe of a table of slot mask `mask` stay in bounds, and
slot numbers fit in 31 bits (no index computation wraps). -/
structure ArrU (ctrl : ByteArray) (mask : USize) : Prop where
  word : mask.toNat + 8 ≤ ctrl.size
  small : mask.toNat < 2 ^ 31

/-- `ArrU`, and keys are read only from an allocated table: in the unallocated one (`emptyGroup`,
mask `0`) no tag matches and the first group has an EMPTY slot (`firstGroup`). -/
structure LoopU (ctrl : ByteArray) (keys : Array α) (mask : USize) : Prop where
  arr : ArrU ctrl mask
  keys : mask.toNat < keys.size ∨ (ctrl = emptyGroup ∧ mask = 0)

/-- The control reads of a probe on `Nat` indices of a table of `cap` slots stay in bounds. -/
structure CtrlN (ctrl : ByteArray) (cap : Nat) : Prop where
  pos : 0 < cap
  word : cap + 8 ≤ ctrl.size

/-- `CtrlN`, and the key reads too. -/
structure ArrN (ctrl : ByteArray) (keys : Array α) (cap : Nat) : Prop extends CtrlN ctrl cap where
  keys : cap < keys.size

/-- The old table of a machine-word rebuild: slots up to `omask`, below `2 ^ 31`. -/
structure MoveSrcU (oc : ByteArray) (ok : Array α) (ov : Array β) (omask : USize) : Prop where
  small : omask.toNat < 2 ^ 31
  ctrl : omask.toNat < oc.size
  keys : omask.toNat < ok.size
  vals : omask.toNat < ov.size

/-- The new table of a machine-word rebuild: `nmask + 1` slots, the mirror and the placeholder
cells. -/
structure MoveDstU (nc : ByteArray) (nk : Array α) (nv : Array β) (nmask : USize) : Prop where
  arr : ArrU nc nmask
  ctrl_size : nc.size = nmask.toNat + 9
  keys_size : nk.size = nmask.toNat + 2
  vals_size : nv.size = nmask.toNat + 2

/-- The old table of a rebuild on `Nat` indices: `ocap` slots. -/
structure MoveSrcN (oc : ByteArray) (ok : Array α) (ov : Array β) (ocap : Nat) : Prop where
  ctrl : ocap ≤ oc.size
  keys : ocap ≤ ok.size
  vals : ocap ≤ ov.size

/-- The new table of a rebuild on `Nat` indices: `ncap` slots, the mirror and the placeholder
cells. -/
structure MoveDstN (nc : ByteArray) (nk : Array α) (nv : Array β) (ncap : Nat) : Prop where
  pos : 0 < ncap
  ctrl_size : nc.size = ncap + 8
  keys_size : nk.size = ncap + 1
  vals_size : nv.size = ncap + 1

/-- The arrays of a machine-word traversal of `cap` slots (a multiple of 8, at most `2 ^ 31`). -/
structure FoldU (ctrl : ByteArray) (keys : Array α) (vals : Array β) (cap : USize) : Prop where
  small : cap.toNat ≤ 2 ^ 31
  word : cap.toNat + 8 ≤ ctrl.size
  keys : cap.toNat ≤ keys.size
  vals : cap.toNat ≤ vals.size
  eight : cap.toNat % 8 = 0

/-- `p` is the start of a group of a table of `cap` slots. -/
def GroupAt (cap p : USize) : Prop := p.toNat + 8 ≤ cap.toNat ∧ p.toNat % 8 = 0

/-- The arrays of a traversal on `Nat` indices of `cap` slots (a multiple of 8). -/
structure FoldN (ctrl : ByteArray) (keys : Array α) (vals : Array β) (cap : Nat) : Prop where
  word : cap + 8 ≤ ctrl.size
  keys : cap ≤ keys.size
  vals : cap ≤ vals.size
  eight : cap % 8 = 0

/-- `p` is the start of a group of a table of `cap` slots. -/
def GroupAtN (cap p : Nat) : Prop := p + 8 ≤ cap ∧ p % 8 = 0

/-- The cells of the group at `p` of a reverse machine-word traversal. -/
structure RevGroupU (keys : Array α) (vals : Array β) (p : USize) : Prop where
  keys : p.toNat + 8 ≤ keys.size
  vals : p.toNat + 8 ≤ vals.size
  small : p.toNat ≤ 2 ^ 31

/-- The arrays of a reverse machine-word traversal of the slots below `p`. -/
structure RevAtU (ctrl : ByteArray) (keys : Array α) (vals : Array β) (p : USize) : Prop where
  word : p.toNat ≤ ctrl.size
  keys : p.toNat ≤ keys.size
  vals : p.toNat ≤ vals.size
  small : p.toNat ≤ 2 ^ 31

/-- The cells of the group at `p` of a reverse traversal on `Nat` indices. -/
structure RevGroupN (keys : Array α) (vals : Array β) (p : Nat) : Prop where
  keys : p + 8 ≤ keys.size
  vals : p + 8 ≤ vals.size

/-- The arrays of a reverse traversal on `Nat` indices of the slots below `p`. -/
structure RevAtN (ctrl : ByteArray) (keys : Array α) (vals : Array β) (p : Nat) : Prop where
  word : p ≤ ctrl.size
  keys : p ≤ keys.size
  vals : p ≤ vals.size

/-- The arrays of `filterMap`'s pass over an allocated table of `cap` slots. -/
structure FMArr (ctrl : ByteArray) (keys : Array α) (vals : Array β) (cap : Nat) : Prop where
  word : cap + 8 ≤ ctrl.size
  keys : cap < keys.size
  vals : cap ≤ vals.size

end OAMap.Core.Swiss
