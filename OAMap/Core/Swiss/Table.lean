module

public import OAMap.Core.Swiss.Group

/-!
# The SwissTable core: the table and its operations (executable code, frozen)

The 23 definitions of the core contract (`docs/ARCHITECTURE.md` §3.2) on hashbrown's generic
(non-SIMD) layout, as chosen by the bake-off (`docs/bakeoff/decision.md`). This file is the code
the verified core compiles to. It is frozen: later work adds the invariant and the proofs, and may
change the code only to make it provable (then re-measuring it against this version).

**Not proved yet.** Every array bound is `by sorry`, and every loop terminates by a measure whose
`decreasing_by` is `sorry`. The measures are the intended ones; their proofs need the invariant's
facts (at most `2 ^ 31` slots on the machine-word paths, `stride ≤ mask`, a free slot), which the
proof phase threads in as erased hypotheses. Nothing here is `partial`, and no other proof is
missing.

## Layout

`cap = 2 ^ lg` slots, `lg ≥ 3`, in three arrays (`Table`):

* `ctrl : ByteArray`, `cap + 8` bytes: control byte `ctrl[i]` of slot `i`, then a copy of
  `ctrl[0 .. 8)` (the mirror, `Swiss.Mirrored`), so that the group word of 8 bytes at any slot is
  one read that never wraps. `setCtrl` writes both copies.
* `slotKeys`, `slotVals`: `cap + 1` cells, slot `i` in cell `i` and in cell `cap` the
  placeholder pair. Free slots hold the placeholder: erase writes it back, so an erased key and
  value are released at once.
* `size`, `growthLeft` (EMPTY slots that may still be filled before a rebuild), `mask = cap - 1`,
  `shift = 57 - lg`, and `reqCap`, the capacity asked for by `emptyWithCapacity`.

Control bytes (hashbrown's): EMPTY = `0xFF`, DELETED = `0x80`, FULL = `0b0hhhhhhh`, the 7-bit tag
`h2` of the key. `q = (hash a * ⌊2^64/φ⌋) >>> shift` keeps the top `lg + 7` bits of the Fibonacci
product: the home slot is `q >>> 7` (masked), the tag `q &&& 0x7F`. Hashes are not stored; a
rebuild recomputes them, as Std does.

The empty map (`emptyWithCapacity c`, hence `∅`) allocates nothing: its `ctrl` is a shared group
of 8 EMPTY bytes (`emptyGroup`), `mask = 0`, `shift = 57`, both arrays `#[]`, and `reqCap = c`.
Every probe of it ends in its first group without reading a key, so the queries need no special
case. The first insert allocates `lgFor (max c 1)` and takes its own pair as the placeholder.

## Algorithms

* **Groups** (`OAMap.Core.Swiss.Group`): the group word `ctrlWord`, the exact per-lane tag match
  `matchTag` (no false positives), `matchEmpty`, `matchFree`, `matchFull`, `lowestLane`,
  `clearLowest`, `setCtrl`, the erase rule `needsTombstone`.
* **Probe**: triangular over groups, `pos ← (pos + stride) &&& mask` after `stride ← stride + 8`,
  for at most `cap / 8` groups (the `stride > mask` exit). A lookup (`findLoop`) walks the tag
  matches of each group lowest lane first, comparing the stored key on the left (`k == a`, as
  Std), and stops at the first group with an EMPTY byte. The insertion probe (`findInsLoop`) is
  the same walk, also remembering the first EMPTY or DELETED slot it passes.
* **Load** 7/8: `capacity = cap / 8 * 7`, with `growthLeft + size + #DELETED ≤ capacity`.
* **Insert**: one insertion probe; a hit replaces the stored key and value (Std's semantics), a
  new key is written at the first free slot (`insertNewU`, inlined at each call site). When that
  slot is EMPTY and `growthLeft = 0`, `reserveInsert` first rebuilds: into a fresh table of the
  same capacity when `size + 1 ≤ capacity / 2`, of twice the capacity otherwise.
  `containsThenInsert` (hence `insert`) has fast path C: when the home byte is EMPTY and no lane
  of the home group carries the tag, the key is new and goes to the home slot with no probe.
  `getThenInsertIfNew?` and `alter` have none (measured: the fast path costs `hashcons` 15%).
* **Rebuild** (`rebuild`): always into fresh arrays, each FULL slot moved to the first free slot
  of its probe, with no key comparison, and the inserting pair as the new placeholder (so at most
  one erased pair stays referenced, and only until the next rebuild).
* **Erase** (`eraseAtU`): EMPTY (and `growthLeft + 1`) when every 8-window around the slot has
  another EMPTY slot (`needsTombstone`), else DELETED; tombstone rule B: when the tombstones exceed
  `capacity / 4`, `growthLeft := 0`. The cells get the placeholder back. Erase never shrinks.
* **Traversals** go a group at a time over the `matchFull` mask, in slot order (`foldM`,
  `forIn`), or in reverse slot order (`foldRev`, highest lane first within a group).
* **filter** erases in place (`eraseAtN`, the erase rule) and **map** rewrites the values in place
  (`Array.mapFinIdx`); **filterMap** does both in one pass that builds the new value array. They
  compare no keys, so their model lemmas hold without lawfulness. Free cells of a new value array
  hold the first mapped value; a result with no entry is the unallocated table.

## Machine words

Every operation runs on `USize` indices on tables of at most `2 ^ 31` slots (the `…U` loops), and
on `Nat` indices beyond (the `…N` loops, the same algorithms; also executable), following the
`slotFor` pattern of the earlier verified linear-probing map: below `2 ^ 31` slots no index
computation wraps on any platform. Each operation tests this once, at its top, with `smallShift`
or `smallMask` (equivalent on every table). The bulk operations `filter`, `filterMap` and `map`
use `Nat` indices at every size.

## Fused operations

`containsThenInsert` and `getThenInsertIfNew?` each make one probe and one write, and
`insert := (containsThenInsert ..).2`, `insertIfNew := (getThenInsertIfNew? ..).2` and
`containsThenInsertIfNew := ((getThenInsertIfNew? ..).1.isSome, (getThenInsertIfNew? ..).2)`, so
the second components of the contract equalities hold by unfolding. The first components need the
U lemma that the insertion probe (with its fast path) hits exactly where the lookup probe does:
both walk the same groups and candidates, and the fast path applies only when the home group has
no candidate and an EMPTY byte, where the lookup probe stops with a miss.

## Code shape

The code was shaped by measurement against the SwissF prototype (instructions and ns per op in
the bake-off harness), and these choices are deliberate:

* The hit and the miss of each insertion probe are written out at each exit (the miss through the
  top-level `@[inline] insertNewU`), not passed as continuations: a continuation used at two
  exits becomes a join point, and the table cell taken apart at the top is then reused at only
  one of them (measured: a fresh allocation on every new key).
* The `2 ^ 31` guard is the one change against SwissF that clang does not absorb: its cold `Nat`
  branch changes the register allocation of the caller's loop. Spilled loop-carried values were
  then reloaded by one `ldp` from two separately stored stack slots, which this core cannot
  forward from the store buffer, so iterations stopped overlapping (string `getD` 2.5x slower,
  flat `insert-cap` at 10^6 1.3x; with clang's pairing pass disabled the gap disappeared). Of the
  equivalent guard forms, `smallShift` (`shift ≥ 26`) avoids it for the lookups, `erase`,
  `modify` and `getThenInsertIfNew?`, and `smallMask` (bit 31 of `mask`) for `containsThenInsert`
  and `alter`; the lookup keeps its `Nat` path inline (one call to `findN`), which measured fewer
  instructions than an out-of-line `lookupN`. This is fragile: re-measure after any change.
-/

set_option cleanup.letToHave false

public section

universe u v w w'

namespace OAMap.Core

/-- The SwissTable: control bytes, keys and values in slot order (the layout above). The fields
are core internals: code above the core reaches a table only through the contract names (checked
by `test/OAMapTest/SealCheck.lean`). -/
structure Table (α : Type u) (β : Type v) [BEq α] [Hashable α] : Type (max u v) where
  /-- The control bytes: `cap` slots, then the mirror of the first 8. -/
  ctrl : ByteArray
  /-- The key of each slot, then the placeholder key. -/
  slotKeys : Array α
  /-- The value of each slot, then the placeholder value. -/
  slotVals : Array β
  /-- The number of entries. -/
  size : Nat
  /-- How many EMPTY slots may still be filled before a rebuild. -/
  growthLeft : Nat
  /-- `cap - 1` (`0` for the unallocated table). -/
  mask : USize
  /-- `57 - log₂ cap`: `hashBits` keeps the top `log₂ cap + 7` bits of the product. -/
  shift : UInt64
  /-- The capacity asked for by `emptyWithCapacity`, used by the first insert. -/
  reqCap : Nat

namespace Swiss

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
decreasing_by all_goals sorry

/-- The control array of an empty table of `cap` slots, a power of two at least 8: `cap + 8`
EMPTY bytes, built by doubling appends. -/
def emptyCtrl (cap : Nat) : ByteArray := dblTo cap emptyGroup ++ emptyGroup

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
    (hm : cap + 8 ≤ c.size) : ByteArray :=
  (c.set i b hi).set (((i + cap - 8) % cap) + 8) b (by sorry)

/-- The machine-word guard read off `shift = 57 - log₂ cap` (`57` for the unallocated table): at
most `2 ^ 31` slots. The lookups, `erase`, `modify`, `getThenInsertIfNew?` and the traversals test
this form. -/
@[inline] def smallShift (shift : UInt64) : Bool := shift ≥ 26

/-- The machine-word guard read off `mask = cap - 1`: bit 31 clear, i.e. at most `2 ^ 31` slots.
`containsThenInsert`, `alter`, `insertFresh` and `rebuild` test this form. (The two forms are
equivalent on every table; each operation uses the one that measured best, see "Code shape".) -/
@[inline] def smallMask (mask : USize) : Bool := mask &&& 0x80000000 == 0

/-- The capacity of a table of `cap` slots: `7/8` of them. -/
@[inline] def capacityOf (cap : Nat) : Nat := cap / 8 * 7

/-- `⌈log₂ n⌉`, `0` for `n ≤ 1`. -/
def clog2 (n : Nat) : Nat := if n ≤ 1 then 0 else (n - 1).log2 + 1

/-- `log₂` of the least table (at least 8 slots) whose capacity `cap / 8 * 7` holds `n`
entries. -/
def lgFor (n : Nat) : Nat := 3 + clog2 ((n + 6) / 7)

/-! ## The model -/

/-- The entry of slot `i`: its key and value when its control byte is FULL. -/
def entryAt [BEq α] [Hashable α] (t : Table α β) (i : Nat) : Option ((_ : α) × β) :=
  match t.ctrl[i]? with
  | some c =>
    if c < 0x80 then t.slotKeys[i]?.bind fun k => t.slotVals[i]?.map fun v => ⟨k, v⟩ else none
  | none => none

/-! ## Probes on machine words (`mask < 2 ^ 31`) -/

/-- The slot of a key `== a` from the group at `pos` (the probe's step `stride`, group word `g`,
tag matches `m` still to try) on, or `mask + 1` when the probe ends without one. -/
@[specialize] def findLoop [BEq α] (ctrl : @& ByteArray) (keys : @& Array α) (a : @& α)
    (mask : USize) (rep : UInt64) (pos stride : USize) (g m : UInt64) : USize :=
  if m != 0 then
    let i := (pos + lowestLane m) &&& mask
    if keys.uget i (by sorry) == a then i
    else findLoop ctrl keys a mask rep pos stride g (clearLowest m)
  else if matchEmpty g != 0 then mask + 1
  else
    let stride := stride + 8
    if stride > mask then mask + 1
    else
      let pos := (pos + stride) &&& mask
      let g := ctrlWord ctrl pos (by sorry)
      findLoop ctrl keys a mask rep pos stride g (matchTag g rep)
termination_by (mask.toNat + 8 - stride.toNat, m.toNat)
decreasing_by all_goals sorry

/-- The slot of a key `== a`, or `mask + 1`. -/
@[inline] def findU [BEq α] [Hashable α] (ctrl : ByteArray) (keys : Array α) (mask : USize)
    (shift : UInt64) (a : α) : USize :=
  let q := hashBits shift a
  let pos := homeU q mask
  let rep := repTag (tagOf q)
  let g := ctrlWord ctrl pos (by sorry)
  findLoop ctrl keys a mask rep pos 0 g (matchTag g rep)

/-- `findLoop`, also remembering the first EMPTY or DELETED slot `ins` passed (`ins > mask`: none
yet): the slot `i ≤ mask` of a key `== a`, or `mask + 1 + ins`. -/
@[specialize] def findInsLoop [BEq α] (ctrl : @& ByteArray) (keys : @& Array α) (a : @& α)
    (mask : USize) (rep : UInt64) (pos stride : USize) (g m : UInt64) (ins : USize) : USize :=
  if m != 0 then
    let i := (pos + lowestLane m) &&& mask
    if keys.uget i (by sorry) == a then i
    else findInsLoop ctrl keys a mask rep pos stride g (clearLowest m) ins
  else
    let ins := if ins > mask then
        let f := matchFree g
        if f != 0 then (pos + lowestLane f) &&& mask else ins
      else ins
    if matchEmpty g != 0 then ins + (mask + 1)
    else
      let stride := stride + 8
      if stride > mask then ins + (mask + 1)
      else
        let pos := (pos + stride) &&& mask
        let g := ctrlWord ctrl pos (by sorry)
        findInsLoop ctrl keys a mask rep pos stride g (matchTag g rep) ins
termination_by (mask.toNat + 8 - stride.toNat, m.toNat)
decreasing_by all_goals sorry

/-- The first EMPTY or DELETED slot of the probe from the group at `pos` (step `stride`), or
`mask + 1` when the probe ends without one. -/
def findFree (ctrl : @& ByteArray) (mask pos stride : USize) : USize :=
  let f := matchFree (ctrlWord ctrl pos (by sorry))
  if f != 0 then (pos + lowestLane f) &&& mask
  else
    let stride := stride + 8
    if stride > mask then mask + 1
    else findFree ctrl mask ((pos + stride) &&& mask) stride
termination_by mask.toNat + 8 - stride.toNat
decreasing_by all_goals sorry

/-! ## Probes on `Nat` indices (tables beyond `2 ^ 31` slots) -/

/-- `findLoop` on `Nat` indices, for a table of `cap` slots: the slot of a key `== a`, if the
probe finds one. -/
@[specialize] def findLoopN [BEq α] (ctrl : @& ByteArray) (keys : @& Array α) (a : @& α)
    (cap : Nat) (rep : UInt64) (pos stride : Nat) (g m : UInt64) : Option Nat :=
  if m != 0 then
    let i := (pos + (lowestLane64 m).toNat) % cap
    if keys[i]'(by sorry) == a then some i
    else findLoopN ctrl keys a cap rep pos stride g (clearLowest m)
  else if matchEmpty g != 0 then none
  else
    let stride := stride + 8
    if cap ≤ stride then none
    else
      let pos := (pos + stride) % cap
      let g := ctrlWordN ctrl pos (by sorry)
      findLoopN ctrl keys a cap rep pos stride g (matchTag g rep)
termination_by (cap + 8 - stride, m.toNat)
decreasing_by all_goals sorry

/-- The slot of a key `== a` in a table of `cap` slots, if any (`findU` on `Nat` indices). -/
@[specialize] def findN [BEq α] [Hashable α] (ctrl : @& ByteArray) (keys : @& Array α)
    (cap : Nat) (shift : UInt64) (a : @& α) : Option Nat :=
  let q := hashBits shift a
  let pos := homeN q cap
  let rep := repTag (tagOf q)
  let g := ctrlWordN ctrl pos (by sorry)
  findLoopN ctrl keys a cap rep pos 0 g (matchTag g rep)

/-- `findInsLoop` on `Nat` indices: `.inl i` at the slot `i` of a key `== a`, else `.inr ins`
with `ins` the first free slot passed (`cap` when none). -/
@[specialize] def findInsLoopN [BEq α] (ctrl : @& ByteArray) (keys : @& Array α) (a : @& α)
    (cap : Nat) (rep : UInt64) (pos stride : Nat) (g m : UInt64) (ins : Nat) : Nat ⊕ Nat :=
  if m != 0 then
    let i := (pos + (lowestLane64 m).toNat) % cap
    if keys[i]'(by sorry) == a then .inl i
    else findInsLoopN ctrl keys a cap rep pos stride g (clearLowest m) ins
  else
    let ins := if cap ≤ ins then
        let f := matchFree g
        if f != 0 then (pos + (lowestLane64 f).toNat) % cap else ins
      else ins
    if matchEmpty g != 0 then .inr ins
    else
      let stride := stride + 8
      if cap ≤ stride then .inr ins
      else
        let pos := (pos + stride) % cap
        let g := ctrlWordN ctrl pos (by sorry)
        findInsLoopN ctrl keys a cap rep pos stride g (matchTag g rep) ins
termination_by (cap + 8 - stride, m.toNat)
decreasing_by all_goals sorry

/-- The insertion probe of `Table.containsThenInsert` on `Nat` indices, for a table of `cap`
slots, with fast path C: `.inl i` at the slot `i` of a key `== a`, else `.inr j` with `j` the
first free slot of the probe. -/
@[inline] def insSlotN [BEq α] (ctrl : ByteArray) (keys : Array α) (a : α) (cap : Nat)
    (q : UInt64) : Nat ⊕ Nat :=
  let pos := homeN q cap
  let rep := repTag (tagOf q)
  let g := ctrlWordN ctrl pos (by sorry)
  let mt := matchTag g rep
  if mt == 0 && g &&& 0xFF == 0xFF then .inr pos
  else findInsLoopN ctrl keys a cap rep pos 0 g mt cap

/-- `findFree` on `Nat` indices: the first free slot of the probe from `pos`, or `cap`. -/
def findFreeN (ctrl : @& ByteArray) (cap pos stride : Nat) : Nat :=
  let f := matchFree (ctrlWordN ctrl pos (by sorry))
  if f != 0 then (pos + (lowestLane64 f).toNat) % cap
  else
    let stride := stride + 8
    if cap ≤ stride then cap
    else findFreeN ctrl cap ((pos + stride) % cap) stride
termination_by cap + 8 - stride
decreasing_by all_goals sorry

/-! ## Allocation and rebuild -/

/-- An empty table of `2 ^ lg` slots (`lg ≥ 3`) with placeholders `k0` and `v0`. -/
def emptyTable [BEq α] [Hashable α] (lg : Nat) (k0 : α) (v0 : β) (req : Nat) : Table α β :=
  let cap := 2 ^ lg
  ⟨emptyCtrl cap, Array.replicate (cap + 1) k0, Array.replicate (cap + 1) v0, 0, capacityOf cap,
    (cap - 1).toUSize, (57 - lg).toUInt64, req⟩

/-- Move every FULL slot `i ≤ omask` of the old table into the new one, at the first free slot of
its probe there (hash recomputed, no key comparison). -/
@[specialize] def moveLoop [Hashable α] (oc : @& ByteArray) (ok : @& Array α) (ov : @& Array β)
    (omask i : USize) (nc : ByteArray) (nk : Array α) (nv : Array β) (nmask : USize)
    (nshift : UInt64) : ByteArray × Array α × Array β :=
  if i > omask then (nc, nk, nv)
  else if oc.uget i (by sorry) &&& 0x80 == 0 then
    let k := ok.uget i (by sorry)
    let q := hashBits nshift k
    let j := findFree nc nmask (homeU q nmask) 0
    moveLoop oc ok ov omask (i + 1) (setCtrl nc nmask j (tagOf q) (by sorry) (by sorry))
      (nk.uset j k (by sorry)) (nv.uset j (ov.uget i (by sorry)) (by sorry)) nmask nshift
  else moveLoop oc ok ov omask (i + 1) nc nk nv nmask nshift
termination_by omask.toNat + 1 - i.toNat
decreasing_by all_goals sorry

/-- `moveLoop` on `Nat` indices: the old table has `ocap` slots, the new one `ncap`. -/
@[specialize] def moveLoopN [Hashable α] (oc : @& ByteArray) (ok : @& Array α) (ov : @& Array β)
    (ocap i : Nat) (nc : ByteArray) (nk : Array α) (nv : Array β) (ncap : Nat)
    (nshift : UInt64) : ByteArray × Array α × Array β :=
  if h : i < ocap then
    if oc[i]'(by sorry) &&& 0x80 == 0 then
      let k := ok[i]'(by sorry)
      let q := hashBits nshift k
      let j := findFreeN nc ncap (homeN q ncap) 0
      moveLoopN oc ok ov ocap (i + 1) (setCtrlN nc ncap j (tagOf q) (by sorry) (by sorry))
        (nk.set j k (by sorry)) (nv.set j (ov[i]'(by sorry)) (by sorry)) ncap nshift
    else moveLoopN oc ok ov ocap (i + 1) nc nk nv ncap nshift
  else (nc, nk, nv)
termination_by ocap - i

/-- Rebuild into a fresh table of `2 ^ lg` slots holding the same entries, with placeholders `k0`
and `v0` (the pair being inserted). -/
@[specialize] def rebuild [BEq α] [Hashable α] (t : Table α β) (lg : Nat) (k0 : α) (v0 : β) :
    Table α β :=
  let ⟨ctrl, keys, vals, size, _, mask, _, req⟩ := t
  let cap := 2 ^ lg
  let nmask := (cap - 1).toUSize
  let nshift := (57 - lg).toUInt64
  let nc := ctrl.propagateMark (emptyCtrl cap)
  let nk := keys.propagateMark (Array.replicate (cap + 1) k0)
  let nv := vals.propagateMark (Array.replicate (cap + 1) v0)
  let (nc, nk, nv) :=
    if smallMask nmask then moveLoop ctrl keys vals mask 0 nc nk nv nmask nshift
    else moveLoopN ctrl keys vals (ctrl.size - 8) 0 nc nk nv cap nshift
  ⟨nc, nk, nv, size, capacityOf cap - size, nmask, nshift, req⟩

/-- Insert the absent key `a ↦ b` into a table with room: at the first free slot of its probe. -/
@[specialize] def insertFresh [BEq α] [Hashable α] (t : Table α β) (a : α) (b : β) :
    Table α β :=
  let ⟨ctrl, keys, vals, size, gl, mask, shift, req⟩ := t
  let q := hashBits shift a
  if smallMask mask then
    let i := findFree ctrl mask (homeU q mask) 0
    let old := ctrl.uget i (by sorry)
    ⟨setCtrl ctrl mask i (tagOf q) (by sorry) (by sorry), keys.uset i a (by sorry),
      vals.uset i b (by sorry), size + 1, if old == EMPTY then gl - 1 else gl, mask, shift, req⟩
  else
    let cap := ctrl.size - 8
    let i := findFreeN ctrl cap (homeN q cap) 0
    let old := ctrl[i]'(by sorry)
    ⟨setCtrlN ctrl cap i (tagOf q) (by sorry) (by sorry), keys.set i a (by sorry),
      vals.set i b (by sorry), size + 1, if old == EMPTY then gl - 1 else gl, mask, shift, req⟩

/-- Insert the absent key `a ↦ b` when no EMPTY slot may be filled: allocate the unallocated
table, or rebuild at the same capacity (when `size + 1 ≤ capacity / 2`) or at twice it, then
insert. -/
@[specialize] def reserveInsert [BEq α] [Hashable α] (t : Table α β) (a : α) (b : β) :
    Table α β :=
  let t :=
    if t.slotKeys.size == 0 then emptyTable (lgFor (max t.reqCap 1)) a b t.reqCap
    else
      let full := capacityOf (t.ctrl.size - 8)
      if t.size + 1 ≤ full / 2 then rebuild t (lgFor full) a b
      else rebuild t (lgFor (max (t.size + 1) (full + 1))) a b
  insertFresh t a b

/-! ## Writes on machine words -/

/-- Write the new key `a ↦ b` (hash bits `q`) at the free slot `i` of its probe, after a rebuild
when `i` is EMPTY and `growthLeft = 0`. -/
@[inline] def insertNewU [BEq α] [Hashable α] (t : Table α β) (a : α) (b : β) (q : UInt64)
    (i : USize) : Table α β :=
  let ⟨ctrl, keys, vals, size, gl, mask, shift, req⟩ := t
  let old := ctrl.uget i (by sorry)
  if old == EMPTY then
    if gl == 0 then reserveInsert ⟨ctrl, keys, vals, size, gl, mask, shift, req⟩ a b
    else
      ⟨setCtrl ctrl mask i (tagOf q) (by sorry) (by sorry), keys.uset i a (by sorry),
        vals.uset i b (by sorry), size + 1, gl - 1, mask, shift, req⟩
  else
    ⟨setCtrl ctrl mask i (tagOf q) (by sorry) (by sorry), keys.uset i a (by sorry),
      vals.uset i b (by sorry), size + 1, gl, mask, shift, req⟩

/-- Erase the full slot `i`: EMPTY when every 8-window around it has another EMPTY slot (and
`growthLeft + 1`), else DELETED (and, past `capacity / 4` tombstones, `growthLeft := 0`); the key
and value cells get the placeholders back. -/
@[specialize] def eraseAtU [BEq α] [Hashable α] (t : Table α β) (i : USize) : Table α β :=
  let ⟨ctrl, keys, vals, size, gl, mask, shift, req⟩ := t
  let ea := matchEmpty (ctrlWord ctrl i (by sorry))
  let eb := matchEmpty (ctrlWord ctrl ((i - 8) &&& mask) (by sorry))
  let del := needsTombstone ea eb
  let ctrl := setCtrl ctrl mask i (if del then DELETED else EMPTY) (by sorry) (by sorry)
  let p := mask + 1
  let k0 := keys.uget p (by sorry)
  let v0 := vals.uget p (by sorry)
  let full := ((mask + 1) >>> 3) * 7
  let gl := if del then
      (if (size - 1).toUSize + gl.toUSize + (full >>> 2) < full then 0 else gl)
    else gl + 1
  ⟨ctrl, keys.uset i k0 (by sorry), vals.uset i v0 (by sorry), size - 1, gl, mask, shift, req⟩

/-- Replace the key of the full slot `i` by `a` and its value `v` by `f v` (taken out of its cell
first, so that `f` sees it unshared). -/
@[inline] def modifyAtU [BEq α] [Hashable α] (t : Table α β) (i : USize) (a : α) (f : β → β) :
    Table α β :=
  let ⟨ctrl, keys, vals, size, gl, mask, shift, req⟩ := t
  let v := vals.uget i (by sorry)
  let vals := vals.uset i (vals.uget (mask + 1) (by sorry)) (by sorry)
  ⟨ctrl, keys.uset i a (by sorry), vals.uset i (f v) (by sorry), size, gl, mask, shift, req⟩

/-! ## Writes on `Nat` indices -/

/-- `insertNewU` on `Nat` indices. -/
@[specialize] def insertNewN [BEq α] [Hashable α] (t : Table α β) (a : α) (b : β) (q : UInt64)
    (i : Nat) : Table α β :=
  let ⟨ctrl, keys, vals, size, gl, mask, shift, req⟩ := t
  let cap := ctrl.size - 8
  let old := ctrl[i]'(by sorry)
  if old == EMPTY then
    if gl == 0 then reserveInsert ⟨ctrl, keys, vals, size, gl, mask, shift, req⟩ a b
    else
      ⟨setCtrlN ctrl cap i (tagOf q) (by sorry) (by sorry), keys.set i a (by sorry),
        vals.set i b (by sorry), size + 1, gl - 1, mask, shift, req⟩
  else
    ⟨setCtrlN ctrl cap i (tagOf q) (by sorry) (by sorry), keys.set i a (by sorry),
      vals.set i b (by sorry), size + 1, gl, mask, shift, req⟩

/-- The new control byte of the full slot `i` at its erasure (`needsTombstone`) and the new
`growthLeft`, on `Nat` indices: `eraseAtU`'s rule. -/
@[inline] def eraseCtrlN (ctrl : ByteArray) (size gl cap i : Nat) : ByteArray × Nat :=
  let ea := matchEmpty (ctrlWordN ctrl i (by sorry))
  let eb := matchEmpty (ctrlWordN ctrl ((i + cap - 8) % cap) (by sorry))
  let del := needsTombstone ea eb
  let ctrl := setCtrlN ctrl cap i (if del then DELETED else EMPTY) (by sorry) (by sorry)
  let full := capacityOf cap
  (ctrl, if del then (if size - 1 + gl + full / 4 < full then 0 else gl) else gl + 1)

/-- `eraseAtU` on `Nat` indices. -/
@[specialize] def eraseAtN [BEq α] [Hashable α] (t : Table α β) (i : Nat) : Table α β :=
  let ⟨ctrl, keys, vals, size, gl, mask, shift, req⟩ := t
  let cap := ctrl.size - 8
  let (ctrl, gl) := eraseCtrlN ctrl size gl cap i
  let k0 := keys[cap]'(by sorry)
  let v0 := vals[cap]'(by sorry)
  ⟨ctrl, keys.set i k0 (by sorry), vals.set i v0 (by sorry), size - 1, gl, mask, shift, req⟩

/-- `modifyAtU` on `Nat` indices. -/
@[inline] def modifyAtN [BEq α] [Hashable α] (t : Table α β) (i : Nat) (a : α) (f : β → β) :
    Table α β :=
  let ⟨ctrl, keys, vals, size, gl, mask, shift, req⟩ := t
  let cap := ctrl.size - 8
  let v := vals[i]'(by sorry)
  let vals := vals.set i (vals[cap]'(by sorry)) (by sorry)
  ⟨ctrl, keys.set i a (by sorry), vals.set i (f v) (by sorry), size, gl, mask, shift, req⟩

/-! ## Operations on `Nat` indices (out of line) -/

/-- `Table.erase` on `Nat` indices. -/
@[specialize] def eraseN [BEq α] [Hashable α] (t : Table α β) (a : α) : Table α β :=
  match findN t.ctrl t.slotKeys (t.ctrl.size - 8) t.shift a with
  | some i => eraseAtN t i
  | none => t

/-- `Table.modify` on `Nat` indices. -/
@[specialize] def modifyN [BEq α] [Hashable α] (t : Table α β) (a : α) (f : β → β) :
    Table α β :=
  match findN t.ctrl t.slotKeys (t.ctrl.size - 8) t.shift a with
  | some i => modifyAtN t i a f
  | none => t

/-- `Table.containsThenInsert` on `Nat` indices. -/
@[specialize] def containsThenInsertN [BEq α] [Hashable α] (t : Table α β) (a : α) (b : β) :
    Bool × Table α β :=
  let ⟨ctrl, keys, vals, size, gl, mask, shift, req⟩ := t
  let q := hashBits shift a
  match insSlotN ctrl keys a (ctrl.size - 8) q with
  | .inl i =>
    (true, ⟨ctrl, keys.set i a (by sorry), vals.set i b (by sorry), size, gl, mask, shift, req⟩)
  | .inr j => (false, insertNewN ⟨ctrl, keys, vals, size, gl, mask, shift, req⟩ a b q j)

/-- `Table.getThenInsertIfNew?` on `Nat` indices. -/
@[specialize] def getThenInsertIfNewN [BEq α] [Hashable α] (t : Table α β) (a : α) (b : β) :
    Option β × Table α β :=
  let ⟨ctrl, keys, vals, size, gl, mask, shift, req⟩ := t
  let cap := ctrl.size - 8
  let q := hashBits shift a
  let pos := homeN q cap
  let rep := repTag (tagOf q)
  let g := ctrlWordN ctrl pos (by sorry)
  match findInsLoopN ctrl keys a cap rep pos 0 g (matchTag g rep) cap with
  | .inl i => (some (vals[i]'(by sorry)), ⟨ctrl, keys, vals, size, gl, mask, shift, req⟩)
  | .inr j => (none, insertNewN ⟨ctrl, keys, vals, size, gl, mask, shift, req⟩ a b q j)

/-- `Table.alter` on `Nat` indices. -/
@[specialize] def alterN [BEq α] [Hashable α] (t : Table α β) (a : α)
    (f : Option β → Option β) : Table α β :=
  let ⟨ctrl, keys, vals, size, gl, mask, shift, req⟩ := t
  let cap := ctrl.size - 8
  let q := hashBits shift a
  let pos := homeN q cap
  let rep := repTag (tagOf q)
  let g := ctrlWordN ctrl pos (by sorry)
  match findInsLoopN ctrl keys a cap rep pos 0 g (matchTag g rep) cap with
  | .inl i =>
    let v := vals[i]'(by sorry)
    let vals := vals.set i (vals[cap]'(by sorry)) (by sorry)
    match f (some v) with
    | some v' =>
      ⟨ctrl, keys.set i a (by sorry), vals.set i v' (by sorry), size, gl, mask, shift, req⟩
    | none => eraseAtN ⟨ctrl, keys, vals, size, gl, mask, shift, req⟩ i
  | .inr j =>
    match f none with
    | some v' => insertNewN ⟨ctrl, keys, vals, size, gl, mask, shift, req⟩ a v' q j
    | none => ⟨ctrl, keys, vals, size, gl, mask, shift, req⟩

/-! ## Traversals on machine words -/

/-- `foldM` from the full lanes `fm` of the group at `p` on, slot order; `cap` slots. -/
@[specialize] def foldMLoop {ε : Type w} {m : Type w → Type w'} [Monad m] (f : ε → α → β → m ε)
    (ctrl : @& ByteArray) (keys : @& Array α) (vals : @& Array β) (cap p : USize) (fm : UInt64)
    (acc : ε) : m ε :=
  if fm != 0 then
    let i := p + lowestLane fm
    do
      let acc ← f acc (keys.uget i (by sorry)) (vals.uget i (by sorry))
      foldMLoop f ctrl keys vals cap p (clearLowest fm) acc
  else
    let p := p + 8
    if p < cap then foldMLoop f ctrl keys vals cap p (matchFull (ctrlWord ctrl p (by sorry))) acc
    else pure acc
termination_by (cap.toNat + 8 - p.toNat, fm.toNat)
decreasing_by all_goals sorry

/-- `forIn` from the full lanes `fm` of the group at `p` on, slot order, with early exit. -/
@[specialize] def forInLoop {ε : Type w} {m : Type w → Type w'} [Monad m]
    (f : α → β → ε → m (ForInStep ε)) (ctrl : @& ByteArray) (keys : @& Array α)
    (vals : @& Array β) (cap p : USize) (fm : UInt64) (acc : ε) : m ε :=
  if fm != 0 then
    let i := p + lowestLane fm
    do
      match ← f (keys.uget i (by sorry)) (vals.uget i (by sorry)) acc with
      | .done acc => pure acc
      | .yield acc => forInLoop f ctrl keys vals cap p (clearLowest fm) acc
  else
    let p := p + 8
    if p < cap then forInLoop f ctrl keys vals cap p (matchFull (ctrlWord ctrl p (by sorry))) acc
    else pure acc
termination_by (cap.toNat + 8 - p.toNat, fm.toNat)
decreasing_by all_goals sorry

/-- Fold over the full lanes `fm` of the group at `p`, highest lane first. -/
@[specialize] def foldRevGroup {ε : Type w} (f : ε → α → β → ε) (keys : @& Array α)
    (vals : @& Array β) (p : USize) (fm : UInt64) (acc : ε) : ε :=
  if fm != 0 then
    let i := p + lowestLane fm
    f (foldRevGroup f keys vals p (clearLowest fm) acc) (keys.uget i (by sorry))
      (vals.uget i (by sorry))
  else acc
termination_by fm.toNat
decreasing_by all_goals sorry

/-- `foldRev` over the groups below slot `p`, last group first. -/
@[specialize] def foldRevLoop {ε : Type w} (f : ε → α → β → ε) (ctrl : @& ByteArray)
    (keys : @& Array α) (vals : @& Array β) (p : USize) (acc : ε) : ε :=
  if p < 8 then acc
  else
    let p := p - 8
    let acc := foldRevGroup f keys vals p (matchFull (ctrlWord ctrl p (by sorry))) acc
    foldRevLoop f ctrl keys vals p acc
termination_by p.toNat
decreasing_by all_goals sorry

/-! ## Traversals on `Nat` indices -/

/-- `foldMLoop` on `Nat` indices. -/
@[specialize] def foldMLoopN {ε : Type w} {m : Type w → Type w'} [Monad m] (f : ε → α → β → m ε)
    (ctrl : @& ByteArray) (keys : @& Array α) (vals : @& Array β) (cap p : Nat) (fm : UInt64)
    (acc : ε) : m ε :=
  if fm != 0 then
    let i := p + (lowestLane64 fm).toNat
    do
      let acc ← f acc (keys[i]'(by sorry)) (vals[i]'(by sorry))
      foldMLoopN f ctrl keys vals cap p (clearLowest fm) acc
  else
    let p := p + 8
    if p < cap then
      foldMLoopN f ctrl keys vals cap p (matchFull (ctrlWordN ctrl p (by sorry))) acc
    else pure acc
termination_by (cap + 8 - p, fm.toNat)
decreasing_by all_goals sorry

/-- `forInLoop` on `Nat` indices. -/
@[specialize] def forInLoopN {ε : Type w} {m : Type w → Type w'} [Monad m]
    (f : α → β → ε → m (ForInStep ε)) (ctrl : @& ByteArray) (keys : @& Array α)
    (vals : @& Array β) (cap p : Nat) (fm : UInt64) (acc : ε) : m ε :=
  if fm != 0 then
    let i := p + (lowestLane64 fm).toNat
    do
      match ← f (keys[i]'(by sorry)) (vals[i]'(by sorry)) acc with
      | .done acc => pure acc
      | .yield acc => forInLoopN f ctrl keys vals cap p (clearLowest fm) acc
  else
    let p := p + 8
    if p < cap then
      forInLoopN f ctrl keys vals cap p (matchFull (ctrlWordN ctrl p (by sorry))) acc
    else pure acc
termination_by (cap + 8 - p, fm.toNat)
decreasing_by all_goals sorry

/-- `foldRevGroup` on `Nat` indices. -/
@[specialize] def foldRevGroupN {ε : Type w} (f : ε → α → β → ε) (keys : @& Array α)
    (vals : @& Array β) (p : Nat) (fm : UInt64) (acc : ε) : ε :=
  if fm != 0 then
    let i := p + (lowestLane64 fm).toNat
    f (foldRevGroupN f keys vals p (clearLowest fm) acc) (keys[i]'(by sorry)) (vals[i]'(by sorry))
  else acc
termination_by fm.toNat
decreasing_by all_goals sorry

/-- `foldRevLoop` on `Nat` indices. -/
@[specialize] def foldRevLoopN {ε : Type w} (f : ε → α → β → ε) (ctrl : @& ByteArray)
    (keys : @& Array α) (vals : @& Array β) (p : Nat) (acc : ε) : ε :=
  if p < 8 then acc
  else
    let p := p - 8
    let acc := foldRevGroupN f keys vals p (matchFull (ctrlWordN ctrl p (by sorry))) acc
    foldRevLoopN f ctrl keys vals p acc
termination_by p

/-! ## Bulk operations (on `Nat` indices) -/

/-- Erase, in slot order from slot `i` on, every entry that `f` rejects. -/
@[specialize] def filterLoop [BEq α] [Hashable α] (f : α → β → Bool) (cap i : Nat)
    (t : Table α β) : Table α β :=
  if i < cap then
    if t.ctrl[i]'(by sorry) < 0x80 then
      if f (t.slotKeys[i]'(by sorry)) (t.slotVals[i]'(by sorry)) then filterLoop f cap (i + 1) t
      else filterLoop f cap (i + 1) (eraseAtN t i)
    else filterLoop f cap (i + 1) t
  else t
termination_by cap - i

/-- The first full slot from slot `i` on, if any. -/
def firstFull (ctrl : @& ByteArray) (cap i : Nat) : Option Nat :=
  if i < cap then
    if ctrl[i]'(by sorry) < 0x80 then some i else firstFull ctrl cap (i + 1)
  else none
termination_by cap - i

/-- The first full slot from slot `i` on whose entry `f` maps to `some`, with that value. -/
@[specialize] def firstSome {γ : Type w} (f : α → β → Option γ) (ctrl : @& ByteArray)
    (keys : @& Array α) (vals : @& Array β) (cap i : Nat) : Option (Nat × γ) :=
  if i < cap then
    if ctrl[i]'(by sorry) < 0x80 then
      match f (keys[i]'(by sorry)) (vals[i]'(by sorry)) with
      | some c => some (i, c)
      | none => firstSome f ctrl keys vals cap (i + 1)
    else firstSome f ctrl keys vals cap (i + 1)
  else none
termination_by cap - i

/-- `filterMap`'s pass over cells `i .. cap` (cell `cap` is the placeholder), building the new
value array `out`: the entries of slots below `i0` were rejected (`firstSome`), slot `i0` maps to
`c0`, and every later entry is mapped now; a rejected entry is erased in place (`eraseCtrlN`, its
key cell gets the placeholder key), and every free cell of `out` gets `c0`. -/
@[specialize] def filterMapLoop {γ : Type w} (f : α → β → Option γ) (vals : @& Array β)
    (cap i0 : Nat) (c0 : γ) (i : Nat) (ctrl : ByteArray) (keys : Array α) (size gl : Nat)
    (out : Array γ) : ByteArray × Array α × Nat × Nat × Array γ :=
  if i < cap then
    if ctrl[i]'(by sorry) < 0x80 then
      if i < i0 then
        let (ctrl, gl) := eraseCtrlN ctrl size gl cap i
        let keys := keys.set i (keys[cap]'(by sorry)) (by sorry)
        filterMapLoop f vals cap i0 c0 (i + 1) ctrl keys (size - 1) gl (out.push c0)
      else if i = i0 then
        filterMapLoop f vals cap i0 c0 (i + 1) ctrl keys size gl (out.push c0)
      else
        match f (keys[i]'(by sorry)) (vals[i]'(by sorry)) with
        | some c => filterMapLoop f vals cap i0 c0 (i + 1) ctrl keys size gl (out.push c)
        | none =>
          let (ctrl, gl) := eraseCtrlN ctrl size gl cap i
          let keys := keys.set i (keys[cap]'(by sorry)) (by sorry)
          filterMapLoop f vals cap i0 c0 (i + 1) ctrl keys (size - 1) gl (out.push c0)
    else filterMapLoop f vals cap i0 c0 (i + 1) ctrl keys size gl (out.push c0)
  else (ctrl, keys, size, gl, out.push c0)
termination_by cap - i

end Swiss

namespace Table

open Swiss

variable {α : Type u} {β : Type v} {γ : Type w} [BEq α] [Hashable α]

/-! ## The 23 primitive definitions -/

/-- The entries of the table: its full slots in slot order. -/
def toListModel (t : Table α β) : List ((_ : α) × β) :=
  (List.range (t.ctrl.size - 8)).filterMap (entryAt t)

/-- The empty table, with room for `capacity` entries once the first insert allocates it: it
allocates nothing (a shared group of 8 EMPTY control bytes, no slots). -/
def emptyWithCapacity (capacity : Nat) : Table α β :=
  ⟨emptyGroup, #[], #[], 0, 0, 0, 57, capacity⟩

/-- The number of slots, counting for the unallocated table the slots its first insert allocates
(so it is positive, as Std's bucket count is). -/
def numBuckets (t : Table α β) : Nat :=
  if t.slotKeys.size == 0 then 2 ^ lgFor (max t.reqCap 1) else t.ctrl.size - 8

/-- The identity; at runtime it makes the three arrays unique and marks them linear, as Std's
`Raw.markLinear` does for its bucket array. -/
@[expose] def markLinear (t : Table α β) : Table α β :=
  ⟨t.ctrl.markLinear, t.slotKeys.markLinear, t.slotVals.markLinear, t.size, t.growthLeft, t.mask,
    t.shift, t.reqCap⟩

/-- One probe for `a`: `found k v` on the stored key `k == a` and its value, `missing ()` when
there is none. -/
@[inline] def lookup {σ : Type w} (t : Table α β) (a : α) (found : α → β → σ)
    (missing : Unit → σ) : σ :=
  if smallShift t.shift then
    let i := findU t.ctrl t.slotKeys t.mask t.shift a
    if i ≤ t.mask then found (t.slotKeys.uget i (by sorry)) (t.slotVals.uget i (by sorry))
    else missing ()
  else
    match findN t.ctrl t.slotKeys (t.ctrl.size - 8) t.shift a with
    | some i => found (t.slotKeys[i]'(by sorry)) (t.slotVals[i]'(by sorry))
    | none => missing ()

/-- Whether a stored key is `==` to `a`. -/
@[inline] def contains (t : Table α β) (a : α) : Bool :=
  t.lookup a (fun _ _ => true) (fun _ => false)

/-- `lookupMem` on `Nat` indices (tables beyond `2 ^ 31` slots). -/
@[specialize] def lookupMemN {σ : Type w} (t : Table α β) (a : α)
    (hm : ¬smallShift t.shift = true) (h : t.contains a = true) (found : α → β → σ) : σ :=
  match he : findN t.ctrl t.slotKeys (t.ctrl.size - 8) t.shift a with
  | some i => found (t.slotKeys[i]'(by sorry)) (t.slotVals[i]'(by sorry))
  | none => absurd h (by simp [contains, lookup, hm, he])

/-- One probe for a key known to be present: `found k v` on the stored key and its value. -/
@[inline] def lookupMem {σ : Type w} (t : Table α β) (a : α) (h : t.contains a = true)
    (found : α → β → σ) : σ :=
  if hm : smallShift t.shift then
    let i := findU t.ctrl t.slotKeys t.mask t.shift a
    if hi : i ≤ t.mask then found (t.slotKeys.uget i (by sorry)) (t.slotVals.uget i (by sorry))
    else absurd h (by simp [contains, lookup, hm, i, hi])
  else lookupMemN t a hm h found

/-- Insert `a ↦ b`, also returning whether a key `== a` was present; that key is replaced by `a`
and its value by `b`. One probe. -/
@[inline] def containsThenInsert (t : Table α β) (a : α) (b : β) : Bool × Table α β :=
  let ⟨ctrl, keys, vals, size, gl, mask, shift, req⟩ := t
  if smallMask mask then
    let q := hashBits shift a
    let pos := homeU q mask
    let rep := repTag (tagOf q)
    let g := ctrlWord ctrl pos (by sorry)
    let mt := matchTag g rep
    -- Fast path C: the home byte is EMPTY and no lane of the home group carries the tag, so the
    -- key is new and goes to the home slot (an address known before the group load returns).
    if mt == 0 then
      if g &&& 0xFF == 0xFF then
        (false, insertNewU ⟨ctrl, keys, vals, size, gl, mask, shift, req⟩ a b q pos)
      else
        let r := findInsLoop ctrl keys a mask rep pos 0 g mt (mask + 1)
        if r ≤ mask then
          (true, ⟨ctrl, keys.uset r a (by sorry), vals.uset r b (by sorry), size, gl, mask, shift,
            req⟩)
        else
          (false, insertNewU ⟨ctrl, keys, vals, size, gl, mask, shift, req⟩ a b q (r - (mask + 1)))
    else
      let r := findInsLoop ctrl keys a mask rep pos 0 g mt (mask + 1)
      if r ≤ mask then
        (true, ⟨ctrl, keys.uset r a (by sorry), vals.uset r b (by sorry), size, gl, mask, shift,
          req⟩)
      else
        (false, insertNewU ⟨ctrl, keys, vals, size, gl, mask, shift, req⟩ a b q (r - (mask + 1)))
  else containsThenInsertN ⟨ctrl, keys, vals, size, gl, mask, shift, req⟩ a b

/-- Insert `a ↦ b`, replacing the stored key `== a` (by `a`) and its value if present. -/
@[inline] def insert (t : Table α β) (a : α) (b : β) : Table α β :=
  (t.containsThenInsert a b).2

/-- The value of the stored key `== a` if there is one (the table unchanged), else `none` and the
table with `a ↦ b` inserted. One probe. -/
@[inline] def getThenInsertIfNew? (t : Table α β) (a : α) (b : β) : Option β × Table α β :=
  let ⟨ctrl, keys, vals, size, gl, mask, shift, req⟩ := t
  if smallShift shift then
    let q := hashBits shift a
    let pos := homeU q mask
    let rep := repTag (tagOf q)
    let g := ctrlWord ctrl pos (by sorry)
    let r := findInsLoop ctrl keys a mask rep pos 0 g (matchTag g rep) (mask + 1)
    if r ≤ mask then
      (some (vals.uget r (by sorry)), ⟨ctrl, keys, vals, size, gl, mask, shift, req⟩)
    else
      (none, insertNewU ⟨ctrl, keys, vals, size, gl, mask, shift, req⟩ a b q (r - (mask + 1)))
  else getThenInsertIfNewN ⟨ctrl, keys, vals, size, gl, mask, shift, req⟩ a b

/-- Insert `a ↦ b` unless a key `== a` is stored. -/
@[inline] def insertIfNew (t : Table α β) (a : α) (b : β) : Table α β :=
  (t.getThenInsertIfNew? a b).2

/-- `insertIfNew`, also returning whether a key `== a` was present. One probe. -/
@[inline] def containsThenInsertIfNew (t : Table α β) (a : α) (b : β) : Bool × Table α β :=
  let r := t.getThenInsertIfNew? a b
  (r.1.isSome, r.2)

/-- Remove the entry of the stored key `== a`; the table itself when there is none. -/
@[inline] def erase (t : Table α β) (a : α) : Table α β :=
  if smallShift t.shift then
    let i := findU t.ctrl t.slotKeys t.mask t.shift a
    if i ≤ t.mask then eraseAtU t i else t
  else eraseN t a

/-- Replace the value `v?` of `a` (`none` when absent) by `f v?`: `some` stores it under the key
`a` (replacing the stored key, as `Const.alterKey`), `none` removes the entry. One probe. -/
@[inline] def alter (t : Table α β) (a : α) (f : Option β → Option β) : Table α β :=
  let ⟨ctrl, keys, vals, size, gl, mask, shift, req⟩ := t
  if smallMask mask then
    let q := hashBits shift a
    let pos := homeU q mask
    let rep := repTag (tagOf q)
    let g := ctrlWord ctrl pos (by sorry)
    let r := findInsLoop ctrl keys a mask rep pos 0 g (matchTag g rep) (mask + 1)
    if r ≤ mask then
      let v := vals.uget r (by sorry)
      let vals := vals.uset r (vals.uget (mask + 1) (by sorry)) (by sorry)
      match f (some v) with
      | some v' =>
        ⟨ctrl, keys.uset r a (by sorry), vals.uset r v' (by sorry), size, gl, mask, shift, req⟩
      | none => eraseAtU ⟨ctrl, keys, vals, size, gl, mask, shift, req⟩ r
    else
      match f none with
      | some v' =>
        insertNewU ⟨ctrl, keys, vals, size, gl, mask, shift, req⟩ a v' q (r - (mask + 1))
      | none => ⟨ctrl, keys, vals, size, gl, mask, shift, req⟩
  else alterN ⟨ctrl, keys, vals, size, gl, mask, shift, req⟩ a f

/-- Apply `f` to the value of the stored key `== a`, if any, replacing that key by `a` (as
`Const.modifyKey`); the table itself when there is none. -/
@[inline] def modify (t : Table α β) (a : α) (f : β → β) : Table α β :=
  if smallShift t.shift then
    let i := findU t.ctrl t.slotKeys t.mask t.shift a
    if i ≤ t.mask then modifyAtU t i a f else t
  else modifyN t a f

/-- Keep the entries that satisfy `f`: the others are erased in place. -/
@[inline] def filter (f : α → β → Bool) (t : Table α β) : Table α β :=
  filterLoop f (t.ctrl.size - 8) 0 t

/-- Map the values through `f`, dropping the entries mapped to `none`: in place on the control
bytes and keys, into a new value array. -/
@[inline] def filterMap (f : α → β → Option γ) (t : Table α β) : Table α γ :=
  let ⟨ctrl, keys, vals, size, gl, mask, shift, req⟩ := t
  let cap := ctrl.size - 8
  match firstSome f ctrl keys vals cap 0 with
  | none => emptyWithCapacity req
  | some (i0, c0) =>
    let (ctrl, keys, size, gl, out) :=
      filterMapLoop f vals cap i0 c0 0 ctrl keys size gl (.emptyWithCapacity (cap + 1))
    ⟨ctrl, keys, vals.propagateMark out, size, gl, mask, shift, req⟩

/-- Map the values through `f`, in place: the value array is rewritten cell by cell (free cells
get the first mapped value). -/
@[inline] def map (f : α → β → γ) (t : Table α β) : Table α γ :=
  let ⟨ctrl, keys, vals, size, gl, mask, shift, req⟩ := t
  let cap := ctrl.size - 8
  match firstFull ctrl cap 0 with
  | none => emptyWithCapacity req
  | some i0 =>
    let c0 := f (keys[i0]'(by sorry)) (vals[i0]'(by sorry))
    let vals := vals.mapFinIdx fun i v _ =>
      if i < cap ∧ i ≠ i0 ∧ ctrl[i]'(by sorry) < 0x80 then f (keys[i]'(by sorry)) v else c0
    ⟨ctrl, keys, vals, size, gl, mask, shift, req⟩

/-- Monadic left fold over the entries, in slot order. -/
@[inline] def foldM {ε : Type w} {m : Type w → Type w'} [Monad m] (f : ε → α → β → m ε)
    (init : ε) (t : Table α β) : m ε :=
  if smallShift t.shift then
    let cap := t.ctrl.usize - 8
    if 0 < cap then
      foldMLoop f t.ctrl t.slotKeys t.slotVals cap 0 (matchFull (ctrlWord t.ctrl 0 (by sorry)))
        init
    else pure init
  else
    let cap := t.ctrl.size - 8
    foldMLoopN f t.ctrl t.slotKeys t.slotVals cap 0 (matchFull (ctrlWordN t.ctrl 0 (by sorry)))
      init

/-- Right fold over the entries: `f` sees them in reverse slot order. -/
@[inline] def foldRev {ε : Type w} (f : ε → α → β → ε) (init : ε) (t : Table α β) : ε :=
  if smallShift t.shift then
    foldRevLoop f t.ctrl t.slotKeys t.slotVals (t.ctrl.usize - 8) init
  else
    foldRevLoopN f t.ctrl t.slotKeys t.slotVals (t.ctrl.size - 8) init

/-- Monadic loop over the entries in slot order, with early exit. -/
@[inline] def forIn {ε : Type w} {m : Type w → Type w'} [Monad m]
    (f : α → β → ε → m (ForInStep ε)) (init : ε) (t : Table α β) : m ε :=
  if smallShift t.shift then
    let cap := t.ctrl.usize - 8
    if 0 < cap then
      forInLoop f t.ctrl t.slotKeys t.slotVals cap 0 (matchFull (ctrlWord t.ctrl 0 (by sorry)))
        init
    else pure init
  else
    let cap := t.ctrl.size - 8
    forInLoopN f t.ctrl t.slotKeys t.slotVals cap 0 (matchFull (ctrlWordN t.ctrl 0 (by sorry)))
      init

end Table

end OAMap.Core
