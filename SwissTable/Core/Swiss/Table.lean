module

public import SwissTable.Core.Swiss.Proofs.Write
public import SwissTable.Core.Swiss.Proofs.Bulk

/-!
# The Swiss core: the table and its operations (executable code, frozen)

The 23 definitions of the core contract (`docs/ARCHITECTURE.md` §3.2) on hashbrown's generic
(non-SIMD) layout, as chosen by the bake-off (`docs/bakeoff/decision.md`). This file and the code
files it builds on (`Defs.lean`, `Loops.lean`, `Build.lean`) are the code the verified core
compiles to. The code is frozen at the version the bake-off measured: the proofs only add erased
arguments, and a change to the code, even to those arguments, is checked against the frozen
version (its generated C, or instructions per operation on the bake-off harness).

## Proof structure

The code carries no `sorry`: every array bound and every termination measure is a lemma, and every
table it builds carries its invariant `Swiss.WF` (`Defs.lean`; the field `Table.wf`, erased at
runtime), also by a lemma. The lemmas are proved in eight proof files under
`SwissTable/Core/Swiss/Proofs/`, interleaved with the code files so that each proof needs only what
is stated before it (the code files are `Defs`, `Loops`, `Build` and this one):

    Group ── Defs ── Proofs/Bounds ── Loops ─┬─ Proofs/Probe ─────────────┐
                                              └─ Proofs/Rebuild ── Build ─┴─ Proofs/Write ──
        ── Proofs/Bulk ── Table ─┬─ Proofs/Query ── Proofs/Update   (contract lemmas 1–16)
                                  └─ Proofs/Traverse                 (contract lemmas 17–22)

* `Bounds`: the bounds and termination facts of the loops, what the operations read off the
  invariant (shape, the guards `smallMask ↔ smallShift`, the loops' erased hypotheses), the
  capacity arithmetic, the machine-word forms of the control-array operations, and the small
  facts the later files share (machine-word arithmetic, the entry of a slot);
* `Probe`: the probe lemmas (a lookup or insertion probe ends at a hit, or at a free slot that its
  key's probe reaches with the key absent), and the U facts of the fused operations (the
  insertion probe hits exactly where the lookup probe does);
* `Rebuild`: the empty table, `findFree`, and the move loops (a rebuild builds a well-formed table
  with the same entries, comparing no keys);
* `Write`: the invariant and the entries after each single-slot write (a new key, the key and
  value of a hit, an erasure by the tombstone rule, a value), and what `reserveInsert` needs of
  `reserveTable`;
* `Bulk`: `firstFull`, `firstSome` and `filterMap`'s in-place pass;
* `Query`, `Update`, `Traverse`: the 22 contract lemmas (`SwissTable/Core/Swiss.lean` collects them).

Each proof file's header describes its proof.

The contract definitions (namespace `Table`) are not exposed, as the contract requires (only
`markLinear` is); their bodies are the exposed `Swiss.*Impl` definitions below, and each has an
equation lemma `Table.*_def` here, so that the proof files can unfold them.

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

The empty map (`emptyWithCapacity c`, hence `∅`) allocates no array, only its table cell: its
`ctrl` is a shared group of 8 EMPTY bytes (`emptyGroup`), `mask = 0`, `shift = 57`, both arrays
`#[]`, and `reqCap = c`.
Every probe of it ends in its first group without reading a key, so the queries need no special
case. The first insert allocates `lgFor (max c 1)` and takes its own pair as the placeholder.

## Algorithms

* **Groups** (`SwissTable.Core.Swiss.Group`): the group word `ctrlWord`, the exact per-lane tag
  match `matchTag` (no false positives), `matchEmpty`, `matchFree`, `matchFull`, `lowestLane`,
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
on `Nat` indices on larger ones, from `2 ^ 32` slots (the `…N` loops, the same algorithms; also
executable): up to `2 ^ 31` slots no index computation wraps on any platform. Each operation tests
this once, at its top, with `smallShift` or `smallMask` (equivalent on every table). The bulk
operations `filter`, `filterMap` and `map` use `Nat` indices at every size.

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
* The proofs ride along as erased arguments (`Prop` hypotheses of the loops, `if h :` and
  `match h :` in place of `if` and `match`, the `wf` field): the generated code is the frozen
  version's (checked on the generated C and by instructions per op).

## Measured (the freeze reference)

`docs/bakeoff/freeze-results.csv` (summary `freeze-summary.txt`): std, SwissF and this core
(`final`) on rand, flat, string and struct keys at n = 1000, 98304, 10^6, 10^7, every workload,
Apple M5 Pro, harness `oabench2`. Against SwissF, the geometric mean of ns/op over the 16 cells of
each workload is within +2.8% (getopt) and down to 0.61 (fold, group at a time); the geometric
mean of instructions/op per workload ranges from −2% (insert, fold) to +4% (reinsert; the guard
and the exact tag match), with +9% on `get?` (getopt, getopt-shuf), and memory is identical. Later
changes made for the proofs are checked against these instructions/op.
-/

-- Elaborated `let`s stay `let`s instead of becoming `have`s, the setting of the SwissF prototype
-- and of the bake-off harness that measured the frozen code. Without it, the generated C of this
-- file differs from the frozen version's (the order of a join point's parameters in `eraseAtU`).
set_option cleanup.letToHave false

public section

universe u v w w'

namespace SwissTable.Core

namespace Swiss

variable {α : Type u} {β : Type v} {γ : Type w}

@[expose] section Impl

/-! ## Inserting into a table with room -/

/-- Insert the absent key `a ↦ b` into a table with room: at the first free slot of its probe. -/
@[specialize] def insertFresh [BEq α] [Hashable α] (t : Table α β) (a : α) (b : β)
    (h : FreshPre t.slots t.growthLeft a) : Table α β :=
  let ⟨ctrl, keys, vals, size, gl, mask, shift, req, wf⟩ := t
  let q := hashBits shift a
  if hs : smallMask mask then
    let i := findFree ctrl mask (homeU q mask) 0 (wf.loopU' hs).arr (and_mask_le _ _) stride_zero
    let old := ctrl.uget i (wf.fresh_ctrl hs h)
    ⟨setCtrl ctrl mask i (tagOf q) (wf.fresh_ctrl hs h) (wf.mirror_lt (wf.cap_pos_of_gl h.room)),
      keys.uset i a (wf.fresh_keys hs h), vals.uset i b (wf.fresh_vals hs h), size + 1,
      if old == EMPTY then gl - 1 else gl, mask, shift, req, wf.freshU hs h rfl⟩
  else
    let cap := ctrl.size - 8
    let i := findFreeN ctrl cap (homeN q cap) 0 (wf.ctrlN' hs) (Nat.mod_lt _ (wf.ctrlN' hs).pos)
    let old := ctrl[i]'(wf.freshN_ctrl hs h)
    ⟨setCtrlN ctrl cap i (tagOf q) (wf.freshN_ctrl hs h) (wf.ctrlN' hs).word (wf.ctrlN' hs).pos,
      keys.set i a (wf.freshN_keys hs h), vals.set i b (wf.freshN_vals hs h), size + 1,
      if old == EMPTY then gl - 1 else gl, mask, shift, req, wf.freshN hs h rfl⟩

/-- Insert the absent key `a ↦ b` when no EMPTY slot may be filled: allocate the unallocated
table, or rebuild at the same capacity (when `size + 1 ≤ capacity / 2`) or at twice it, then
insert (`reserveTable`). -/
@[specialize] def reserveInsert [BEq α] [Hashable α] (t : Table α β) (a : α) (b : β)
    (h : ∀ [EquivBEq α] [LawfulHashable α], t.slots.Absent a) : Table α β :=
  insertFresh (reserveTable t a b) a b (freshPre_reserve t a b h)

/-! ## Writes on machine words -/

/-- Write the new key `a ↦ b` (hash bits `q`) at the free slot `i` of its probe, after a rebuild
when `i` is EMPTY and `growthLeft = 0`. -/
@[inline] def insertNewU [BEq α] [Hashable α] (t : Table α β) (a : α) (b : β) (q : UInt64)
    (i : USize) (hs : smallMask t.mask = true) (h : NewSlot t.slots t.shift a q i.toNat) :
    Table α β :=
  let ⟨ctrl, keys, vals, size, gl, mask, shift, req, wf⟩ := t
  let old := ctrl.uget i (wf.new_ctrl h)
  if hold : old == EMPTY then
    if hgl : gl == 0 then
      reserveInsert ⟨ctrl, keys, vals, size, gl, mask, shift, req, wf⟩ a b h.absent
    else
      ⟨setCtrl ctrl mask i (tagOf q) (wf.new_ctrl h) (wf.mirror_lt (wf.new_alloc_gl h hgl)),
        keys.uset i a (wf.new_keys h (wf.new_alloc_gl h hgl)),
        vals.uset i b (wf.new_vals h (wf.new_alloc_gl h hgl)), size + 1, gl - 1, mask, shift, req,
        wf.newU_empty hs h hold hgl⟩
  else
    ⟨setCtrl ctrl mask i (tagOf q) (wf.new_ctrl h) (wf.mirror_lt (wf.new_alloc_old h hold)),
      keys.uset i a (wf.new_keys h (wf.new_alloc_old h hold)),
      vals.uset i b (wf.new_vals h (wf.new_alloc_old h hold)), size + 1, gl, mask, shift, req,
      wf.newU_del hs h hold⟩

/-- Erase the full slot `i`: EMPTY when every 8-window around it has another EMPTY slot (and
`growthLeft + 1`), else DELETED (and, past `capacity / 4` tombstones, `growthLeft := 0`); the key
and value cells get the placeholders back. -/
@[specialize] def eraseAtU [BEq α] [Hashable α] (t : Table α β) (i : USize)
    (hs : smallMask t.mask = true) (hi : t.slots.IsFull i.toNat) : Table α β :=
  let ⟨ctrl, keys, vals, size, gl, mask, shift, req, wf⟩ := t
  let ea := matchEmpty (ctrlWord ctrl i (wf.full_word hi))
  let eb := matchEmpty (ctrlWord ctrl ((i - 8) &&& mask) (and_mask_word (wf.loopU' hs).arr.word))
  let del := needsTombstone ea eb
  let ctrl := setCtrl ctrl mask i (if del then DELETED else EMPTY) (wf.full_ctrl hi)
    (wf.mirror_lt hi.cap_pos)
  let p := mask + 1
  let k0 := keys.uget p (wf.place_keys hs hi.cap_pos)
  let v0 := vals.uget p (wf.place_vals hs hi.cap_pos)
  let full := ((mask + 1) >>> 3) * 7
  let gl := if del then
      (if (size - 1).toUSize + gl.toUSize + (full >>> 2) < full then 0 else gl)
    else gl + 1
  ⟨ctrl, keys.uset i k0 (wf.keys_lt hi.1), vals.uset i v0 (wf.vals_lt hi.1), size - 1, gl, mask,
    shift, req, wf.eraseU hs hi rfl rfl⟩

/-- Replace the key of the full slot `i` by `a` and its value `v` by `f v` (taken out of its cell
first, so that `f` sees it unshared). -/
@[inline] def modifyAtU [BEq α] [Hashable α] (t : Table α β) (i : USize) (a : α) (f : β → β)
    (hs : smallMask t.mask = true) (hi : t.slots.Hit t.shift a i.toNat) : Table α β :=
  let ⟨ctrl, keys, vals, size, gl, mask, shift, req, wf⟩ := t
  let v := vals.uget i (wf.vals_lt hi.1.1)
  let vals := vals.uset i (vals.uget (mask + 1) (wf.place_vals hs hi.1.cap_pos))
    (wf.vals_lt hi.1.1)
  ⟨ctrl, keys.uset i a (wf.keys_lt hi.1.1), vals.uset i (f v) (lt_size_uset (wf.vals_lt hi.1.1)),
    size, gl, mask, shift, req,
    WF.replaceVals (wf.keyU hi) ((Array.size_uset _).trans (Array.size_uset _))⟩

/-! ## Writes on `Nat` indices -/

/-- `insertNewU` on `Nat` indices. -/
@[specialize] def insertNewN [BEq α] [Hashable α] (t : Table α β) (a : α) (b : β) (q : UInt64)
    (i : Nat) (h : NewSlot t.slots t.shift a q i) : Table α β :=
  let ⟨ctrl, keys, vals, size, gl, mask, shift, req, wf⟩ := t
  let cap := ctrl.size - 8
  let old := ctrl[i]'(wf.new_ctrl h)
  if hold : old == EMPTY then
    if hgl : gl == 0 then
      reserveInsert ⟨ctrl, keys, vals, size, gl, mask, shift, req, wf⟩ a b h.absent
    else
      ⟨setCtrlN ctrl cap i (tagOf q) (wf.new_ctrl h) wf.cap_word (wf.new_alloc_gl h hgl),
        keys.set i a (wf.new_keys h (wf.new_alloc_gl h hgl)),
        vals.set i b (wf.new_vals h (wf.new_alloc_gl h hgl)), size + 1, gl - 1, mask, shift, req,
        wf.newN_empty h hold hgl⟩
  else
    ⟨setCtrlN ctrl cap i (tagOf q) (wf.new_ctrl h) wf.cap_word (wf.new_alloc_oldN h hold),
      keys.set i a (wf.new_keys h (wf.new_alloc_oldN h hold)),
      vals.set i b (wf.new_vals h (wf.new_alloc_oldN h hold)), size + 1, gl, mask, shift, req,
      wf.newN_del h hold⟩

/-- `eraseAtU` on `Nat` indices. -/
@[specialize] def eraseAtN [BEq α] [Hashable α] (t : Table α β) (i : Nat)
    (hi : t.slots.IsFull i) : Table α β :=
  let ⟨ctrl, keys, vals, size, gl, mask, shift, req, wf⟩ := t
  let cap := ctrl.size - 8
  match he : eraseCtrlN ctrl size gl cap i hi.1 wf.cap_word with
  | (ctrl, gl) =>
    let k0 := keys[cap]'(wf.place_keysN hi.cap_pos)
    let v0 := vals[cap]'(wf.place_valsN hi.cap_pos)
    ⟨ctrl, keys.set i k0 (wf.keys_lt hi.1), vals.set i v0 (wf.vals_lt hi.1), size - 1, gl, mask,
      shift, req, wf.eraseN hi he⟩

/-- `eraseAtN` keeps the size of the control array. -/
theorem ctrl_size_eraseAtN [BEq α] [Hashable α] (t : Table α β) (i : Nat)
    (hi : t.slots.IsFull i) : (eraseAtN t i hi).ctrl.size = t.ctrl.size := by
  cases t
  simp only [eraseAtN, eraseCtrlN, size_setCtrlN]

/-- `modifyAtU` on `Nat` indices. -/
@[inline] def modifyAtN [BEq α] [Hashable α] (t : Table α β) (i : Nat) (a : α) (f : β → β)
    (hi : t.slots.Hit t.shift a i) : Table α β :=
  let ⟨ctrl, keys, vals, size, gl, mask, shift, req, wf⟩ := t
  let cap := ctrl.size - 8
  let v := vals[i]'(wf.vals_lt hi.1.1)
  let vals := vals.set i (vals[cap]'(wf.place_valsN hi.1.cap_pos)) (wf.vals_lt hi.1.1)
  ⟨ctrl, keys.set i a (wf.keys_lt hi.1.1), vals.set i (f v) (lt_size_set (wf.vals_lt hi.1.1)),
    size, gl, mask, shift, req,
    WF.replaceVals (wf.keyN hi) ((Array.size_set _).trans (Array.size_set _))⟩

/-! ## Operations on `Nat` indices (out of line) -/

/-- `Table.erase` on `Nat` indices. -/
@[specialize] def eraseN [BEq α] [Hashable α] (t : Table α β) (a : α)
    (hs : ¬smallShift t.shift = true) : Table α β :=
  match he : findN t.ctrl t.slotKeys (t.ctrl.size - 8) t.shift a (t.wf.arrN hs) with
  | some i => eraseAtN t i (t.wf.findN_hit (t.wf.arrN hs) he).1
  | none => t

/-- `Table.modify` on `Nat` indices. -/
@[specialize] def modifyN [BEq α] [Hashable α] (t : Table α β) (a : α) (f : β → β)
    (hs : ¬smallShift t.shift = true) : Table α β :=
  match he : findN t.ctrl t.slotKeys (t.ctrl.size - 8) t.shift a (t.wf.arrN hs) with
  | some i => modifyAtN t i a f (t.wf.findN_hit (t.wf.arrN hs) he)
  | none => t

/-- `Table.containsThenInsert` on `Nat` indices. -/
@[specialize] def containsThenInsertN [BEq α] [Hashable α] (t : Table α β) (a : α) (b : β)
    (hs : ¬smallMask t.mask = true) : Bool × Table α β :=
  let ⟨ctrl, keys, vals, size, gl, mask, shift, req, wf⟩ := t
  let q := hashBits shift a
  match he : insSlotN ctrl keys a (ctrl.size - 8) q (wf.arrN' hs) with
  | .inl i =>
    (true, ⟨ctrl, keys.set i a (wf.keys_lt (wf.insSlotN_hit (wf.arrN' hs) he).1.1),
      vals.set i b (wf.vals_lt (wf.insSlotN_hit (wf.arrN' hs) he).1.1), size, gl, mask, shift, req,
      WF.replaceVals (wf.keyN (wf.insSlotN_hit (wf.arrN' hs) he)) (Array.size_set _)⟩)
  | .inr j =>
    (false, insertNewN ⟨ctrl, keys, vals, size, gl, mask, shift, req, wf⟩ a b q j
      (wf.insSlotN_new (wf.arrN' hs) he))

/-- `Table.getThenInsertIfNew?` on `Nat` indices. -/
@[specialize] def getThenInsertIfNewN [BEq α] [Hashable α] (t : Table α β) (a : α) (b : β)
    (hs : ¬smallShift t.shift = true) : Option β × Table α β :=
  let ⟨ctrl, keys, vals, size, gl, mask, shift, req, wf⟩ := t
  let cap := ctrl.size - 8
  let q := hashBits shift a
  let pos := homeN q cap
  let rep := repTag (tagOf q)
  let g := ctrlWordN ctrl pos ((wf.arrN hs).mod_word _)
  match he : findInsLoopN ctrl keys a cap rep pos 0 g (matchTag g rep) cap (wf.arrN hs)
      (isMask_matchTag g rep) with
  | .inl i =>
    (some (vals[i]'(wf.vals_lt (wf.insProbeN_hit (wf.arrN hs) he).1.1)),
      ⟨ctrl, keys, vals, size, gl, mask, shift, req, wf⟩)
  | .inr j =>
    (none, insertNewN ⟨ctrl, keys, vals, size, gl, mask, shift, req, wf⟩ a b q j
      (wf.insProbeN_new (wf.arrN hs) he))

/-- `Table.alter` on `Nat` indices. -/
@[specialize] def alterN [BEq α] [Hashable α] (t : Table α β) (a : α)
    (f : Option β → Option β) (hs : ¬smallMask t.mask = true) : Table α β :=
  let ⟨ctrl, keys, vals, size, gl, mask, shift, req, wf⟩ := t
  let cap := ctrl.size - 8
  let q := hashBits shift a
  let pos := homeN q cap
  let rep := repTag (tagOf q)
  let g := ctrlWordN ctrl pos ((wf.arrN' hs).mod_word _)
  match he : findInsLoopN ctrl keys a cap rep pos 0 g (matchTag g rep) cap (wf.arrN' hs)
      (isMask_matchTag g rep) with
  | .inl i =>
    let v := vals[i]'(wf.vals_lt (wf.insProbeN_hit (wf.arrN' hs) he).1.1)
    let vals := vals.set i
      (vals[cap]'(wf.place_valsN (wf.insProbeN_hit (wf.arrN' hs) he).1.cap_pos))
      (wf.vals_lt (wf.insProbeN_hit (wf.arrN' hs) he).1.1)
    match f (some v) with
    | some v' =>
      ⟨ctrl, keys.set i a (wf.keys_lt (wf.insProbeN_hit (wf.arrN' hs) he).1.1),
        vals.set i v' (lt_size_set (wf.vals_lt (wf.insProbeN_hit (wf.arrN' hs) he).1.1)), size,
        gl, mask, shift, req,
        WF.replaceVals (wf.keyN (wf.insProbeN_hit (wf.arrN' hs) he))
          ((Array.size_set _).trans (Array.size_set _))⟩
    | none =>
      eraseAtN
        ⟨ctrl, keys, vals, size, gl, mask, shift, req, WF.replaceVals wf (Array.size_set _)⟩ i
        (wf.insProbeN_hit (wf.arrN' hs) he).1
  | .inr j =>
    match f none with
    | some v' =>
      insertNewN ⟨ctrl, keys, vals, size, gl, mask, shift, req, wf⟩ a v' q j
        (wf.insProbeN_new (wf.arrN' hs) he)
    | none => ⟨ctrl, keys, vals, size, gl, mask, shift, req, wf⟩

/-! ## Bulk operations (on `Nat` indices) -/

/-- Erase, in slot order from slot `i` on, every entry that `f` rejects. -/
@[specialize] def filterLoop [BEq α] [Hashable α] (f : α → β → Bool) (cap i : Nat)
    (t : Table α β) (hc : cap = t.ctrl.size - 8) : Table α β :=
  if h : i < cap then
    if hf : t.ctrl[i]'(lt_ctrl_of_cap h hc) < 0x80 then
      if f (t.slotKeys[i]'(t.wf.keys_lt (Nat.lt_of_lt_of_eq h hc)))
          (t.slotVals[i]'(t.wf.vals_lt (Nat.lt_of_lt_of_eq h hc))) then
        filterLoop f cap (i + 1) t hc
      else
        filterLoop f cap (i + 1) (eraseAtN t i (isFull_of (Nat.lt_of_lt_of_eq h hc) hf))
          (hc.trans (congrArg (· - 8) (ctrl_size_eraseAtN t i _).symm))
    else filterLoop f cap (i + 1) t hc
  else t
termination_by cap - i

/-! ## The operations of the contract -/

/-- The unallocated table (`Table.emptyWithCapacity`). -/
def emptyImpl [BEq α] [Hashable α] (capacity : Nat) : Table α β :=
  ⟨emptyGroup, #[], #[], 0, 0, 0, 57, capacity, WF.unalloc⟩

/-- One probe for `a` (`Table.lookup`). -/
@[inline] def lookupImpl [BEq α] [Hashable α] {σ : Type w} (t : Table α β) (a : α)
    (found : α → β → σ) (missing : Unit → σ) : σ :=
  if hs : smallShift t.shift then
    let i := findU t.ctrl t.slotKeys t.mask t.shift a (t.wf.loopU hs)
    if hi : i ≤ t.mask then
      found (t.slotKeys.uget i (t.wf.keys_lt (t.wf.findU_hit (t.wf.loopU hs) hi).1.1))
        (t.slotVals.uget i (t.wf.vals_lt (t.wf.findU_hit (t.wf.loopU hs) hi).1.1))
    else missing ()
  else
    match he : findN t.ctrl t.slotKeys (t.ctrl.size - 8) t.shift a (t.wf.arrN hs) with
    | some i =>
      found (t.slotKeys[i]'(t.wf.keys_lt (t.wf.findN_hit (t.wf.arrN hs) he).1.1))
        (t.slotVals[i]'(t.wf.vals_lt (t.wf.findN_hit (t.wf.arrN hs) he).1.1))
    | none => missing ()

/-- Whether a stored key is `==` to `a` (`Table.contains`). -/
@[inline] def containsImpl [BEq α] [Hashable α] (t : Table α β) (a : α) : Bool :=
  lookupImpl t a (fun _ _ => true) (fun _ => false)

/-- `lookupMemImpl` on `Nat` indices (tables beyond `2 ^ 31` slots). -/
@[specialize] def lookupMemN [BEq α] [Hashable α] {σ : Type w} (t : Table α β) (a : α)
    (hm : ¬smallShift t.shift = true) (h : containsImpl t a = true) (found : α → β → σ) : σ :=
  match he : findN t.ctrl t.slotKeys (t.ctrl.size - 8) t.shift a (t.wf.arrN hm) with
  | some i =>
    found (t.slotKeys[i]'(t.wf.keys_lt (t.wf.findN_hit (t.wf.arrN hm) he).1.1))
      (t.slotVals[i]'(t.wf.vals_lt (t.wf.findN_hit (t.wf.arrN hm) he).1.1))
  | none => absurd h (by unfold containsImpl lookupImpl; rw [dite_eq_right hm]; split <;> simp_all)

/-- One probe for a key known to be present (`Table.lookupMem`). -/
@[inline] def lookupMemImpl [BEq α] [Hashable α] {σ : Type w} (t : Table α β) (a : α)
    (h : containsImpl t a = true) (found : α → β → σ) : σ :=
  if hm : smallShift t.shift then
    let i := findU t.ctrl t.slotKeys t.mask t.shift a (t.wf.loopU hm)
    if hi : i ≤ t.mask then
      found (t.slotKeys.uget i (t.wf.keys_lt (t.wf.findU_hit (t.wf.loopU hm) hi).1.1))
        (t.slotVals.uget i (t.wf.vals_lt (t.wf.findU_hit (t.wf.loopU hm) hi).1.1))
    else absurd h (by simp [containsImpl, lookupImpl, hm, i, hi])
  else lookupMemN t a hm h found

/-- `Table.containsThenInsert`: one probe, with fast path C. -/
@[inline] def containsThenInsertImpl [BEq α] [Hashable α] (t : Table α β) (a : α) (b : β) :
    Bool × Table α β :=
  let ⟨ctrl, keys, vals, size, gl, mask, shift, req, wf⟩ := t
  if hsm : smallMask mask then
    let q := hashBits shift a
    let pos := homeU q mask
    let rep := repTag (tagOf q)
    let g := ctrlWord ctrl pos (and_mask_word (wf.loopU' hsm).arr.word)
    let mt := matchTag g rep
    -- Fast path C: the home byte is EMPTY and no lane of the home group carries the tag, so the
    -- key is new and goes to the home slot (an address known before the group load returns).
    if hmt : mt == 0 then
      if hg : g &&& 0xFF == 0xFF then
        (false, insertNewU ⟨ctrl, keys, vals, size, gl, mask, shift, req, wf⟩ a b q pos hsm
          (wf.fast_new (wf.loopU' hsm) hmt hg))
      else
        let r := findInsLoop ctrl keys a mask rep pos 0 g mt (mask + 1) (wf.loopU' hsm).arr
          stride_zero (isMask_matchTag g rep) (firstGroup (wf.loopU' hsm) q)
        if hr : r ≤ mask then
          (true, ⟨ctrl, keys.uset r a (wf.keys_lt (wf.insProbeU_hit (wf.loopU' hsm) hr).1.1),
            vals.uset r b (wf.vals_lt (wf.insProbeU_hit (wf.loopU' hsm) hr).1.1), size, gl, mask,
            shift, req,
            WF.replaceVals (wf.keyU (wf.insProbeU_hit (wf.loopU' hsm) hr)) (Array.size_uset _)⟩)
        else
          (false, insertNewU ⟨ctrl, keys, vals, size, gl, mask, shift, req, wf⟩ a b q
            (r - (mask + 1)) hsm (wf.insProbeU_new (wf.loopU' hsm) hr))
    else
      let r := findInsLoop ctrl keys a mask rep pos 0 g mt (mask + 1) (wf.loopU' hsm).arr
        stride_zero (isMask_matchTag g rep) (firstGroup (wf.loopU' hsm) q)
      if hr : r ≤ mask then
        (true, ⟨ctrl, keys.uset r a (wf.keys_lt (wf.insProbeU_hit (wf.loopU' hsm) hr).1.1),
          vals.uset r b (wf.vals_lt (wf.insProbeU_hit (wf.loopU' hsm) hr).1.1), size, gl, mask,
          shift, req,
          WF.replaceVals (wf.keyU (wf.insProbeU_hit (wf.loopU' hsm) hr)) (Array.size_uset _)⟩)
      else
        (false, insertNewU ⟨ctrl, keys, vals, size, gl, mask, shift, req, wf⟩ a b q
          (r - (mask + 1)) hsm (wf.insProbeU_new (wf.loopU' hsm) hr))
  else containsThenInsertN ⟨ctrl, keys, vals, size, gl, mask, shift, req, wf⟩ a b hsm

/-- `Table.getThenInsertIfNew?`: one probe, no fast path. -/
@[inline] def getThenInsertIfNewImpl [BEq α] [Hashable α] (t : Table α β) (a : α) (b : β) :
    Option β × Table α β :=
  let ⟨ctrl, keys, vals, size, gl, mask, shift, req, wf⟩ := t
  if hss : smallShift shift then
    let q := hashBits shift a
    let pos := homeU q mask
    let rep := repTag (tagOf q)
    let g := ctrlWord ctrl pos (and_mask_word (wf.loopU hss).arr.word)
    let r := findInsLoop ctrl keys a mask rep pos 0 g (matchTag g rep) (mask + 1)
      (wf.loopU hss).arr stride_zero (isMask_matchTag g rep) (firstGroup (wf.loopU hss) q)
    if hr : r ≤ mask then
      (some (vals.uget r (wf.vals_lt (wf.insProbeU_hit (wf.loopU hss) hr).1.1)),
        ⟨ctrl, keys, vals, size, gl, mask, shift, req, wf⟩)
    else
      (none, insertNewU ⟨ctrl, keys, vals, size, gl, mask, shift, req, wf⟩ a b q (r - (mask + 1))
        (wf.smallMask_of_smallShift hss) (wf.insProbeU_new (wf.loopU hss) hr))
  else getThenInsertIfNewN ⟨ctrl, keys, vals, size, gl, mask, shift, req, wf⟩ a b hss

/-- `Table.erase`: the table itself when there is no key `== a`. -/
@[inline] def eraseImpl [BEq α] [Hashable α] (t : Table α β) (a : α) : Table α β :=
  if hs : smallShift t.shift then
    let i := findU t.ctrl t.slotKeys t.mask t.shift a (t.wf.loopU hs)
    if hi : i ≤ t.mask then
      eraseAtU t i (t.wf.smallMask_of_smallShift hs) (t.wf.findU_hit (t.wf.loopU hs) hi).1
    else t
  else eraseN t a hs

/-- `Table.alter`: one probe. -/
@[inline] def alterImpl [BEq α] [Hashable α] (t : Table α β) (a : α)
    (f : Option β → Option β) : Table α β :=
  let ⟨ctrl, keys, vals, size, gl, mask, shift, req, wf⟩ := t
  if hsm : smallMask mask then
    let q := hashBits shift a
    let pos := homeU q mask
    let rep := repTag (tagOf q)
    let g := ctrlWord ctrl pos (and_mask_word (wf.loopU' hsm).arr.word)
    let r := findInsLoop ctrl keys a mask rep pos 0 g (matchTag g rep) (mask + 1)
      (wf.loopU' hsm).arr stride_zero (isMask_matchTag g rep) (firstGroup (wf.loopU' hsm) q)
    if hr : r ≤ mask then
      let v := vals.uget r (wf.vals_lt (wf.insProbeU_hit (wf.loopU' hsm) hr).1.1)
      let vals := vals.uset r
        (vals.uget (mask + 1) (wf.place_vals hsm (wf.insProbeU_hit (wf.loopU' hsm) hr).1.cap_pos))
        (wf.vals_lt (wf.insProbeU_hit (wf.loopU' hsm) hr).1.1)
      match f (some v) with
      | some v' =>
        ⟨ctrl, keys.uset r a (wf.keys_lt (wf.insProbeU_hit (wf.loopU' hsm) hr).1.1),
          vals.uset r v' (lt_size_uset (wf.vals_lt (wf.insProbeU_hit (wf.loopU' hsm) hr).1.1)),
          size, gl, mask, shift, req,
          WF.replaceVals (wf.keyU (wf.insProbeU_hit (wf.loopU' hsm) hr))
            ((Array.size_uset _).trans (Array.size_uset _))⟩
      | none =>
        eraseAtU
          ⟨ctrl, keys, vals, size, gl, mask, shift, req, WF.replaceVals wf (Array.size_uset _)⟩ r
          hsm (wf.insProbeU_hit (wf.loopU' hsm) hr).1
    else
      match f none with
      | some v' =>
        insertNewU ⟨ctrl, keys, vals, size, gl, mask, shift, req, wf⟩ a v' q (r - (mask + 1)) hsm
          (wf.insProbeU_new (wf.loopU' hsm) hr)
      | none => ⟨ctrl, keys, vals, size, gl, mask, shift, req, wf⟩
  else alterN ⟨ctrl, keys, vals, size, gl, mask, shift, req, wf⟩ a f hsm

/-- `Table.modify`: the table itself when there is no key `== a`. -/
@[inline] def modifyImpl [BEq α] [Hashable α] (t : Table α β) (a : α) (f : β → β) :
    Table α β :=
  if hs : smallShift t.shift then
    let i := findU t.ctrl t.slotKeys t.mask t.shift a (t.wf.loopU hs)
    if hi : i ≤ t.mask then
      modifyAtU t i a f (t.wf.smallMask_of_smallShift hs) (t.wf.findU_hit (t.wf.loopU hs) hi)
    else t
  else modifyN t a f hs

/-- `Table.filter`: the rejected entries erased in place. -/
@[inline] def filterImpl [BEq α] [Hashable α] (f : α → β → Bool) (t : Table α β) : Table α β :=
  filterLoop f (t.ctrl.size - 8) 0 t rfl

/-- `Table.filterMap`: in place on the control bytes and keys, into a new value array. -/
@[inline] def filterMapImpl [BEq α] [Hashable α] (f : α → β → Option γ) (t : Table α β) :
    Table α γ :=
  let ⟨ctrl, keys, vals, size, gl, mask, shift, req, wf⟩ := t
  let cap := ctrl.size - 8
  match hs : firstSome f ctrl keys vals cap 0 wf.foldN with
  | none => emptyImpl req
  | some (i0, c0) =>
    match hl : filterMapLoop f vals cap i0 c0 0 ctrl keys size gl (.emptyWithCapacity (cap + 1))
        (wf.fmArr hs) with
    | (ctrl, keys, size, gl, out) =>
      ⟨ctrl, keys, vals.propagateMark out, size, gl, mask, shift, req, wf.filterMap hs hl⟩

/-- `Table.map`: the value array rewritten in place (free cells get the first mapped value). -/
@[inline] def mapImpl [BEq α] [Hashable α] (f : α → β → γ) (t : Table α β) : Table α γ :=
  let ⟨ctrl, keys, vals, size, gl, mask, shift, req, wf⟩ := t
  let cap := ctrl.size - 8
  match hs : firstFull ctrl cap 0 wf.cap_le_ctrl with
  | none => emptyImpl req
  | some i0 =>
    let c0 := f (keys[i0]'(wf.keys_lt (firstFull_lt hs))) (vals[i0]'(wf.vals_lt (firstFull_lt hs)))
    let vals := vals.mapFinIdx fun i v hi =>
      if i < cap ∧ i ≠ i0 ∧ ctrl[i]'(wf.ctrl_of_vals hi) < 0x80 then
        f (keys[i]'(wf.keys_of_vals hi)) v
      else c0
    ⟨ctrl, keys, vals, size, gl, mask, shift, req, WF.replaceVals wf Array.size_mapFinIdx⟩

/-- `Table.foldM`: a group at a time, in slot order. -/
@[inline] def foldMImpl [BEq α] [Hashable α] {ε : Type w} {m : Type w → Type w'} [Monad m]
    (f : ε → α → β → m ε) (init : ε) (t : Table α β) : m ε :=
  if hs : smallShift t.shift then
    let cap := t.ctrl.usize - 8
    if hc : 0 < cap then
      foldMLoop f t.ctrl t.slotKeys t.slotVals cap 0 (matchFull (ctrlWord t.ctrl 0 t.wf.word0))
        init (t.wf.foldU hs) (t.wf.group0 hs hc) (isMask_matchFull _)
    else pure init
  else
    let cap := t.ctrl.size - 8
    foldMLoopN f t.ctrl t.slotKeys t.slotVals cap 0 (matchFull (ctrlWordN t.ctrl 0 t.wf.word0N))
      init t.wf.foldN (t.wf.group0N hs) (isMask_matchFull _)

/-- `Table.foldRev`: a group at a time, in reverse slot order. -/
@[inline] def foldRevImpl [BEq α] [Hashable α] {ε : Type w} (f : ε → α → β → ε) (init : ε)
    (t : Table α β) : ε :=
  if hs : smallShift t.shift then
    foldRevLoop f t.ctrl t.slotKeys t.slotVals (t.ctrl.usize - 8) init (t.wf.revU hs)
  else
    foldRevLoopN f t.ctrl t.slotKeys t.slotVals (t.ctrl.size - 8) init t.wf.revN

/-- `Table.forIn`: a group at a time, in slot order, with early exit. -/
@[inline] def forInImpl [BEq α] [Hashable α] {ε : Type w} {m : Type w → Type w'} [Monad m]
    (f : α → β → ε → m (ForInStep ε)) (init : ε) (t : Table α β) : m ε :=
  if hs : smallShift t.shift then
    let cap := t.ctrl.usize - 8
    if hc : 0 < cap then
      forInLoop f t.ctrl t.slotKeys t.slotVals cap 0 (matchFull (ctrlWord t.ctrl 0 t.wf.word0))
        init (t.wf.foldU hs) (t.wf.group0 hs hc) (isMask_matchFull _)
    else pure init
  else
    let cap := t.ctrl.size - 8
    forInLoopN f t.ctrl t.slotKeys t.slotVals cap 0 (matchFull (ctrlWordN t.ctrl 0 t.wf.word0N))
      init t.wf.foldN (t.wf.group0N hs) (isMask_matchFull _)

end Impl

end Swiss

namespace Table

open Swiss

variable {α : Type u} {β : Type v} {γ : Type w} [BEq α] [Hashable α]

/-! ## The 23 primitive definitions -/

/-- The entries of the table: its full slots in slot order. -/
def toListModel (t : Table α β) : List ((_ : α) × β) := t.slots.entries

/-- The empty table, with room for `capacity` entries once the first insert allocates it: it
allocates no array (a shared group of 8 EMPTY control bytes, no slots). -/
def emptyWithCapacity (capacity : Nat) : Table α β := emptyImpl capacity

/-- The number of slots, counting for the unallocated table the slots its first insert allocates
(so it is positive, as Std's bucket count is). -/
def numBuckets (t : Table α β) : Nat :=
  if t.slotKeys.size == 0 then 2 ^ lgFor (max t.reqCap 1) else t.ctrl.size - 8

/-- The identity; at runtime it makes the three arrays unique and marks them linear, as Std's
`Raw.markLinear` does for its bucket array. -/
@[expose] def markLinear (t : Table α β) : Table α β :=
  ⟨t.ctrl.markLinear, t.slotKeys.markLinear, t.slotVals.markLinear, t.size, t.growthLeft, t.mask,
    t.shift, t.reqCap, t.wf⟩

/-- One probe for `a`: `found k v` on the stored key `k == a` and its value, `missing ()` when
there is none. -/
@[inline] def lookup {σ : Type w} (t : Table α β) (a : α) (found : α → β → σ)
    (missing : Unit → σ) : σ :=
  lookupImpl t a found missing

/-- Whether a stored key is `==` to `a`. -/
@[inline] def contains (t : Table α β) (a : α) : Bool :=
  t.lookup a (fun _ _ => true) (fun _ => false)

/-- One probe for a key known to be present: `found k v` on the stored key and its value. -/
@[inline] def lookupMem {σ : Type w} (t : Table α β) (a : α) (h : t.contains a = true)
    (found : α → β → σ) : σ :=
  lookupMemImpl t a h found

/-- Insert `a ↦ b`, also returning whether a key `== a` was present; that key is replaced by `a`
and its value by `b`. One probe. -/
@[inline] def containsThenInsert (t : Table α β) (a : α) (b : β) : Bool × Table α β :=
  containsThenInsertImpl t a b

/-- Insert `a ↦ b`, replacing the stored key `== a` (by `a`) and its value if present. -/
@[inline] def insert (t : Table α β) (a : α) (b : β) : Table α β :=
  (t.containsThenInsert a b).2

/-- The value of the stored key `== a` if there is one (the table unchanged), else `none` and the
table with `a ↦ b` inserted. One probe. -/
@[inline] def getThenInsertIfNew? (t : Table α β) (a : α) (b : β) : Option β × Table α β :=
  getThenInsertIfNewImpl t a b

/-- Insert `a ↦ b` unless a key `== a` is stored. -/
@[inline] def insertIfNew (t : Table α β) (a : α) (b : β) : Table α β :=
  (t.getThenInsertIfNew? a b).2

/-- `insertIfNew`, also returning whether a key `== a` was present. One probe. -/
@[inline] def containsThenInsertIfNew (t : Table α β) (a : α) (b : β) : Bool × Table α β :=
  let r := t.getThenInsertIfNew? a b
  (r.1.isSome, r.2)

/-- Remove the entry of the stored key `== a`; the table itself when there is none. -/
@[inline] def erase (t : Table α β) (a : α) : Table α β :=
  eraseImpl t a

/-- Replace the value `v?` of `a` (`none` when absent) by `f v?`: `some` stores it under the key
`a` (replacing the stored key, as `Const.alterKey`), `none` removes the entry. One probe. -/
@[inline] def alter (t : Table α β) (a : α) (f : Option β → Option β) : Table α β :=
  alterImpl t a f

/-- Apply `f` to the value of the stored key `== a`, if any, replacing that key by `a` (as
`Const.modifyKey`); the table itself when there is none. -/
@[inline] def modify (t : Table α β) (a : α) (f : β → β) : Table α β :=
  modifyImpl t a f

/-- Keep the entries that satisfy `f`: the others are erased in place. -/
@[inline] def filter (f : α → β → Bool) (t : Table α β) : Table α β :=
  filterImpl f t

/-- Map the values through `f`, dropping the entries mapped to `none`: in place on the control
bytes and keys, into a new value array. -/
@[inline] def filterMap (f : α → β → Option γ) (t : Table α β) : Table α γ :=
  filterMapImpl f t

/-- Map the values through `f`, in place: the value array is rewritten cell by cell (free cells
get the first mapped value). -/
@[inline] def map (f : α → β → γ) (t : Table α β) : Table α γ :=
  mapImpl f t

/-- Monadic left fold over the entries, in slot order. -/
@[inline] def foldM {ε : Type w} {m : Type w → Type w'} [Monad m] (f : ε → α → β → m ε)
    (init : ε) (t : Table α β) : m ε :=
  foldMImpl f init t

/-- Right fold over the entries: `f` sees them in reverse slot order. -/
@[inline] def foldRev {ε : Type w} (f : ε → α → β → ε) (init : ε) (t : Table α β) : ε :=
  foldRevImpl f init t

/-- Monadic loop over the entries in slot order, with early exit. -/
@[inline] def forIn {ε : Type w} {m : Type w → Type w'} [Monad m]
    (f : α → β → ε → m (ForInStep ε)) (init : ε) (t : Table α β) : m ε :=
  forInImpl f init t

/-! ## Equation lemmas

The contract definitions are not exposed; these let the proof files unfold them. -/

theorem toListModel_def (t : Table α β) : t.toListModel = t.slots.entries := by
  unfold toListModel; rfl

theorem emptyWithCapacity_def (c : Nat) :
    (emptyWithCapacity c : Table α β) = emptyImpl c := by
  unfold emptyWithCapacity; rfl

theorem numBuckets_def (t : Table α β) :
    t.numBuckets = if t.slotKeys.size == 0 then 2 ^ lgFor (max t.reqCap 1) else t.ctrl.size - 8 :=
  by unfold numBuckets; rfl

theorem lookup_def {σ : Type w} (t : Table α β) (a : α) (f : α → β → σ) (g : Unit → σ) :
    t.lookup a f g = lookupImpl t a f g := by
  unfold lookup; rfl

theorem contains_def (t : Table α β) (a : α) : t.contains a = containsImpl t a := by
  unfold contains lookup; rfl

theorem lookupMem_def {σ : Type w} (t : Table α β) (a : α) (h : t.contains a = true)
    (f : α → β → σ) : t.lookupMem a h f = lookupMemImpl t a ((contains_def t a) ▸ h) f := by
  unfold lookupMem; rfl

theorem containsThenInsert_def (t : Table α β) (a : α) (b : β) :
    t.containsThenInsert a b = containsThenInsertImpl t a b := by
  unfold containsThenInsert; rfl

theorem insert_def (t : Table α β) (a : α) (b : β) :
    t.insert a b = (containsThenInsertImpl t a b).2 := by
  unfold insert containsThenInsert; rfl

theorem getThenInsertIfNew?_def (t : Table α β) (a : α) (b : β) :
    t.getThenInsertIfNew? a b = getThenInsertIfNewImpl t a b := by
  unfold getThenInsertIfNew?; rfl

theorem insertIfNew_def (t : Table α β) (a : α) (b : β) :
    t.insertIfNew a b = (getThenInsertIfNewImpl t a b).2 := by
  unfold insertIfNew getThenInsertIfNew?; rfl

theorem containsThenInsertIfNew_def (t : Table α β) (a : α) (b : β) :
    t.containsThenInsertIfNew a b =
      ((getThenInsertIfNewImpl t a b).1.isSome, (getThenInsertIfNewImpl t a b).2) := by
  unfold containsThenInsertIfNew getThenInsertIfNew?; rfl

theorem erase_def (t : Table α β) (a : α) : t.erase a = eraseImpl t a := by
  unfold erase; rfl

theorem alter_def (t : Table α β) (a : α) (f : Option β → Option β) :
    t.alter a f = alterImpl t a f := by
  unfold alter; rfl

theorem modify_def (t : Table α β) (a : α) (f : β → β) : t.modify a f = modifyImpl t a f := by
  unfold modify; rfl

theorem filter_def (f : α → β → Bool) (t : Table α β) : t.filter f = filterImpl f t := by
  unfold filter; rfl

theorem filterMap_def (f : α → β → Option γ) (t : Table α β) :
    t.filterMap f = filterMapImpl f t := by
  unfold filterMap; rfl

theorem map_def (f : α → β → γ) (t : Table α β) : t.map f = mapImpl f t := by
  unfold map; rfl

theorem foldM_def {ε : Type w} {m : Type w → Type w'} [Monad m] (f : ε → α → β → m ε)
    (init : ε) (t : Table α β) : t.foldM f init = foldMImpl f init t := by
  unfold foldM; rfl

theorem foldRev_def {ε : Type w} (f : ε → α → β → ε) (init : ε) (t : Table α β) :
    t.foldRev f init = foldRevImpl f init t := by
  unfold foldRev; rfl

theorem forIn_def {ε : Type w} {m : Type w → Type w'} [Monad m]
    (f : α → β → ε → m (ForInStep ε)) (init : ε) (t : Table α β) :
    t.forIn f init = forInImpl f init t := by
  unfold forIn; rfl

end Table

end SwissTable.Core
