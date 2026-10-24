module

public import OAMap.Core.Swiss.Loops

/-!
# Swiss core proofs, part 3: the empty table, `findFree`, and the rebuild's move loops

A proof file of the SwissTable core (`OAMap/Core/Swiss/Table.lean`, "Proof structure"). Its
owner edits only this file: the proofs, and any private helper lemmas or definitions. The
statements are fixed (later files use them), except those marked *suggested route*, which no
other file uses and which may be changed or dropped.

* **The empty table** (`Build.lean`: `emptyTable`, `rebuild`): `emptyCtrl (2 ^ lg)` is `2 ^ lg + 8`
  EMPTY bytes (`dblTo` doubles `emptyGroup` exactly up to `2 ^ lg`), so the fresh arrays are a
  well-formed empty table (`WF.empty`) and satisfy the move loops' hypotheses (`moveDstU`,
  `moveDstN`).
* **`findFree`** (`Build.lean`, `Table.lean`'s `insertFresh`, `Write.lean`): it ends at a slot or
  `mask + 1` (`freeBound`, `freeBoundN`), and, when the table has a free slot, at a free slot its
  probe reaches (`WF.findFree_slot`, `WF.findFreeN_slot`): the first group with a free byte, so
  no earlier group has an EMPTY byte.
* **The rebuild** (`Build.lean`'s `rebuild`; `Write.lean` lifts the entries to `Table`): the move
  loops build a well-formed table (`WF.rebuild`) with the same entries up to order
  (`rebuild_perm_raw`), with no key comparison and no lawfulness.

Suggested route (the earlier linear-probing map's `Grow.lean`: `ReinsertInv`, `reinsertN_inv`,
`entries_grow_perm`): first `moveLoop_eq_moveLoopN` and `findFree_toNat` (the machine-word loops
are the `Nat` ones, through `setCtrl_eq_setCtrlN`, `ctrlWord_eq_ctrlWordN`, `homeU_toNat` and
`Array.uset_eq_set`), then an invariant of `moveLoopN` after the old slots below `i` are moved:
the new arrays are mirrored, of the right sizes, hold only EMPTY and FULL bytes, carry the tags of
the new shift, satisfy `Distinct`/`ProbeInv` under lawfulness (a moved key is not `==` to any key
moved before it, by the old table's `Distinct`), have no tombstones, and hold the entries of the
old slots below `i` up to order. The probe of a moved key passes only groups without a free byte
(`findFree`), hence without an EMPTY byte.
-/

@[expose] public section

universe u v w

namespace OAMap.Core.Swiss

variable {α : Type u} {β : Type v}

/-! ## The empty table -/

theorem size_emptyCtrl {lg : Nat} (h : 3 ≤ lg) :
    (emptyCtrl ((2 : Nat) ^ lg)).size = (2 : Nat) ^ lg + 8 := by
  sorry

theorem getElem!_emptyCtrl {lg : Nat} (h : 3 ≤ lg) {i : Nat} (hi : i < (2 : Nat) ^ lg + 8) :
    (emptyCtrl ((2 : Nat) ^ lg))[i]! = EMPTY := by
  sorry

theorem mirrored_emptyCtrl {lg : Nat} (h : 3 ≤ lg) :
    Mirrored (emptyCtrl ((2 : Nat) ^ lg)) ((2 : Nat) ^ lg) := by
  sorry

/-- The fresh arrays of `2 ^ lg` slots are a well-formed empty table. -/
theorem WF.empty [BEq α] [Hashable α] {lg : Nat} (k0 : α) (v0 : β) (h : 3 ≤ lg) :
    WF ⟨emptyCtrl ((2 : Nat) ^ lg), Array.replicate ((2 : Nat) ^ lg + 1) k0,
        Array.replicate ((2 : Nat) ^ lg + 1) v0⟩
      0 (capacityOf ((2 : Nat) ^ lg)) (((2 : Nat) ^ lg - 1).toUSize) ((57 - lg).toUInt64) := by
  sorry

/-- The fresh arrays of a machine-word rebuild into `2 ^ lg ≤ 2 ^ 31` slots. -/
theorem moveDstU {lg : Nat} (h3 : 3 ≤ lg) (hs : smallMask (((2 : Nat) ^ lg - 1).toUSize) = true)
    {c : ByteArray} {k : Array α} {v : Array β} {k0 : α} {v0 : β} :
    MoveDstU (c.propagateMark (emptyCtrl ((2 : Nat) ^ lg)))
      (k.propagateMark (Array.replicate ((2 : Nat) ^ lg + 1) k0))
      (v.propagateMark (Array.replicate ((2 : Nat) ^ lg + 1) v0))
      (((2 : Nat) ^ lg - 1).toUSize) := by
  sorry

/-- The fresh arrays of a rebuild on `Nat` indices into `2 ^ lg` slots. -/
theorem moveDstN {lg : Nat} (h3 : 3 ≤ lg) {c : ByteArray} {k : Array α} {v : Array β} {k0 : α}
    {v0 : β} :
    MoveDstN (c.propagateMark (emptyCtrl ((2 : Nat) ^ lg)))
      (k.propagateMark (Array.replicate ((2 : Nat) ^ lg + 1) k0))
      (v.propagateMark (Array.replicate ((2 : Nat) ^ lg + 1) v0)) ((2 : Nat) ^ lg) := by
  sorry

/-! ## `findFree` -/

/-- `findFree` ends at a slot or at `mask + 1`. -/
theorem freeBound {mask : USize} : FreeBound mask := by
  sorry

/-- `findFreeN` ends at a slot or at `cap`. -/
theorem freeBoundN {cap : Nat} : FreeBoundN cap := by
  sorry

/-- `findFree` is `findFreeN` (suggested route; not used outside this file). -/
theorem findFree_toNat {c : ByteArray} {cap : Nat} {mask : USize} (hg : Geom cap mask)
    (hsz : c.size = cap + 8) {pos stride : USize} {hA : ArrU c mask} {hp : pos.toNat ≤ mask.toNat}
    {hs : stride.toNat ≤ mask.toNat} {hA' : CtrlN c cap} {hp' : pos.toNat < cap} :
    (findFree c mask pos stride hA hp hs).toNat =
      findFreeN c cap pos.toNat stride.toNat hA' hp' := by
  sorry

/-- **`findFree` finds a free slot that the probe reaches**, in a table with room. -/
theorem WF.findFree_slot [BEq α] [Hashable α] {s : Slots α β} {size gl : Nat} {mask : USize}
    {shift : UInt64} (wf : WF s size gl mask shift) (hs : smallMask mask = true) {a : α}
    (h : FreshPre s gl a) :
    s.FreeSlot (homeN (hashBits shift a) s.cap)
      (findFree s.ctrl mask (homeU (hashBits shift a) mask) 0 (wf.loopU' hs).arr (and_mask_le _ _)
        stride_zero).toNat := by
  sorry

/-- **`findFreeN` finds a free slot that the probe reaches**, in a table with room. -/
theorem WF.findFreeN_slot [BEq α] [Hashable α] {s : Slots α β} {size gl : Nat} {mask : USize}
    {shift : UInt64} (wf : WF s size gl mask shift) (hs : ¬smallMask mask = true) {a : α}
    (h : FreshPre s gl a) :
    s.FreeSlot (homeN (hashBits shift a) s.cap)
      (findFreeN s.ctrl (s.ctrl.size - 8) (homeN (hashBits shift a) (s.ctrl.size - 8)) 0
        (wf.ctrlN' hs) (Nat.mod_lt _ (wf.ctrlN' hs).pos)) := by
  sorry

section Fresh

variable [BEq α] [Hashable α] {s : Slots α β} {size gl : Nat} {mask : USize} {shift : UInt64}

/-! Bounds of `insertFresh`'s writes (`findFree` ends at most at `mask + 1`, a cell of an
allocated table). -/

theorem WF.fresh_ctrl (wf : WF s size gl mask shift) (hs : smallMask mask = true) {a : α}
    (h : FreshPre s gl a) {pos stride : USize} {hA : ArrU s.ctrl mask}
    {hp : pos.toNat ≤ mask.toNat} {hs' : stride.toNat ≤ mask.toNat} :
    (findFree s.ctrl mask pos stride hA hp hs').toNat < s.ctrl.size := by
  sorry

theorem WF.fresh_keys (wf : WF s size gl mask shift) (hs : smallMask mask = true) {a : α}
    (h : FreshPre s gl a) {pos stride : USize} {hA : ArrU s.ctrl mask}
    {hp : pos.toNat ≤ mask.toNat} {hs' : stride.toNat ≤ mask.toNat} :
    (findFree s.ctrl mask pos stride hA hp hs').toNat < s.keys.size := by
  sorry

theorem WF.fresh_vals (wf : WF s size gl mask shift) (hs : smallMask mask = true) {a : α}
    (h : FreshPre s gl a) {pos stride : USize} {hA : ArrU s.ctrl mask}
    {hp : pos.toNat ≤ mask.toNat} {hs' : stride.toNat ≤ mask.toNat} :
    (findFree s.ctrl mask pos stride hA hp hs').toNat < s.vals.size := by
  sorry

theorem WF.freshN_ctrl (wf : WF s size gl mask shift) (hs : ¬smallMask mask = true) {a : α}
    (h : FreshPre s gl a) {pos stride : Nat} {hA : CtrlN s.ctrl (s.ctrl.size - 8)}
    {hp : pos < s.ctrl.size - 8} :
    findFreeN s.ctrl (s.ctrl.size - 8) pos stride hA hp < s.ctrl.size := by
  sorry

theorem WF.freshN_keys (wf : WF s size gl mask shift) (hs : ¬smallMask mask = true) {a : α}
    (h : FreshPre s gl a) {pos stride : Nat} {hA : CtrlN s.ctrl (s.ctrl.size - 8)}
    {hp : pos < s.ctrl.size - 8} :
    findFreeN s.ctrl (s.ctrl.size - 8) pos stride hA hp < s.keys.size := by
  sorry

theorem WF.freshN_vals (wf : WF s size gl mask shift) (hs : ¬smallMask mask = true) {a : α}
    (h : FreshPre s gl a) {pos stride : Nat} {hA : CtrlN s.ctrl (s.ctrl.size - 8)}
    {hp : pos < s.ctrl.size - 8} :
    findFreeN s.ctrl (s.ctrl.size - 8) pos stride hA hp < s.vals.size := by
  sorry

end Fresh

/-! ## The move loops -/

/-- `moveLoop` is `moveLoopN` (suggested route; not used outside this file). -/
theorem moveLoop_eq_moveLoopN [Hashable α] {oc : ByteArray} {ok : Array α} {ov : Array β}
    {omask i : USize} {nc : ByteArray} {nk : Array α} {nv : Array β} {nmask : USize}
    {nshift : UInt64} {ocap ncap : Nat} (hog : omask.toNat + 1 = ocap) (hg : Geom ncap nmask)
    (hsz : nc.size = ncap + 8) (hi : i.toNat ≤ ocap) {hO : MoveSrcU oc ok ov omask}
    {hN : MoveDstU nc nk nv nmask} {hff : FreeBound nmask} {hO' : MoveSrcN oc ok ov ocap}
    {hN' : MoveDstN nc nk nv ncap} {hff' : FreeBoundN ncap} :
    moveLoop oc ok ov omask i nc nk nv nmask nshift hO hN hff =
      moveLoopN oc ok ov ocap i.toNat nc nk nv ncap nshift hO' hN' hff' := by
  sorry

section Move

variable [BEq α] [Hashable α] {ctrl : ByteArray} {keys : Array α} {vals : Array β}
  {size gl : Nat} {mask : USize} {shift : UInt64}

/-- **The rebuild builds a well-formed table**: `size` entries in `2 ^ lg` slots, no
tombstones, `growthLeft = capacity - size`. The hypothesis is the move of `Build.lean`'s
`rebuild`, word for word. -/
theorem WF.rebuild (wf : WF ⟨ctrl, keys, vals⟩ size gl mask shift) {lg : Nat} {k0 : α} {v0 : β}
    (h : RebuildPre ⟨ctrl, keys, vals⟩ size lg) {nc : ByteArray} {nk : Array α} {nv : Array β}
    (hm : (if hs : smallMask (((2 : Nat) ^ lg - 1).toUSize) = true then
        moveLoop ctrl keys vals mask 0 (ctrl.propagateMark (emptyCtrl ((2 : Nat) ^ lg)))
          (keys.propagateMark (Array.replicate ((2 : Nat) ^ lg + 1) k0))
          (vals.propagateMark (Array.replicate ((2 : Nat) ^ lg + 1) v0))
          (((2 : Nat) ^ lg - 1).toUSize) ((57 - lg).toUInt64) (wf.moveSrcU h hs)
          (moveDstU h.three_le hs) freeBound
      else
        moveLoopN ctrl keys vals (ctrl.size - 8) 0 (ctrl.propagateMark (emptyCtrl ((2 : Nat) ^ lg)))
          (keys.propagateMark (Array.replicate ((2 : Nat) ^ lg + 1) k0))
          (vals.propagateMark (Array.replicate ((2 : Nat) ^ lg + 1) v0)) ((2 : Nat) ^ lg)
          ((57 - lg).toUInt64) wf.moveSrcN (moveDstN h.three_le) freeBoundN) = (nc, nk, nv)) :
    WF ⟨nc, nk, nv⟩ size (capacityOf ((2 : Nat) ^ lg) - size) (((2 : Nat) ^ lg - 1).toUSize)
      ((57 - lg).toUInt64) := by
  sorry

/-- **The rebuild keeps the entries**, up to order (no lawfulness: no key is compared). -/
theorem rebuild_perm_raw (wf : WF ⟨ctrl, keys, vals⟩ size gl mask shift) {lg : Nat} {k0 : α}
    {v0 : β} (h : RebuildPre ⟨ctrl, keys, vals⟩ size lg) {nc : ByteArray} {nk : Array α}
    {nv : Array β}
    (hm : (if hs : smallMask (((2 : Nat) ^ lg - 1).toUSize) = true then
        moveLoop ctrl keys vals mask 0 (ctrl.propagateMark (emptyCtrl ((2 : Nat) ^ lg)))
          (keys.propagateMark (Array.replicate ((2 : Nat) ^ lg + 1) k0))
          (vals.propagateMark (Array.replicate ((2 : Nat) ^ lg + 1) v0))
          (((2 : Nat) ^ lg - 1).toUSize) ((57 - lg).toUInt64) (wf.moveSrcU h hs)
          (moveDstU h.three_le hs) freeBound
      else
        moveLoopN ctrl keys vals (ctrl.size - 8) 0 (ctrl.propagateMark (emptyCtrl ((2 : Nat) ^ lg)))
          (keys.propagateMark (Array.replicate ((2 : Nat) ^ lg + 1) k0))
          (vals.propagateMark (Array.replicate ((2 : Nat) ^ lg + 1) v0)) ((2 : Nat) ^ lg)
          ((57 - lg).toUInt64) wf.moveSrcN (moveDstN h.three_le) freeBoundN) = (nc, nk, nv)) :
    (Slots.entries ⟨nc, nk, nv⟩).Perm (Slots.entries ⟨ctrl, keys, vals⟩) := by
  sorry

/-- The rebuilt table has `2 ^ lg` slots. -/
theorem rebuild_cap_raw (wf : WF ⟨ctrl, keys, vals⟩ size gl mask shift) {lg : Nat} {k0 : α}
    {v0 : β} (h : RebuildPre ⟨ctrl, keys, vals⟩ size lg) {nc : ByteArray} {nk : Array α}
    {nv : Array β}
    (hm : (if hs : smallMask (((2 : Nat) ^ lg - 1).toUSize) = true then
        moveLoop ctrl keys vals mask 0 (ctrl.propagateMark (emptyCtrl ((2 : Nat) ^ lg)))
          (keys.propagateMark (Array.replicate ((2 : Nat) ^ lg + 1) k0))
          (vals.propagateMark (Array.replicate ((2 : Nat) ^ lg + 1) v0))
          (((2 : Nat) ^ lg - 1).toUSize) ((57 - lg).toUInt64) (wf.moveSrcU h hs)
          (moveDstU h.three_le hs) freeBound
      else
        moveLoopN ctrl keys vals (ctrl.size - 8) 0 (ctrl.propagateMark (emptyCtrl ((2 : Nat) ^ lg)))
          (keys.propagateMark (Array.replicate ((2 : Nat) ^ lg + 1) k0))
          (vals.propagateMark (Array.replicate ((2 : Nat) ^ lg + 1) v0)) ((2 : Nat) ^ lg)
          ((57 - lg).toUInt64) wf.moveSrcN (moveDstN h.three_le) freeBoundN) = (nc, nk, nv)) :
    (Slots.mk nc nk nv).cap = (2 : Nat) ^ lg := by
  sorry

end Move

end OAMap.Core.Swiss
