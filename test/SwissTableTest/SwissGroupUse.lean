module

import SwissTable.Core.Swiss.Group

/-!
# The SWAR group library, used from another module

`SwissTable.Core.Swiss.Group` is a `public section` without `@[expose]`: a module that imports it
sees the statements but cannot unfold the definitions (`matchTag`, `ctrlWord`, `slotByte`,
`setCtrl`, `needsTombstone`, …). This module is such an importer. It proves, with the exported
lemmas only, the two steps a SwissTable-layout core needs that touch every part of the library:

* `slot_of_matchTag` (lookup): the candidate slot `(pos + lowestLane m) &&& mask` of a nonzero tag
  mask `m` of the group at `pos` holds the tag;
* `erase_creates_no_empty_window` (erase): writing the byte the erase rule picks creates no EMPTY
  slot in an 8-slot window that had none, so no probe that passed a window before the erase stops
  in it afterwards.

The `example`s check that `decide` works on `IsCtrl` and `IsMask` from outside.
-/

open SwissTable.Core.Swiss

namespace SwissTableTest.SwissGroupUse

/-- **Lookup step.** A nonzero tag mask of the group at `pos` names, through `lowestLane`, a slot
whose control byte is the tag. -/
theorem slot_of_matchTag {c : ByteArray} {cap : Nat} {mask pos : USize} {t : UInt8}
    (h : Mirrored c cap) (hg : Geom cap mask) (hp : pos.toNat < cap)
    (hm : matchTag (ctrlWord c pos (h.group_bound hp)) (repTag t) ≠ 0) :
    slotByte c cap
      ((pos + lowestLane (matchTag (ctrlWord c pos (h.group_bound hp)) (repTag t))) &&& mask).toNat
      = t := by
  obtain ⟨hl8, hf, -⟩ := lowestLane_spec (isMask_matchTag _ _) hm
  rw [flag_matchTag_ctrlWord h hg.cap_le_size _ t hl8, beq_iff_eq] at hf
  rw [hg.toNat_add_and_mask]
  exact hf

/-- **Erase step.** Erase the full slot `i` as hashbrown does: DELETED when `needsTombstone`
says so, EMPTY otherwise. Every 8-slot window (the group at any `p`) that has an EMPTY slot after
the write had one before. -/
theorem erase_creates_no_empty_window {c : ByteArray} {cap : Nat} {mask i : USize}
    (h : Mirrored c cap) (hg : Geom cap mask) (hctrl : ∀ k < cap, IsCtrl (slotByte c cap k))
    (hi : i.toNat < cap) (p : Nat)
    (hnew : ∃ l < 8, slotByte
      (setCtrl c mask i
        (if needsTombstone (matchEmpty (ctrlWord c i (h.group_bound hi)))
            (matchEmpty (ctrlWord c ((i - 8) &&& mask) (h.group_bound (hg.and_mask_lt _))))
          then DELETED else EMPTY)
        (h.lt_size hi) (h.mask_lt hg.mask_add_one)) cap ((p + l) % cap) = EMPTY) :
    ∃ l < 8, slotByte c cap ((p + l) % cap) = EMPTY := by
  obtain ⟨l, hl, he⟩ := hnew
  rw [hg.slotByte_setCtrl h _ _ _ hi] at he
  split at he
  · rename_i hpi
    split at he
    · exact absurd he DELETED_ne_EMPTY
    · rename_i hrule
      exact exists_empty_of_needsTombstone_eq_false h hg hctrl _ _
        (Bool.eq_false_iff.mpr hrule) hl (by rwa [Nat.mod_mod] at hpi)
  · exact ⟨l, hl, he⟩

example : IsCtrl 0x7F := by decide
example : IsCtrl EMPTY := by rw [EMPTY_eq]; decide
example : ¬ IsCtrl 0x81 := by decide
example : IsMask 0x8000000000000080 := by decide
example : ¬ IsMask 1 := by decide

end SwissTableTest.SwissGroupUse
