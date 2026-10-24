module

public import SwissTable.Core.Swiss.Proofs.Query

/-!
# Swiss core proofs, part 7: insert, insertIfNew, erase, alter, modify (contract 12–16)

A proof file of the Swiss core (`SwissTable/Core/Swiss/Table.lean`, "Proof structure"): the
contract lemmas 12–16 (`docs/ARCHITECTURE.md` §3.3).

Every operation takes one of two paths (machine words on tables of at most `2 ^ 31` slots, `Nat`
indices beyond), and on each path ends in one of the writes of `Proofs/Write.lean`, whose entries
are known. The private lemmas state each write as a list operation, and each contract lemma is a
case split over the paths and the probe's result:

* a hit (`WF.insProbeU_hit`, `WF.insSlotN_hit`, ...): the key and value of the slot replaced,
  `replaceEntry` (`WF.entries_kvN_replace`), which is `insertEntry` since the key is present;
  `modify` and `alter` write the placeholder value first (`Array.set_set`/`Array.uset_eq_set`
  make it one write); an erasure is `eraseKey` (`WF.entries_eraseN_eraseKey`, as
  `eraseAtU_eraseKey` and `eraseAtN_eraseKey`);
* a new key (`WF.insProbeU_new`, `WF.fast_new`, `WF.insSlotN_new`, ...): a `NewSlot`, absent for
  lawful instances, so `insertEntry` is a cons; the write adds the entry (`entries_newN_perm`, as
  `insertNewU_perm` and `insertNewN_perm`), directly or after `reserveInsert` rebuilt the table
  (`reserveInsert_perm`: `reserveTable_perm`, then `insertFresh_perm` with `WF.findFree_slot`).

The machine-word writes are the `Nat` ones through `setCtrl_eq_setCtrlN`, `Array.uset_eq_set`,
`WF.geom` and `homeU_toNat`. The values the list operations read (`getValue?`) come from the hit
(`WF.getEntry?_hit`).

`Const.alterKey` and `Const.modifyKey` are not exposed by Std, so their definitions cannot be
unfolded here; `alterKey_perm` recovers the `match` of the definition up to order, by induction
with Std's `Const.alterKey_cons_perm`, and `Const.modifyKey_eq_alterKey` reduces `modifyKey` to
it. This is why `modifyAtU_modifyKey` and `modifyAtN_modifyKey` are stated up to order.
-/

@[expose] public section

universe u v w w'

open Std.Internal.List

namespace SwissTable.Core

namespace Swiss

variable {α : Type u} {β : Type v}

section Lists

variable [BEq α]

/-! ### `Const.alterKey` and `Const.modifyKey`

Their definitions are not exposed (Std), so they are read off Std's lemmas: up to order,
`Const.alterKey` is the `match` of its definition (`alterKey_perm`). -/

/-- `Const.alterKey`, up to order, by the value it reads. -/
private theorem alterKey_perm (a : α) (f : Option β → Option β) (l : List ((_ : α) × β)) :
    (Const.alterKey a f l).Perm
      (match f (getValue? a l) with
        | none => eraseKey a l
        | some v => insertEntry a v l) := by
  induction l with
  | nil =>
    rw [Const.alterKey_nil, getValue?_nil]
    split <;> simp_all
  | cons e l ih =>
    obtain ⟨k', v'⟩ := e
    refine Const.alterKey_cons_perm.trans ?_
    by_cases hk : (k' == a) = true
    · simp only [hk, ↓reduceIte]
      rw [getValue?_cons_of_true hk, eraseKey_cons_of_beq hk]
      cases f (some v') with
      | none => exact List.Perm.refl _
      | some w => dsimp only; rw [insertEntry_cons_of_beq hk]
    · have hk' : (k' == a) = false := by simpa using hk
      simp only [hk', Bool.false_eq_true, ↓reduceIte]
      rw [getValue?_cons_of_false hk', eraseKey_cons_of_false hk']
      refine (ih.cons _).trans ?_
      cases f (getValue? a l) with
      | none => exact List.Perm.refl _
      | some w => exact (insertEntry_cons_of_false hk').symm

private theorem alterKey_perm_some {a : α} {f : Option β → Option β} {l : List ((_ : α) × β)}
    {o : Option β} (ho : getValue? a l = o) {v' : β} (hf : f o = some v') :
    (Const.alterKey a f l).Perm (insertEntry a v' l) := by
  have := alterKey_perm a f l
  rw [ho, hf] at this
  exact this

private theorem alterKey_perm_none {a : α} {f : Option β → Option β} {l : List ((_ : α) × β)}
    {o : Option β} (ho : getValue? a l = o) (hf : f o = none) :
    (Const.alterKey a f l).Perm (eraseKey a l) := by
  have := alterKey_perm a f l
  rw [ho, hf] at this
  exact this

end Lists

section Writes

variable [BEq α] [Hashable α]

/-- The arrays of a table built from its fields. -/
private theorem slots_mk {ctrl : ByteArray} {keys : Array α} {vals : Array β} {size gl : Nat}
    {mask : USize} {shift : UInt64} {req : Nat}
    {wf : WF ⟨ctrl, keys, vals⟩ size gl mask shift} :
    Table.slots ⟨ctrl, keys, vals, size, gl, mask, shift, req, wf⟩ = ⟨ctrl, keys, vals⟩ := rfl

/-- A machine-word control write in an allocated table on the machine-word path is the `Nat`
one. -/
private theorem setCtrl_eqN {ctrl : ByteArray} {keys : Array α} {vals : Array β} {size gl : Nat}
    {mask : USize} {shift : UInt64} (wf : WF ⟨ctrl, keys, vals⟩ size gl mask shift)
    (hs : smallMask mask = true) {i : USize} (hi : i.toNat < ctrl.size - 8) {b : UInt8}
    {h1 : i.toNat < ctrl.size} {h2 : mask.toNat + 8 < ctrl.size} :
    setCtrl ctrl mask i b h1 h2 =
      setCtrlN ctrl (ctrl.size - 8) i.toNat b h1 wf.cap_word (by omega) := by
  have hcap : 0 < Slots.cap ⟨ctrl, keys, vals⟩ := by simp only [Slots.cap]; omega
  exact setCtrl_eq_setCtrlN (wf.geom hs hcap) hi

/-- Two writes to the same cell are the last one. -/
private theorem uset_uset {γ : Type w} {xs : Array γ} {i : USize} (x y : γ) (h : i.toNat < xs.size)
    {h' : i.toNat < (xs.uset i x h).size} : (xs.uset i x h).uset i y h' = xs.uset i y h :=
  Array.set_set x h

/-- The value list operations read at a hit for `a`. -/
private theorem getValue?_hit {s : Slots α β} {size gl : Nat} {mask : USize} {shift : UInt64}
    (wf : WF s size gl mask shift) {a : α} {i : Nat} (hit : s.Hit shift a i) {v : β}
    (hv : s.vals[i]? = some v) [EquivBEq α] [LawfulHashable α] :
    getValue? a s.entries = some v := by
  obtain ⟨k, hk, -⟩ := hit.2.2
  rw [getValue?_eq_getEntry?, wf.getEntry?_hit hit hk hv]
  rfl

/-- A hit for `a` makes `a` a key of the entries. -/
private theorem containsKey_hit {s : Slots α β} {size gl : Nat} {mask : USize} {shift : UInt64}
    (wf : WF s size gl mask shift) {a : α} {i : Nat} (hit : s.Hit shift a i) [EquivBEq α]
    [LawfulHashable α] : containsKey a s.entries = true := by
  obtain ⟨k, hk, -⟩ := hit.2.2
  rw [containsKey_eq_isSome_getEntry?,
    wf.getEntry?_hit hit hk (Array.getElem?_eq_getElem (wf.vals_lt hit.1.1))]
  rfl

/-- An absent key is not a key of the entries. -/
private theorem containsKey_absent {s : Slots α β} {a : α} (habs : s.Absent a) :
    containsKey a s.entries = false :=
  getEntry?_eq_none.1 (getEntry?_absent habs)

/-- An absent key has no value. -/
private theorem getValue?_absent {s : Slots α β} {a : α} (habs : s.Absent a) :
    getValue? a s.entries = none :=
  getValue?_eq_none.2 (containsKey_absent habs)

/-- `Const.modifyKey` at a hit. -/
private theorem modifyKey_of_hit {s : Slots α β} {size gl : Nat} {mask : USize} {shift : UInt64}
    (wf : WF s size gl mask shift) {a : α} {i : Nat} (hit : s.Hit shift a i) {f : β → β} {v : β}
    (hv : s.vals[i]? = some v) [EquivBEq α] [LawfulHashable α] :
    (Const.modifyKey a f s.entries).Perm (replaceEntry a (f v) s.entries) := by
  rw [Const.modifyKey_eq_alterKey,
    ← insertEntry_of_containsKey (v := f v) (containsKey_hit wf hit)]
  exact alterKey_perm_some (getValue?_hit wf hit hv) rfl

/-- `Const.modifyKey` of an absent key. -/
private theorem modifyKey_absent {s : Slots α β} {a : α} (habs : s.Absent a) {f : β → β} :
    (Const.modifyKey a f s.entries).Perm s.entries := by
  rw [Const.modifyKey_eq_alterKey]
  exact (alterKey_perm_none (getValue?_absent habs) rfl).trans
    (List.Perm.of_eq (eraseKey_of_containsKey_eq_false (containsKey_absent habs)))

/-- The key and value of a hit for `a` replaced: `insertEntry`. -/
private theorem kvN_insertEntry {ctrl : ByteArray} {keys : Array α} {vals : Array β}
    {size gl : Nat} {mask : USize} {shift : UInt64} (wf : WF ⟨ctrl, keys, vals⟩ size gl mask shift)
    {a : α} {i : Nat} (hit : Slots.Hit ⟨ctrl, keys, vals⟩ shift a i) (b : β)
    {h1 : i < keys.size} {h2 : i < vals.size} [EquivBEq α] [LawfulHashable α] :
    (Slots.mk ctrl (keys.set i a h1) (vals.set i b h2)).entries.Perm
      (insertEntry a b (Slots.entries ⟨ctrl, keys, vals⟩)) := by
  rw [wf.entries_kvN_replace hit, insertEntry_of_containsKey (containsKey_hit wf hit)]

/-- `kvN_insertEntry` on machine words. -/
private theorem kvU_insertEntry {ctrl : ByteArray} {keys : Array α} {vals : Array β}
    {size gl : Nat} {mask : USize} {shift : UInt64} (wf : WF ⟨ctrl, keys, vals⟩ size gl mask shift)
    {a : α} {i : USize} (hit : Slots.Hit ⟨ctrl, keys, vals⟩ shift a i.toNat) (b : β)
    {h1 : i.toNat < keys.size} {h2 : i.toNat < vals.size} [EquivBEq α] [LawfulHashable α] :
    (Slots.mk ctrl (keys.uset i a h1) (vals.uset i b h2)).entries.Perm
      (insertEntry a b (Slots.entries ⟨ctrl, keys, vals⟩)) := by
  rw [Array.uset_eq_set, Array.uset_eq_set]
  exact kvN_insertEntry wf hit b

/-- The erasure by the tombstone rule of the hit for `a`, on machine words: `eraseKey`. -/
private theorem eraseU_entries {ctrl : ByteArray} {keys : Array α} {vals : Array β}
    {size gl : Nat} {mask : USize} {shift : UInt64} (wf : WF ⟨ctrl, keys, vals⟩ size gl mask shift)
    (hs : smallMask mask = true) {a : α} {i : USize}
    (hit : Slots.Hit ⟨ctrl, keys, vals⟩ shift a i.toNat) {hw1 : i.toNat + 8 ≤ ctrl.size}
    {hw2 : ((i - 8) &&& mask).toNat + 8 ≤ ctrl.size} {h1 : i.toNat < ctrl.size}
    {h2 : mask.toNat + 8 < ctrl.size} {k0 : α} {v0 : β} {h3 : i.toNat < keys.size}
    {h4 : i.toNat < vals.size} [EquivBEq α] [LawfulHashable α] :
    (Slots.mk
      (setCtrl ctrl mask i (if needsTombstone (matchEmpty (ctrlWord ctrl i hw1))
        (matchEmpty (ctrlWord ctrl ((i - 8) &&& mask) hw2)) then DELETED else EMPTY) h1 h2)
      (keys.uset i k0 h3) (vals.uset i v0 h4)).entries =
      eraseKey a (Slots.entries ⟨ctrl, keys, vals⟩) := by
  have hic : i.toNat < ctrl.size - 8 := hit.1.1
  have hcap : 0 < Slots.cap ⟨ctrl, keys, vals⟩ := hit.1.cap_pos
  have hg := wf.geom hs hcap
  have hle := wf.cap_le_of_smallMask hs
  have h8 := hg.le_cap
  simp only [Slots.cap] at hic hcap hg hle h8
  have hA : ctrlWord ctrl i hw1 = ctrlWordN ctrl i.toNat hw1 :=
    ctrlWord_eq_ctrlWordN (by omega)
  have hB : ctrlWord ctrl ((i - 8) &&& mask) hw2 =
      ctrlWordN ctrl ((i.toNat + (ctrl.size - 8) - 8) % (ctrl.size - 8))
        (by have := Nat.mod_lt (i.toNat + (ctrl.size - 8) - 8) hcap; omega) := by
    have hm := hg.toNat_sub_eight_and_mask i
    rw [ctrlWord_eq_ctrlWordN (h' := hw2)
      (by have := Nat.mod_lt (i.toNat + (ctrl.size - 8 - 8)) hcap; omega)]
    exact ctrlWordN_congr (by rw [hm]; congr 1; omega)
  rw [setCtrl_eqN wf hs hic, Array.uset_eq_set, Array.uset_eq_set, hA, hB]
  exact wf.entries_eraseN_eraseKey hit (sz := size) (g := gl) (hic := hic) (hc := wf.cap_word)
    (Prod.eta _).symm

/-- `insertFresh` adds its entry. -/
private theorem insertFresh_perm (t : Table α β) (a : α) (b : β)
    (h : FreshPre t.slots t.growthLeft a) :
    (insertFresh t a b h).slots.entries.Perm (⟨a, b⟩ :: t.slots.entries) := by
  obtain ⟨ctrl, keys, vals, size, gl, mask, shift, req, wf⟩ := t
  unfold insertFresh
  dsimp only
  split <;> rw [slots_mk, slots_mk]
  · rename_i hs
    have slot := wf.findFree_slot hs h
    rw [setCtrl_eqN wf hs slot.lt, Array.uset_eq_set, Array.uset_eq_set]
    exact entries_newN_perm slot (tagOf_lt _) a b
  · rename_i hs
    exact entries_newN_perm (wf.findFreeN_slot hs h) (tagOf_lt _) a b

/-- `reserveInsert` adds its entry. -/
private theorem reserveInsert_perm (t : Table α β) (a : α) (b : β)
    (h : ∀ [EquivBEq α] [LawfulHashable α], t.slots.Absent a) :
    (reserveInsert t a b h).slots.entries.Perm (⟨a, b⟩ :: t.slots.entries) := by
  unfold reserveInsert
  exact (insertFresh_perm _ a b _).trans ((reserveTable_perm t a b).cons _)

/-- A new key written on machine words adds its entry. -/
private theorem insertNewU_perm (t : Table α β) (a : α) (b : β) (q : UInt64) (i : USize)
    (hs : smallMask t.mask = true) (h : NewSlot t.slots t.shift a q i.toNat) :
    (insertNewU t a b q i hs h).slots.entries.Perm (⟨a, b⟩ :: t.slots.entries) := by
  obtain ⟨ctrl, keys, vals, size, gl, mask, shift, req, wf⟩ := t
  unfold insertNewU
  dsimp only
  split
  · split
    · exact reserveInsert_perm _ a b h.absent
    · rename_i hold hgl
      rw [slots_mk, slots_mk]
      have hc := wf.new_alloc_gl h hgl
      have slot := h.slot.resolve_right (fun h0 => Nat.pos_iff_ne_zero.mp hc h0.1)
      rw [setCtrl_eqN wf hs slot.lt, Array.uset_eq_set, Array.uset_eq_set]
      exact entries_newN_perm slot (tagOf_lt _) a b
  · rename_i hold
    rw [slots_mk, slots_mk]
    have hc := wf.new_alloc_old h hold
    have slot := h.slot.resolve_right (fun h0 => Nat.pos_iff_ne_zero.mp hc h0.1)
    rw [setCtrl_eqN wf hs slot.lt, Array.uset_eq_set, Array.uset_eq_set]
    exact entries_newN_perm slot (tagOf_lt _) a b

/-- A new key written on `Nat` indices adds its entry. -/
private theorem insertNewN_perm (t : Table α β) (a : α) (b : β) (q : UInt64) (i : Nat)
    (h : NewSlot t.slots t.shift a q i) :
    (insertNewN t a b q i h).slots.entries.Perm (⟨a, b⟩ :: t.slots.entries) := by
  obtain ⟨ctrl, keys, vals, size, gl, mask, shift, req, wf⟩ := t
  unfold insertNewN
  dsimp only
  split
  · split
    · exact reserveInsert_perm _ a b h.absent
    · rename_i hold hgl
      rw [slots_mk, slots_mk]
      have hc := wf.new_alloc_gl h hgl
      have slot := h.slot.resolve_right (fun h0 => Nat.pos_iff_ne_zero.mp hc h0.1)
      exact entries_newN_perm slot (tagOf_lt _) a b
  · rename_i hold
    rw [slots_mk, slots_mk]
    have hc := wf.new_alloc_oldN h hold
    have slot := h.slot.resolve_right (fun h0 => Nat.pos_iff_ne_zero.mp hc h0.1)
    exact entries_newN_perm slot (tagOf_lt _) a b

/-- Erasing the hit for `a` on machine words is `eraseKey`. -/
private theorem eraseAtU_eraseKey (t : Table α β) (i : USize) (hs : smallMask t.mask = true)
    (hi : t.slots.IsFull i.toNat) {a : α} (hit : t.slots.Hit t.shift a i.toNat) [EquivBEq α]
    [LawfulHashable α] : (eraseAtU t i hs hi).slots.entries = eraseKey a t.slots.entries := by
  obtain ⟨ctrl, keys, vals, size, gl, mask, shift, req, wf⟩ := t
  unfold eraseAtU
  dsimp only
  rw [slots_mk, slots_mk]
  exact eraseU_entries wf hs hit

/-- Erasing the hit for `a` on `Nat` indices is `eraseKey`. -/
private theorem eraseAtN_eraseKey (t : Table α β) (i : Nat) (hi : t.slots.IsFull i) {a : α}
    (hit : t.slots.Hit t.shift a i) [EquivBEq α] [LawfulHashable α] :
    (eraseAtN t i hi).slots.entries = eraseKey a t.slots.entries := by
  obtain ⟨ctrl, keys, vals, size, gl, mask, shift, req, wf⟩ := t
  unfold eraseAtN
  dsimp only
  rw [slots_mk, slots_mk]
  exact wf.entries_eraseN_eraseKey hit (Prod.eta _).symm

/-- `modifyAtU` is `Const.modifyKey`, up to order (Std states `Const.modifyKey`
only up to order: its definition is not exposed). -/
private theorem modifyAtU_modifyKey (t : Table α β) (i : USize) (a : α) (f : β → β)
    (hs : smallMask t.mask = true) (hit : t.slots.Hit t.shift a i.toNat) [EquivBEq α]
    [LawfulHashable α] :
    (modifyAtU t i a f hs hit).slots.entries.Perm (Const.modifyKey a f t.slots.entries) := by
  obtain ⟨ctrl, keys, vals, size, gl, mask, shift, req, wf⟩ := t
  unfold modifyAtU
  dsimp only
  rw [slots_mk, slots_mk, uset_uset, Array.uset_eq_set, Array.uset_eq_set,
    wf.entries_kvN_replace hit]
  exact (modifyKey_of_hit wf hit (Array.getElem?_eq_getElem _)).symm

/-- `modifyAtN` is `Const.modifyKey`, up to order. -/
private theorem modifyAtN_modifyKey (t : Table α β) (i : Nat) (a : α) (f : β → β)
    (hit : t.slots.Hit t.shift a i) [EquivBEq α] [LawfulHashable α] :
    (modifyAtN t i a f hit).slots.entries.Perm (Const.modifyKey a f t.slots.entries) := by
  obtain ⟨ctrl, keys, vals, size, gl, mask, shift, req, wf⟩ := t
  unfold modifyAtN
  dsimp only
  rw [slots_mk, slots_mk, Array.set_set, wf.entries_kvN_replace hit]
  exact (modifyKey_of_hit wf hit (Array.getElem?_eq_getElem _)).symm

/-! ### A new key as the list operations -/

private theorem newU_insertEntry (t : Table α β) (a : α) (b : β) (q : UInt64) (i : USize)
    (hs : smallMask t.mask = true) (h : NewSlot t.slots t.shift a q i.toNat) [EquivBEq α]
    [LawfulHashable α] :
    (insertNewU t a b q i hs h).slots.entries.Perm (insertEntry a b t.slots.entries) := by
  rw [insertEntry_of_containsKey_eq_false (containsKey_absent h.absent)]
  exact insertNewU_perm t a b q i hs h

private theorem newN_insertEntry (t : Table α β) (a : α) (b : β) (q : UInt64) (i : Nat)
    (h : NewSlot t.slots t.shift a q i) [EquivBEq α] [LawfulHashable α] :
    (insertNewN t a b q i h).slots.entries.Perm (insertEntry a b t.slots.entries) := by
  rw [insertEntry_of_containsKey_eq_false (containsKey_absent h.absent)]
  exact insertNewN_perm t a b q i h

private theorem newU_insertEntryIfNew (t : Table α β) (a : α) (b : β) (q : UInt64) (i : USize)
    (hs : smallMask t.mask = true) (h : NewSlot t.slots t.shift a q i.toNat) [EquivBEq α]
    [LawfulHashable α] :
    (insertNewU t a b q i hs h).slots.entries.Perm (insertEntryIfNew a b t.slots.entries) := by
  rw [insertEntryIfNew_of_containsKey_eq_false (containsKey_absent h.absent)]
  exact insertNewU_perm t a b q i hs h

private theorem newN_insertEntryIfNew (t : Table α β) (a : α) (b : β) (q : UInt64) (i : Nat)
    (h : NewSlot t.slots t.shift a q i) [EquivBEq α] [LawfulHashable α] :
    (insertNewN t a b q i h).slots.entries.Perm (insertEntryIfNew a b t.slots.entries) := by
  rw [insertEntryIfNew_of_containsKey_eq_false (containsKey_absent h.absent)]
  exact insertNewN_perm t a b q i h

private theorem newU_alterKey (t : Table α β) (a : α) (v' : β) (q : UInt64) (i : USize)
    (hs : smallMask t.mask = true) (h : NewSlot t.slots t.shift a q i.toNat)
    {f : Option β → Option β} (hf : f none = some v') [EquivBEq α] [LawfulHashable α] :
    (insertNewU t a v' q i hs h).slots.entries.Perm (Const.alterKey a f t.slots.entries) :=
  (newU_insertEntry t a v' q i hs h).trans
    (alterKey_perm_some (getValue?_absent h.absent) hf).symm

private theorem newN_alterKey (t : Table α β) (a : α) (v' : β) (q : UInt64) (i : Nat)
    (h : NewSlot t.slots t.shift a q i) {f : Option β → Option β} (hf : f none = some v')
    [EquivBEq α] [LawfulHashable α] :
    (insertNewN t a v' q i h).slots.entries.Perm (Const.alterKey a f t.slots.entries) :=
  (newN_insertEntry t a v' q i h).trans
    (alterKey_perm_some (getValue?_absent h.absent) hf).symm

/-- `Const.alterKey` of an absent key mapped to `none`. -/
private theorem absent_alterKey {s : Slots α β} {a : α} (habs : s.Absent a)
    {f : Option β → Option β} (hf : f none = none) :
    s.entries.Perm (Const.alterKey a f s.entries) :=
  ((alterKey_perm_none (getValue?_absent habs) hf).trans
    (List.Perm.of_eq (eraseKey_of_containsKey_eq_false (containsKey_absent habs)))).symm

end Writes

end Swiss

namespace Table

open Swiss

variable {α : Type u} {β : Type v} {γ : Type w} {_ : BEq α} {_ : Hashable α}

theorem toListModel_insert [EquivBEq α] [LawfulHashable α] (t : Table α β) (a : α) (b : β) :
    (t.insert a b).toListModel.Perm (insertEntry a b t.toListModel) := by
  rw [insert_def, toListModel_def, toListModel_def]
  obtain ⟨ctrl, keys, vals, size, gl, mask, shift, req, wf⟩ := t
  unfold containsThenInsertImpl
  dsimp only
  split
  · rename_i hsm
    split
    · rename_i hmt
      split
      · rename_i hg
        exact newU_insertEntry _ a b _ _ hsm _
      · split
        · rename_i hg hr
          rw [slots_mk, slots_mk]
          exact kvU_insertEntry wf (wf.insProbeU_hit (wf.loopU' hsm) hr) b
        · exact newU_insertEntry _ a b _ _ hsm _
    · split
      · rename_i hmt hr
        rw [slots_mk, slots_mk]
        exact kvU_insertEntry wf (wf.insProbeU_hit (wf.loopU' hsm) hr) b
      · exact newU_insertEntry _ a b _ _ hsm _
  · rename_i hsm
    unfold containsThenInsertN
    dsimp only
    split
    · rename_i i he
      rw [slots_mk, slots_mk]
      exact kvN_insertEntry wf (wf.insSlotN_hit (wf.arrN' hsm) he) b
    · exact newN_insertEntry _ a b _ _ _

theorem toListModel_insertIfNew [EquivBEq α] [LawfulHashable α] (t : Table α β) (a : α)
    (b : β) : (t.insertIfNew a b).toListModel.Perm (insertEntryIfNew a b t.toListModel) := by
  rw [insertIfNew_def, toListModel_def, toListModel_def]
  obtain ⟨ctrl, keys, vals, size, gl, mask, shift, req, wf⟩ := t
  unfold getThenInsertIfNewImpl
  dsimp only
  split
  · rename_i hss
    split
    · rename_i hr
      rw [slots_mk, insertEntryIfNew_of_containsKey
        (containsKey_hit wf (wf.insProbeU_hit (wf.loopU hss) hr))]
    · exact newU_insertEntryIfNew _ a b _ _ _ _
  · rename_i hss
    unfold getThenInsertIfNewN
    dsimp only
    split
    · rename_i i he
      rw [slots_mk, insertEntryIfNew_of_containsKey
        (containsKey_hit wf (wf.insProbeN_hit (wf.arrN hss) he))]
    · exact newN_insertEntryIfNew _ a b _ _ _

theorem toListModel_erase [EquivBEq α] [LawfulHashable α] (t : Table α β) (a : α) :
    (t.erase a).toListModel.Perm (eraseKey a t.toListModel) := by
  rw [erase_def, toListModel_def, toListModel_def]
  unfold eraseImpl
  dsimp only
  split
  · rename_i hs
    split
    · rename_i hi
      exact List.Perm.of_eq (eraseAtU_eraseKey t _ _ _ (t.wf.findU_hit (t.wf.loopU hs) hi))
    · rename_i hi
      exact (List.Perm.of_eq (eraseKey_of_containsKey_eq_false
        (containsKey_absent (s := t.slots) (t.wf.findU_absent (t.wf.loopU hs) hi)))).symm
  · rename_i hs
    unfold eraseN
    split
    · rename_i i he
      exact List.Perm.of_eq (eraseAtN_eraseKey t i _ (t.wf.findN_hit (t.wf.arrN hs) he))
    · rename_i he
      exact (List.Perm.of_eq (eraseKey_of_containsKey_eq_false
        (containsKey_absent (s := t.slots) (t.wf.findN_absent (t.wf.arrN hs) he)))).symm

theorem toListModel_alter [EquivBEq α] [LawfulHashable α] (t : Table α β) (a : α)
    (f : Option β → Option β) :
    (t.alter a f).toListModel.Perm (Const.alterKey a f t.toListModel) := by
  rw [alter_def, toListModel_def, toListModel_def]
  obtain ⟨ctrl, keys, vals, size, gl, mask, shift, req, wf⟩ := t
  unfold alterImpl
  dsimp only
  split
  · rename_i hsm
    split
    · rename_i hr
      have hit := wf.insProbeU_hit (wf.loopU' hsm) hr
      have hv := getValue?_hit wf hit (Array.getElem?_eq_getElem (wf.vals_lt hit.1.1))
      split
      · rename_i v' hf
        rw [slots_mk, slots_mk, uset_uset]
        exact (kvU_insertEntry wf hit v').trans (alterKey_perm_some hv hf).symm
      · rename_i hf
        unfold eraseAtU
        dsimp only
        rw [slots_mk, slots_mk, uset_uset, eraseU_entries wf hsm hit]
        exact (alterKey_perm_none hv hf).symm
    · rename_i hr
      split
      · rename_i v' hf
        exact newU_alterKey _ a v' _ _ hsm _ hf
      · rename_i hf
        rw [slots_mk]
        exact absent_alterKey (wf.insProbeU_new (wf.loopU' hsm) hr).absent hf
  · rename_i hsm
    unfold alterN
    dsimp only
    split
    · rename_i i he
      have hit := wf.insProbeN_hit (wf.arrN' hsm) he
      have hv := getValue?_hit wf hit (Array.getElem?_eq_getElem (wf.vals_lt hit.1.1))
      split
      · rename_i v' hf
        rw [slots_mk, slots_mk, Array.set_set]
        exact (kvN_insertEntry wf hit v').trans (alterKey_perm_some hv hf).symm
      · rename_i hf
        unfold eraseAtN
        dsimp only
        rw [slots_mk, slots_mk, Array.set_set]
        exact (List.Perm.of_eq (wf.entries_eraseN_eraseKey hit (Prod.eta _).symm)).trans
          (alterKey_perm_none hv hf).symm
    · rename_i j he
      split
      · rename_i v' hf
        exact newN_alterKey _ a v' _ _ _ hf
      · rename_i hf
        rw [slots_mk]
        exact absent_alterKey (wf.insProbeN_new (wf.arrN' hsm) he).absent hf

theorem toListModel_modify [EquivBEq α] [LawfulHashable α] (t : Table α β) (a : α)
    (f : β → β) : (t.modify a f).toListModel.Perm (Const.modifyKey a f t.toListModel) := by
  rw [modify_def, toListModel_def, toListModel_def]
  unfold modifyImpl
  dsimp only
  split
  · rename_i hs
    split
    · rename_i hi
      exact modifyAtU_modifyKey t _ a f _ (t.wf.findU_hit (t.wf.loopU hs) hi)
    · rename_i hi
      exact (modifyKey_absent (t.wf.findU_absent (t.wf.loopU hs) hi)).symm
  · rename_i hs
    unfold modifyN
    split
    · rename_i i he
      exact modifyAtN_modifyKey t i a f (t.wf.findN_hit (t.wf.arrN hs) he)
    · rename_i he
      exact (modifyKey_absent (t.wf.findN_absent (t.wf.arrN hs) he)).symm

end Table

end SwissTable.Core
