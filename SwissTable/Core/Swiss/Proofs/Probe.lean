module

public import SwissTable.Core.Swiss.Loops

/-!
# Swiss core proofs, part 2: the probe lemmas

A proof file of the Swiss core (`SwissTable/Core/Swiss/Table.lean`, "Proof structure"). What a
probe returns, in a well-formed table:

* **Lookup** (`findU`, `findN`): a hit (`Slots.Hit`: a full slot with the tag of `a` and a key
  `== a`), or, for lawful instances, a proof that no stored key is `== a` (`Slots.Absent`).
* **Insertion** (`insProbeU`, `insProbeN`, `insSlotN` with fast path C, and the fast path of
  `containsThenInsert` on machine words, `WF.fast_new`): a hit, or a `NewSlot` for `a`: a free
  slot that the probe of `a` reaches (or slot `0` of the unallocated table), with `a` absent for
  lawful instances. A free slot exists because `size < cap` (the load bound `WF.room`).
* **The fused operations' U facts** (`Proofs/Query.lean`): the insertion probe hits exactly where
  the lookup probe does (`insProbeN_inl_iff`, `insSlotN_inl_iff`, `WF.insProbeU_le_iff`,
  `insProbeU_eq_findU`), and fast path C applies only where the lookup misses (`fast_findU`). No
  lawfulness.

The probe invariant (`Slots.ProbeInv`) and `Distinct` are what make a miss an absence: the slot
`i` of a stored key `k == a` lies in group `k'` of the probe from the home slot of `a` (the same
as that of `k`, by `LawfulHashable`), no group before `k'` has an EMPTY slot, so the probe reaches
group `k'`, where slot `i` carries the tag of `a` (`TagInv`) and is compared. A probe that visits
all `cap / 8` groups visits every slot (`probe_cover`, `probe_unique`).

The proofs go in three steps.

1. The loops on `Nat` indices, by functional induction, with their invariant at group `k` of the
   probe from `p₀` (`pos = probePos cap p₀ k`, `stride = 8 * k`, every tag match of the earlier
   groups and of the compared lanes compared and not `== a`, no EMPTY slot in the earlier
   groups): `findLoopN_spec` (a hit, or every reachable slot with the tag of `a` compared) and
   `findInsLoopN_free` (the first free slot passed, which exists by the load bound);
   `findInsLoopN_getLeft` says that the insertion probe hits exactly where the lookup does.
2. The machine-word loops are the `Nat` ones (`findLoop_toNat`, `findInsLoop_toNat`; `InsRel`: a
   miss at `ins + (mask + 1)` with `ins ≤ cap`), through `Geom` and `ctrlWord_eq_ctrlWordN`, and so
   are the probes from the home slot (`findU_toNat`, `insProbeU_toNat`). The unallocated table,
   which has no slot, is the separate case of `firstGroup`.
3. The lemmas of a well-formed table follow (`WF.findN_hit`, `WF.findN_absent`,
   `WF.insProbeN_new`, then the machine-word ones, `WF.findU_hit`, ...).
-/

@[expose] public section

universe u v w

namespace SwissTable.Core.Swiss

variable {α : Type u} {β : Type v}

/-! ## Proof helpers: the `Nat` loops -/

section NatLoops

variable [BEq α] {ctrl : ByteArray} {keys : Array α} {a : α} {cap : Nat}

/-- The key in cell `x` (if any) is not `== a`. -/
private def Miss (keys : Array α) (a : α) (x : Nat) : Prop :=
  ∀ kk, keys[x]? = some kk → (kk == a) = false

/-- No group before group `k` of the probe from `p₀` has an EMPTY slot. -/
private def NoEmpty (ctrl : ByteArray) (cap p₀ k : Nat) : Prop :=
  ∀ k' < k, ∀ j < 8, ctrl[(probePos cap p₀ k' + j) % cap]! ≠ EMPTY

/-- Every slot carrying `t` in the groups before group `k` holds no key `== a`. -/
private def Done (ctrl : ByteArray) (keys : Array α) (a : α) (cap p₀ : Nat) (t : UInt8) (k : Nat) :
    Prop :=
  ∀ k' < k, ∀ j < 8, ctrl[(probePos cap p₀ k' + j) % cap]! = t →
    Miss keys a ((probePos cap p₀ k' + j) % cap)

/-- What a lookup probe returns: a hit, or a miss after every reachable slot carrying `t`. -/
private def FindPost (ctrl : ByteArray) (keys : Array α) (a : α) (cap p₀ : Nat) (t : UInt8) :
    Option Nat → Prop
  | some i => i < cap ∧ ctrl[i]! = t ∧ ∃ kk, keys[i]? = some kk ∧ (kk == a) = true
  | none => ∀ K < cap / 8, ∀ J < 8, NoEmpty ctrl cap p₀ K →
      ctrl[(probePos cap p₀ K + J) % cap]! = t → Miss keys a ((probePos cap p₀ K + J) % cap)

private theorem miss_of_not {x : Nat} (hx : x < keys.size) (h : ¬(keys[x] == a) = true) :
    Miss keys a x := by
  intro kk hk
  rw [getElem?_pos keys x hx] at hk
  cases hk
  simpa using h

/-- The lowest flag of a nonzero mask, in the `Nat` loops' form. -/
private theorem lowest_spec {m : UInt64} (hm : IsMask m) (h0 : m ≠ 0) :
    (lowestLane64 m).toNat < 8 ∧ flag m (lowestLane64 m).toNat = true := by
  have := lowestLane_spec hm h0
  rw [toNat_lowestLane_of_isMask hm] at this
  exact ⟨this.1, this.2.1⟩

private theorem flag_clearLowest' {m : UInt64} (hm : IsMask m) (h0 : m ≠ 0) (j : Nat) :
    flag (clearLowest m) j = (flag m j && j != (lowestLane64 m).toNat) := by
  rw [flag_clearLowest hm h0, toNat_lowestLane_of_isMask hm]

/-- A nonzero mask has a flag. -/
private theorem exists_flag {m : UInt64} (hm : IsMask m) (h0 : m ≠ 0) :
    ∃ j < 8, flag m j = true :=
  ⟨_, lowest_spec hm h0⟩

/-- A zero `matchEmpty` leaves no EMPTY byte. -/
private theorem ne_empty_of_matchEmpty {g : UInt64} (h : matchEmpty g = 0) {j : Nat} (hj : j < 8) :
    byte g j ≠ EMPTY := by
  intro he
  have := flag_matchEmpty g hj
  rw [h, flag_zero, he, EMPTY_eq] at this
  exact absurd this (by decide)

/-- The group word of the group at `pos` under the mirror: its bytes are the slots' bytes. -/
private theorem byte_wordN (hM : Mirrored ctrl cap) {pos : Nat} {hw : pos + 8 ≤ ctrl.size}
    {j : Nat} (hj : j < 8) : byte (ctrlWordN ctrl pos hw) j = ctrl[(pos + j) % cap]! := by
  rw [byte_ctrlWordN_of_mirrored hM hj, slotByte_def, Nat.mod_mod]

/-- **The lookup loop on `Nat` indices** (the core probe lemma). The invariant at group `k` of the
probe from `p₀`: `pos` and `stride` are those of group `k`, `g` is its group word, the lanes left
in `m` carry the tag `t`, every lane carrying `t` is still in `m` or compared and missed, and the
slots carrying `t` in the groups before `k` all missed (`Done`). Then the loop ends at a hit, or
with every slot carrying `t` that the probe reaches compared and missed: it stops only at a group
with an EMPTY slot (which no later group's `Reach` passes) or after `cap / 8` groups. -/
private theorem findLoopN_spec (hM : Mirrored ctrl cap) (hctrl : ∀ i < cap, IsCtrl ctrl[i]!)
    (hA : ArrN ctrl keys cap) {t : UInt8} {p₀ : Nat} (pos stride : Nat) (g m : UInt64)
    (hm : IsMask m) :
    ∀ k, pos = probePos cap p₀ k → stride = 8 * k → k < cap / 8 →
    (∀ j < 8, byte g j = ctrl[(pos + j) % cap]!) →
    (∀ j < 8, flag m j = true → ctrl[(pos + j) % cap]! = t) →
    (∀ j < 8, ctrl[(pos + j) % cap]! = t → flag m j = true ∨ Miss keys a ((pos + j) % cap)) →
    Done ctrl keys a cap p₀ t k →
    FindPost ctrl keys a cap p₀ t (findLoopN ctrl keys a cap (repTag t) pos stride g m hA hm) := by
  have hc0 := hA.pos
  have h8 : cap % 8 = 0 := by
    obtain ⟨n, hn⟩ := hM.pow_two
    have := (cap_facts hn hM.le_cap).1
    omega
  fun_induction findLoopN ctrl keys a cap (repTag t) pos stride g m hA hm with
  | case1 pos stride g m hm h i hk =>
    intro k hpos hstr hk8 hg htag hcov hdone
    obtain ⟨hl8, hfl⟩ := lowest_spec hm (ne_zero_of_bne h)
    refine ⟨Nat.mod_lt _ hc0, htag _ hl8 hfl, keys[i]'(hA.mod_keys _), getElem?_pos _ _ _, hk⟩
  | case2 pos stride g m hm h i hk ih =>
    intro k hpos hstr hk8 hg htag hcov hdone
    have h0 := ne_zero_of_bne h
    refine ih k hpos hstr hk8 hg (fun j hj hf => ?_) (fun j hj ht => ?_) hdone
    · rw [flag_clearLowest' hm h0, Bool.and_eq_true] at hf
      exact htag j hj hf.1
    · rcases hcov j hj ht with hf | hmiss
      · by_cases hjl : j = (lowestLane64 m).toNat
        · subst hjl
          exact Or.inr (miss_of_not (hA.mod_keys _) hk)
        · left
          rw [flag_clearLowest' hm h0, hf]
          simpa using hjl
      · exact Or.inr hmiss
  | case3 pos stride g m hm h he =>
    intro k hpos hstr hk8 hg htag hcov hdone
    have hm0 := eq_zero_of_not_bne h
    obtain ⟨j0, hj0, hf0⟩ := exists_flag (isMask_matchEmpty g) (ne_zero_of_bne he)
    have hE : ctrl[(pos + j0) % cap]! = EMPTY := by
      rw [flag_matchEmpty g hj0, decide_eq_true_iff, hg j0 hj0] at hf0
      exact (isCtrl_le_iff (hctrl _ (Nat.mod_lt _ hc0))).mp hf0
    intro K hK J hJ hne ht
    rcases Nat.lt_trichotomy K k with hlt | rfl | hgt
    · exact hdone K hlt J hJ ht
    · subst hpos
      rcases hcov J hJ ht with hf | hmiss
      · rw [hm0, flag_zero] at hf; cases hf
      · exact hmiss
    · subst hpos
      exact absurd hE (hne k hgt j0 hj0)
  | case4 pos stride g m hm h he stride' hle =>
    intro k hpos hstr hk8 hg htag hcov hdone
    have hm0 := eq_zero_of_not_bne h
    intro K hK J hJ hne ht
    have hKk : K ≤ k := by
      simp only [stride'] at hle
      omega
    rcases Nat.lt_or_eq_of_le hKk with hlt | rfl
    · exact hdone K hlt J hJ ht
    · subst hpos
      rcases hcov J hJ ht with hf | hmiss
      · rw [hm0, flag_zero] at hf; cases hf
      · exact hmiss
  | case5 pos stride g m hm h he stride' hle pos' g' ih =>
    intro k hpos hstr hk8 hg htag hcov hdone
    have hm0 := eq_zero_of_not_bne h
    have hpos' : pos' = probePos cap p₀ (k + 1) := by
      simp only [pos', stride']
      rw [probePos_succ, hpos, hstr]
      congr 1
    have hp' : pos' < cap := Nat.mod_lt _ hc0
    have hg' : ∀ j < 8, byte g' j = ctrl[(pos' + j) % cap]! := fun j hj => byte_wordN hM hj
    refine ih (k + 1) hpos' (by simp only [stride']; omega) (by simp only [stride'] at hle; omega)
      hg' (fun j hj hf => ?_) (fun j hj ht => ?_) (fun k' hk' j hj ht => ?_)
    · rw [flag_matchTag g' t hj, beq_iff_eq, hg' j hj] at hf
      exact hf
    · left
      rw [flag_matchTag g' t hj, beq_iff_eq, hg' j hj]
      exact ht
    · rcases Nat.lt_or_eq_of_le (Nat.le_of_lt_succ hk') with hlt | rfl
      · exact hdone k' hlt j hj ht
      · rw [← hpos] at ht ⊢
        rcases hcov j hj ht with hf | hmiss
        · rw [hm0, flag_zero] at hf; cases hf
        · exact hmiss

private theorem findLoopN_congr {rep : UInt64} {hA : ArrN ctrl keys cap}
    {pos pos' stride stride' : Nat} {g g' m m' : UInt64} {hm : IsMask m} {hm' : IsMask m'}
    (h1 : pos = pos') (h2 : stride = stride') (h3 : g = g') (h4 : m = m') :
    findLoopN ctrl keys a cap rep pos stride g m hA hm =
      findLoopN ctrl keys a cap rep pos' stride' g' m' hA hm' := by
  subst h1 h2 h3 h4; rfl

/-- The insertion probe hits exactly where the lookup does. -/
private theorem findInsLoopN_getLeft (hA : ArrN ctrl keys cap) (rep : UInt64) (pos stride : Nat)
    (g m : UInt64) (ins : Nat) (hm : IsMask m) :
    (findInsLoopN ctrl keys a cap rep pos stride g m ins hA hm).getLeft? =
      findLoopN ctrl keys a cap rep pos stride g m hA hm := by
  fun_induction findInsLoopN ctrl keys a cap rep pos stride g m ins hA hm with
  | case1 pos stride g m ins hm h i hk =>
    rw [findLoopN, dite_eq_left h]; simp only [i] at hk; simp [hk]; rfl
  | case2 pos stride g m ins hm h i hk ih =>
    rw [findLoopN, dite_eq_left h]; simp only [i] at hk; simp [hk, ih]
  | case3 pos stride g m ins hm h ins' he =>
    rw [findLoopN, dite_eq_right h, ite_eq_left he]; rfl
  | case4 pos stride g m ins hm h ins' he stride' hle =>
    rw [findLoopN, dite_eq_right h, ite_eq_right he, dite_eq_left hle]; rfl
  | case5 pos stride g m ins hm h ins' he stride' hle pos' g' ih =>
    rw [findLoopN, dite_eq_right h, ite_eq_right he, dite_eq_right hle, ih]

/-- Slot `j` is free and reached by the probe from `p₀`. -/
private def FreeRaw (ctrl : ByteArray) (cap p₀ j : Nat) : Prop :=
  j < cap ∧ (ctrl[j]! = EMPTY ∨ ctrl[j]! = DELETED) ∧
    ∃ K < cap / 8, ∃ J < 8, (probePos cap p₀ K + J) % cap = j ∧ NoEmpty ctrl cap p₀ K

/-- Every slot of the groups before group `k` of the probe from `p₀` is full. -/
private def NoFree (ctrl : ByteArray) (cap p₀ k : Nat) : Prop :=
  ∀ k' < k, ∀ j < 8, ctrl[(probePos cap p₀ k' + j) % cap]! < 0x80

private theorem le_C0 {b : UInt8} (h : 0xC0 ≤ b) : 0x80 ≤ b := by
  rw [UInt8.le_iff_toNat_le] at h ⊢; simp at h ⊢; omega

/-- A group with an EMPTY byte has a free byte. -/
private theorem matchFree_ne_of_matchEmpty {g : UInt64} (h : matchEmpty g ≠ 0) :
    matchFree g ≠ 0 := by
  obtain ⟨j, hj, hf⟩ := exists_flag (isMask_matchEmpty g) h
  rw [flag_matchEmpty g hj, decide_eq_true_iff] at hf
  intro h0
  have := flag_matchFree g hj
  rw [h0, flag_zero] at this
  exact absurd (le_C0 hf) (by simpa using this)

/-- The update of the first free slot at a group: unchanged, or the lowest free lane. -/
private theorem insUpd_cases {pos ins ins' : Nat} {g : UInt64}
    (h : ins' = if cap ≤ ins then
        (if (matchFree g != 0) = true then (pos + (lowestLane64 (matchFree g)).toNat) % cap
          else ins)
      else ins) :
    (cap ≤ ins ∧ matchFree g ≠ 0 ∧ ins' = (pos + (lowestLane64 (matchFree g)).toNat) % cap) ∨
      (cap ≤ ins ∧ matchFree g = 0 ∧ ins' = ins) ∨ (ins < cap ∧ ins' = ins) := by
  subst h
  by_cases h1 : cap ≤ ins
  · by_cases h2 : matchFree g = 0
    · right; left; simp [h1, h2]
    · left; simp [h1, h2]
  · right; right; simp [h1]; omega

/-- **The free slot of the insertion probe.** The invariant at group `k`: `ins` is a free slot
that the probe reaches (`FreeRaw`), or `ins ≥ cap` and every slot of the groups before `k` is
full. A probe that ends at a group with an EMPTY slot has passed a free one; a probe that runs
through all `cap / 8` groups has seen every slot (`probe_cover`), and some slot is not full
(`hfree`, from the load bound). -/
private theorem findInsLoopN_free (hM : Mirrored ctrl cap) (hctrl : ∀ i < cap, IsCtrl ctrl[i]!)
    (hfree : ∃ i < cap, ¬ctrl[i]! < 0x80) (hA : ArrN ctrl keys cap) {p₀ : Nat} (rep : UInt64)
    (pos stride : Nat) (g m : UInt64) (ins : Nat) (hm : IsMask m) :
    ∀ k, pos = probePos cap p₀ k → stride = 8 * k → k < cap / 8 →
    (∀ j < 8, byte g j = ctrl[(pos + j) % cap]!) → NoEmpty ctrl cap p₀ k →
    (ins < cap → FreeRaw ctrl cap p₀ ins) → (cap ≤ ins → NoFree ctrl cap p₀ k) →
    ∀ j, findInsLoopN ctrl keys a cap rep pos stride g m ins hA hm = .inr j →
      FreeRaw ctrl cap p₀ j := by
  have hc0 := hA.pos
  have h8 : cap % 8 = 0 := by
    obtain ⟨n, hn⟩ := hM.pow_two
    have := (cap_facts hn hM.le_cap).1
    omega
  -- the slot found in group `k`, when its free mask is nonzero
  have found : ∀ (pos : Nat) (g : UInt64) (k : Nat), pos = probePos cap p₀ k → k < cap / 8 →
      (∀ j < 8, byte g j = ctrl[(pos + j) % cap]!) → NoEmpty ctrl cap p₀ k → matchFree g ≠ 0 →
      FreeRaw ctrl cap p₀ ((pos + (lowestLane64 (matchFree g)).toNat) % cap) := by
    intro pos g k hpos hk8 hg hne hf0
    obtain ⟨hl8, hfl⟩ := lowest_spec (isMask_matchFree g) hf0
    rw [flag_matchFree g hl8, decide_eq_true_iff, hg _ hl8] at hfl
    refine ⟨Nat.mod_lt _ hc0, (isCtrl_free_iff (hctrl _ (Nat.mod_lt _ hc0))).mp hfl, k, hk8, _,
      hl8, by rw [hpos], hne⟩
  -- a group with no free slot
  have full : ∀ (pos : Nat) (g : UInt64), (∀ j < 8, byte g j = ctrl[(pos + j) % cap]!) →
      matchFree g = 0 → ∀ j < 8, ctrl[(pos + j) % cap]! < 0x80 := by
    intro pos g hg hf0 j hj
    have := flag_matchFree g hj
    rw [hf0, flag_zero, hg j hj] at this
    exact UInt8.not_le.mp (by simpa using this)
  fun_induction findInsLoopN ctrl keys a cap rep pos stride g m ins hA hm with
  | case1 pos stride g m ins hm h i hk =>
    intro k _ _ _ _ _ _ _ j hj; cases hj
  | case2 pos stride g m ins hm h i hk ih => exact ih
  | case3 pos stride g m ins hm h ins' he =>
    intro k hpos hstr hk8 hg hne hlt hge j hj
    cases hj
    rcases insUpd_cases (cap := cap) (pos := pos) (ins := ins) (ins' := ins') (g := g) rfl with
      ⟨h1, h2, h3⟩ | ⟨h1, h2, h3⟩ | ⟨h1, h3⟩
    · rw [h3]; exact found pos g k hpos hk8 hg hne h2
    · exact absurd h2 (matchFree_ne_of_matchEmpty (ne_zero_of_bne he))
    · rw [h3]; exact hlt h1
  | case4 pos stride g m ins hm h ins' he stride' hle =>
    intro k hpos hstr hk8 hg hne hlt hge j hj
    cases hj
    rcases insUpd_cases (cap := cap) (pos := pos) (ins := ins) (ins' := ins') (g := g) rfl with
      ⟨h1, h2, h3⟩ | ⟨h1, h2, h3⟩ | ⟨h1, h3⟩
    · rw [h3]; exact found pos g k hpos hk8 hg hne h2
    · exfalso
      obtain ⟨i0, hi0, hnf⟩ := hfree
      obtain ⟨n, hn⟩ := hM.pow_two
      obtain ⟨K, hK, J, hJ, hKJ⟩ := probe_cover p₀ hn hM.le_cap hi0
      have hKk : K ≤ k := by simp only [stride'] at hle; omega
      rcases Nat.lt_or_eq_of_le hKk with hlt' | rfl
      · exact hnf (hKJ ▸ hge h1 K hlt' J hJ)
      · subst hpos
        exact hnf (hKJ ▸ full _ g hg h2 J hJ)
    · rw [h3]; exact hlt h1
  | case5 pos stride g m ins hm h ins' he stride' hle pos' g' ih =>
    intro k hpos hstr hk8 hg hne hlt hge
    have hpos' : pos' = probePos cap p₀ (k + 1) := by
      simp only [pos', stride']
      rw [probePos_succ, hpos, hstr]
      congr 1
    have hp' : pos' < cap := Nat.mod_lt _ hc0
    have hne' : NoEmpty ctrl cap p₀ (k + 1) := by
      intro k' hk' j hj
      rcases Nat.lt_or_eq_of_le (Nat.le_of_lt_succ hk') with hlt' | rfl
      · exact hne k' hlt' j hj
      · rw [← hpos, ← hg j hj]
        exact ne_empty_of_matchEmpty (by simpa using he) hj
    refine ih (k + 1) hpos' (by simp only [stride']; omega) (by simp only [stride'] at hle; omega)
      (fun j hj => byte_wordN hM hj) hne' (fun hlt' => ?_) (fun hge' => ?_)
    · rcases insUpd_cases (cap := cap) (pos := pos) (ins := ins) (ins' := ins') (g := g) rfl with
        ⟨h1, h2, h3⟩ | ⟨h1, h2, h3⟩ | ⟨h1, h3⟩
      · rw [h3]; exact found pos g k hpos hk8 hg hne h2
      · omega
      · rw [h3]; exact hlt h1
    · rcases insUpd_cases (cap := cap) (pos := pos) (ins := ins) (ins' := ins') (g := g) rfl with
        ⟨h1, h2, h3⟩ | ⟨h1, h2, h3⟩ | ⟨h1, h3⟩
      · rw [h3] at hge'; exact absurd hge' (Nat.not_le.mpr (Nat.mod_lt _ hc0))
      · intro k' hk' j hj
        rcases Nat.lt_or_eq_of_le (Nat.le_of_lt_succ hk') with hlt' | rfl
        · exact hge h1 k' hlt' j hj
        · rw [← hpos]; exact full pos g hg h2 j hj
      · omega

omit [BEq α] in
/-- The state of a probe at its home group. -/
private theorem start_pos [Hashable α] (shift : UInt64) (a : α) :
    homeN (hashBits shift a) cap = probePos cap (homeN (hashBits shift a) cap) 0 := by
  rw [probePos_zero]; simp [homeN]

/-- **The lookup probe from the home group.** -/
private theorem findN_post [Hashable α] (hM : Mirrored ctrl cap)
    (hctrl : ∀ i < cap, IsCtrl ctrl[i]!) (hA : ArrN ctrl keys cap) (shift : UInt64) (a : α) :
    FindPost ctrl keys a cap (homeN (hashBits shift a) cap) (tagOf (hashBits shift a))
      (findN ctrl keys cap shift a hA) := by
  have hc0 := hA.pos
  have hp : homeN (hashBits shift a) cap < cap := Nat.mod_lt _ hc0
  have hg : ∀ j < 8, byte (ctrlWordN ctrl (homeN (hashBits shift a) cap) (hA.mod_word _)) j =
      ctrl[(homeN (hashBits shift a) cap + j) % cap]! := fun j hj => byte_wordN hM hj
  refine findLoopN_spec hM hctrl hA _ _ _ _ _ 0 (start_pos shift a) rfl
    (by have := hM.le_cap; omega) hg (fun j hj hf => ?_) (fun j hj ht => ?_)
    (fun k' hk' => absurd hk' (Nat.not_lt_zero _))
  · rw [flag_matchTag _ _ hj, beq_iff_eq, hg j hj] at hf; exact hf
  · left; rw [flag_matchTag _ _ hj, beq_iff_eq, hg j hj]; exact ht

private theorem insProbeN_getLeft [Hashable α] (hA : ArrN ctrl keys cap) (shift : UInt64) (a : α) :
    (insProbeN ctrl keys cap shift a hA).getLeft? = findN ctrl keys cap shift a hA :=
  findInsLoopN_getLeft hA _ _ _ _ _ _ _

/-- **The insertion probe from the home group** ends at a free slot that the probe reaches. -/
private theorem insProbeN_free [Hashable α] (hM : Mirrored ctrl cap)
    (hctrl : ∀ i < cap, IsCtrl ctrl[i]!) (hfree : ∃ i < cap, ¬ctrl[i]! < 0x80)
    (hA : ArrN ctrl keys cap) (shift : UInt64) (a : α) {j : Nat}
    (he : insProbeN ctrl keys cap shift a hA = .inr j) :
    FreeRaw ctrl cap (homeN (hashBits shift a) cap) j := by
  have hc0 := hA.pos
  have hp : homeN (hashBits shift a) cap < cap := Nat.mod_lt _ hc0
  exact findInsLoopN_free hM hctrl hfree hA _ _ _ _ _ _ _ 0 (start_pos shift a) rfl
    (by have := hM.le_cap; omega) (fun j hj => byte_wordN hM hj)
    (fun k' hk' => absurd hk' (Nat.not_lt_zero _)) (fun h => absurd h (Nat.lt_irrefl _))
    (fun _ k' hk' => absurd hk' (Nat.not_lt_zero _)) j he

/-- The lookup ends at once in a group with no candidate and an EMPTY byte. -/
private theorem findLoopN_first {rep : UInt64} {hA : ArrN ctrl keys cap} {pos stride : Nat}
    {g m : UInt64} {hm : IsMask m} (hm0 : m = 0) (he : matchEmpty g ≠ 0) :
    findLoopN ctrl keys a cap rep pos stride g m hA hm = none := by
  rw [findLoopN, dite_eq_right (by simp [hm0]), ite_eq_left (by simpa using he)]

/-- The low byte of a word is EMPTY. -/
private theorem byte_zero_of_low {g : UInt64} (hg : (g &&& 0xFF == 0xFF) = true) :
    byte g 0 = EMPTY := by
  rw [beq_iff_eq] at hg
  apply UInt8.toNat_inj.mp
  rw [toNat_byte g (by decide), Lane.lane_def, EMPTY_eq]
  have h1 := congrArg UInt64.toNat hg
  rw [UInt64.toNat_and] at h1
  have h2 : g.toNat &&& 2 ^ 8 - 1 = g.toNat % 2 ^ 8 := Nat.and_two_pow_sub_one_eq_mod _ _
  simp only [UInt64.reduceToNat, Nat.reducePow, Nat.reduceSub] at h1 h2
  simp only [Nat.pow_zero, Nat.div_one, UInt8.reduceToNat]
  omega

/-- A group whose low byte is EMPTY has an EMPTY byte. -/
private theorem matchEmpty_ne_of_low {g : UInt64} (hg : (g &&& 0xFF == 0xFF) = true) :
    matchEmpty g ≠ 0 := by
  intro h0
  have := flag_matchEmpty g (j := 0) (by decide)
  rw [h0, flag_zero, byte_zero_of_low hg, EMPTY_eq] at this
  exact absurd this (by decide)

end NatLoops

/-! ## Machine words: arithmetic below `2 ^ 31` -/

section WordFacts

private theorem not_succ_le {mask : USize} (hx : mask.toNat < 2 ^ 31) : ¬mask + 1 ≤ mask := by
  rw [USize.le_iff_toNat_le, toNat_add_one hx]; omega

private theorem smallMask_of_lt {mask : USize} (h : mask.toNat < 2 ^ 31) :
    smallMask mask = true := by
  unfold smallMask
  rw [beq_iff_eq]
  apply USize.toNat_inj.mp
  have h1 : (0x80000000 : USize).toNat = 2 ^ 31 := by simp
  rw [USize.toNat_and, h1, USize.toNat_zero]
  apply Nat.eq_of_testBit_eq
  intro i
  rw [Nat.testBit_and, Nat.testBit_two_pow, Nat.zero_testBit]
  by_cases hi : 31 = i
  · subst hi; rw [Nat.testBit_lt_two_pow h]; rfl
  · simp [hi]

end WordFacts

/-! ## Machine-word loops against the `Nat` loops -/

section WordLoops

variable [BEq α] {ctrl : ByteArray} {keys : Array α} {a : α} {cap : Nat} {mask : USize}

/-- The lookup ends at once in a group with no candidate and an EMPTY byte. -/
private theorem findLoop_first {rep : UInt64} {hA : ArrU ctrl mask} {pos stride : USize}
    {g m : UInt64} {hs : stride.toNat ≤ mask.toNat} {hm : IsMask m}
    {hk : mask.toNat < keys.size ∨ (m = 0 ∧ matchEmpty g ≠ 0)} (hm0 : m = 0)
    (he : matchEmpty g ≠ 0) :
    findLoop ctrl keys a mask rep pos stride g m hA hs hm hk = mask + 1 := by
  rw [findLoop, dite_eq_right (by simp [hm0]), dite_eq_left (by simpa using he)]

/-- **The machine-word lookup loop is the `Nat` one.** -/
private theorem findLoop_toNat (hg : Geom cap mask) (hAN : ArrN ctrl keys cap) (rep : UInt64)
    (hA : ArrU ctrl mask) (pos stride : USize) (g m : UInt64) (hs : stride.toNat ≤ mask.toNat)
    (hm : IsMask m) (hk : mask.toNat < keys.size ∨ (m = 0 ∧ matchEmpty g ≠ 0)) :
    pos.toNat < cap →
    (if findLoop ctrl keys a mask rep pos stride g m hA hs hm hk ≤ mask then
        some (findLoop ctrl keys a mask rep pos stride g m hA hs hm hk).toNat else none) =
      findLoopN ctrl keys a cap rep pos.toNat stride.toNat g m hAN hm := by
  have hsm := hA.small
  have hmc := hg.mask_add_one
  fun_induction findLoop ctrl keys a mask rep pos stride g m hA hs hm hk with
  | case1 pos stride g m hs hm hk h i heq =>
    intro _
    have hi : i.toNat = (pos.toNat + (lowestLane64 m).toNat) % cap := by
      simp only [i]; rw [hg.toNat_add_and_mask, toNat_lowestLane_of_isMask hm]
    have hle : i ≤ mask := by rw [USize.le_iff_toNat_le]; exact and_mask_le _ _
    rw [ite_eq_left hle, findLoopN, dite_eq_left h]
    simp only [Array.uget, hi] at heq
    simp [heq, hi]
  | case2 pos stride g m hs hm hk h i heq ih =>
    intro hp
    have hi : i.toNat = (pos.toNat + (lowestLane64 m).toNat) % cap := by
      simp only [i]; rw [hg.toNat_add_and_mask, toNat_lowestLane_of_isMask hm]
    rw [ih hp]
    conv => rhs; rw [findLoopN, dite_eq_left h]
    simp only [Array.uget, hi] at heq
    simp [heq]
  | case3 pos stride g m hs hm hk h he =>
    intro _
    rw [ite_eq_right (not_succ_le hsm)]
    conv => rhs; rw [findLoopN, dite_eq_right h, ite_eq_left he]
  | case4 pos stride g m hs hm hk h he stride' hgt =>
    intro _
    rw [ite_eq_right (not_succ_le hsm)]
    have hst : stride'.toNat = stride.toNat + 8 := toNat_add_eight (by omega)
    have hle : cap ≤ stride.toNat + 8 := by
      rw [GT.gt, USize.lt_iff_toNat_lt, hst] at hgt; omega
    conv => rhs; rw [findLoopN, dite_eq_right h, ite_eq_right he, dite_eq_left hle]
  | case5 pos stride g m hs hm hk h he stride' hgt pos' g' ih =>
    intro hp
    have hst : stride'.toNat = stride.toNat + 8 := toNat_add_eight (by omega)
    have hle : ¬cap ≤ stride.toNat + 8 := by
      have := le_of_not_gt' hgt; omega
    have hp' : pos'.toNat = (pos.toNat + (stride.toNat + 8)) % cap := by
      simp only [pos']; rw [hg.toNat_add_and_mask, hst]
    have hpc : pos'.toNat < cap := by rw [hp']; exact Nat.mod_lt _ (by omega)
    have hgw : g' = ctrlWordN ctrl pos'.toNat (hAN.word_of_lt hpc) :=
      ctrlWord_eq_ctrlWordN (by omega)
    rw [ih hpc]
    conv => rhs; rw [findLoopN, dite_eq_right h, ite_eq_right he, dite_eq_right hle]
    exact findLoopN_congr hp' hst (by rw [hgw]; exact ctrlWordN_congr hp')
      (by rw [hgw]; exact congrArg (fun x => matchTag x rep) (ctrlWordN_congr hp'))

/-- The first free slot after a group, on machine words (`findInsLoop`'s update of `ins`). -/
private def insUpdU (mask pos : USize) (g : UInt64) (ins : USize) : USize :=
  if ins > mask then
    (if (matchFree g != 0) = true then (pos + lowestLane (matchFree g)) &&& mask else ins)
  else ins

/-- The first free slot after a group, on `Nat` indices (`findInsLoopN`'s update of `ins`). -/
private def insUpdN (cap pos : Nat) (g : UInt64) (ins : Nat) : Nat :=
  if cap ≤ ins then
    (if (matchFree g != 0) = true then (pos + (lowestLane64 (matchFree g)).toNat) % cap else ins)
  else ins

omit [BEq α] in
private theorem insUpd_toNat (hg : Geom cap mask) {pos ins : USize} {g : UInt64}
    (hins : ins.toNat ≤ cap) :
    (insUpdU mask pos g ins).toNat = insUpdN cap pos.toNat g ins.toNat ∧
      (insUpdU mask pos g ins).toNat ≤ cap := by
  unfold insUpdU insUpdN
  have hmc := hg.mask_add_one
  by_cases h1 : ins > mask
  · have h1' : cap ≤ ins.toNat := by rw [GT.gt, USize.lt_iff_toNat_lt] at h1; omega
    rw [ite_eq_left h1, ite_eq_left h1']
    by_cases h2 : (matchFree g != 0) = true
    · rw [ite_eq_left h2, ite_eq_left h2, hg.toNat_add_and_mask,
        toNat_lowestLane_of_isMask (isMask_matchFree g)]
      exact ⟨rfl, Nat.le_of_lt (Nat.mod_lt _ (by omega))⟩
    · rw [ite_eq_right h2, ite_eq_right h2]; exact ⟨rfl, hins⟩
  · have h1' : ¬cap ≤ ins.toNat := by rw [GT.gt, USize.lt_iff_toNat_lt] at h1; omega
    rw [ite_eq_right h1, ite_eq_right h1']; exact ⟨rfl, hins⟩

private theorem findInsLoopN_zero {rep : UInt64} {hA : ArrN ctrl keys cap} {pos stride : Nat}
    {g m : UInt64} {ins : Nat} {hm : IsMask m} (h : ¬(m != 0) = true) :
    findInsLoopN ctrl keys a cap rep pos stride g m ins hA hm =
      if (matchEmpty g != 0) = true then .inr (insUpdN cap pos g ins)
      else if _hle : cap ≤ stride + 8 then .inr (insUpdN cap pos g ins)
      else findInsLoopN ctrl keys a cap rep ((pos + (stride + 8)) % cap) (stride + 8)
        (ctrlWordN ctrl ((pos + (stride + 8)) % cap) (hA.mod_word _))
        (matchTag (ctrlWordN ctrl ((pos + (stride + 8)) % cap) (hA.mod_word _)) rep)
        (insUpdN cap pos g ins) hA (isMask_matchTag _ _) := by
  rw [findInsLoopN, dite_eq_right h]; rfl

private theorem findInsLoopN_congr {rep : UInt64} {hA : ArrN ctrl keys cap}
    {pos pos' stride stride' ins ins' : Nat} {g g' m m' : UInt64} {hm : IsMask m}
    {hm' : IsMask m'} (h1 : pos = pos') (h2 : stride = stride') (h3 : g = g') (h4 : m = m')
    (h5 : ins = ins') :
    findInsLoopN ctrl keys a cap rep pos stride g m ins hA hm =
      findInsLoopN ctrl keys a cap rep pos' stride' g' m' ins' hA hm' := by
  subst h1 h2 h3 h4 h5; rfl

/-- How the result of a machine-word insertion probe encodes the `Nat` one. -/
private def InsRel (mask : USize) (cap : Nat) (r : USize) : Nat ⊕ Nat → Prop
  | .inl i => r ≤ mask ∧ r.toNat = i
  | .inr j => j ≤ cap ∧ ∃ u : USize, u.toNat = j ∧ r = u + (mask + 1)

/-- **The machine-word insertion probe loop is the `Nat` one.** -/
private theorem findInsLoop_toNat (hg : Geom cap mask) (hAN : ArrN ctrl keys cap) (rep : UInt64)
    (hA : ArrU ctrl mask) (pos stride : USize) (g m : UInt64) (ins : USize)
    (hs : stride.toNat ≤ mask.toNat) (hm : IsMask m)
    (hk : mask.toNat < keys.size ∨ (m = 0 ∧ matchEmpty g ≠ 0)) :
    pos.toNat < cap → ins.toNat ≤ cap →
    InsRel mask cap (findInsLoop ctrl keys a mask rep pos stride g m ins hA hs hm hk)
      (findInsLoopN ctrl keys a cap rep pos.toNat stride.toNat g m ins.toNat hAN hm) := by
  have hsm := hA.small
  have hmc := hg.mask_add_one
  fun_induction findInsLoop ctrl keys a mask rep pos stride g m ins hA hs hm hk with
  | case1 pos stride g m ins hs hm hk h i heq =>
    intro _ _
    have hi : i.toNat = (pos.toNat + (lowestLane64 m).toNat) % cap := by
      simp only [i]; rw [hg.toNat_add_and_mask, toNat_lowestLane_of_isMask hm]
    have hle : i ≤ mask := by rw [USize.le_iff_toNat_le]; exact and_mask_le _ _
    rw [findInsLoopN, dite_eq_left h]
    simp only [Array.uget, hi] at heq
    simp only [heq, ite_true]
    exact ⟨hle, hi⟩
  | case2 pos stride g m ins hs hm hk h i heq ih =>
    intro hp hins
    have hi : i.toNat = (pos.toNat + (lowestLane64 m).toNat) % cap := by
      simp only [i]; rw [hg.toNat_add_and_mask, toNat_lowestLane_of_isMask hm]
    rw [findInsLoopN, dite_eq_left h]
    simp only [Array.uget, hi] at heq
    simp only [heq, Bool.false_eq_true, ite_false]
    exact ih hp hins
  | case3 pos stride g m ins hs hm hk h ins' he =>
    intro _ hins
    have hI : ins'.toNat = insUpdN cap pos.toNat g ins.toNat ∧ ins'.toNat ≤ cap :=
      insUpd_toNat hg hins
    rw [findInsLoopN_zero h, ite_eq_left he]
    exact ⟨hI.1 ▸ hI.2, ins', hI.1, rfl⟩
  | case4 pos stride g m ins hs hm hk h ins' he stride' hgt =>
    intro _ hins
    have hI : ins'.toNat = insUpdN cap pos.toNat g ins.toNat ∧ ins'.toNat ≤ cap :=
      insUpd_toNat hg hins
    have hst : stride'.toNat = stride.toNat + 8 := toNat_add_eight (by omega)
    have hle : cap ≤ stride.toNat + 8 := by
      rw [GT.gt, USize.lt_iff_toNat_lt, hst] at hgt; omega
    rw [findInsLoopN_zero h, ite_eq_right he, dite_eq_left hle]
    exact ⟨hI.1 ▸ hI.2, ins', hI.1, rfl⟩
  | case5 pos stride g m ins hs hm hk h ins' he stride' hgt pos' g' ih =>
    intro hp hins
    have hI : ins'.toNat = insUpdN cap pos.toNat g ins.toNat ∧ ins'.toNat ≤ cap :=
      insUpd_toNat hg hins
    have hst : stride'.toNat = stride.toNat + 8 := toNat_add_eight (by omega)
    have hle : ¬cap ≤ stride.toNat + 8 := by
      have := le_of_not_gt' hgt; omega
    have hp' : pos'.toNat = (pos.toNat + (stride.toNat + 8)) % cap := by
      simp only [pos']; rw [hg.toNat_add_and_mask, hst]
    have hpc : pos'.toNat < cap := by rw [hp']; exact Nat.mod_lt _ (by omega)
    have hgw : g' = ctrlWordN ctrl pos'.toNat (hAN.word_of_lt hpc) :=
      ctrlWord_eq_ctrlWordN (by omega)
    rw [findInsLoopN_zero h, ite_eq_right he, dite_eq_right hle]
    have hgw' : g' = ctrlWordN ctrl ((pos.toNat + (stride.toNat + 8)) % cap) (hAN.mod_word _) :=
      hgw.trans (ctrlWordN_congr hp')
    have e := findInsLoopN_congr (ctrl := ctrl) (keys := keys) (a := a) (rep := rep) (hA := hAN)
      (hm := isMask_matchTag g' rep) (hm' := isMask_matchTag _ rep) hp' hst hgw'
      (congrArg (fun x => matchTag x rep) hgw') hI.1
    rw [← e]
    exact ih hpc hI.2

/-- The insertion probe hits exactly where the lookup does, on machine words: below
`2 ^ 31` slots `mask + 1` does not wrap, so a miss of the lookup is past the slots. -/
private theorem findInsLoop_eq_findLoop (rep : UInt64) (hA : ArrU ctrl mask) (pos stride : USize)
    (g m : UInt64) (hs : stride.toNat ≤ mask.toNat) (hm : IsMask m)
    (hk : mask.toNat < keys.size ∨ (m = 0 ∧ matchEmpty g ≠ 0)) :
    ∀ ins : USize, findLoop ctrl keys a mask rep pos stride g m hA hs hm hk ≤ mask →
      findInsLoop ctrl keys a mask rep pos stride g m ins hA hs hm hk =
        findLoop ctrl keys a mask rep pos stride g m hA hs hm hk := by
  have hsm := hA.small
  fun_induction findLoop ctrl keys a mask rep pos stride g m hA hs hm hk with
  | case1 pos stride g m hs hm hk h i heq =>
    intro ins _
    rw [findInsLoop, dite_eq_left h]
    simp only [i] at heq
    simp only [heq, ite_true]
    rfl
  | case2 pos stride g m hs hm hk h i heq ih =>
    intro ins hr
    rw [findInsLoop, dite_eq_left h]
    simp only [i] at heq
    simp only [heq, Bool.false_eq_true, ite_false]
    exact ih ins hr
  | case3 pos stride g m hs hm hk h he =>
    intro ins hr; exact absurd hr (not_succ_le hsm)
  | case4 pos stride g m hs hm hk h he stride' hgt =>
    intro ins hr; exact absurd hr (not_succ_le hsm)
  | case5 pos stride g m hs hm hk h he stride' hgt pos' g' ih =>
    intro ins hr
    rw [findInsLoop, dite_eq_right h]
    simp only [he, Bool.false_eq_true, dite_false]
    simp only [stride'] at hgt
    rw [dite_eq_right hgt]
    exact ih _ hr

/-- The insertion probe in a group with no candidate and an EMPTY byte ends there. -/
private theorem findInsLoop_first {rep : UInt64} {hA : ArrU ctrl mask} {pos stride : USize}
    {g m : UInt64} {ins : USize} {hs : stride.toNat ≤ mask.toNat} {hm : IsMask m}
    {hk : mask.toNat < keys.size ∨ (m = 0 ∧ matchEmpty g ≠ 0)} (hm0 : m = 0)
    (he : matchEmpty g ≠ 0) :
    findInsLoop ctrl keys a mask rep pos stride g m ins hA hs hm hk =
      insUpdU mask pos g ins + (mask + 1) := by
  rw [findInsLoop, dite_eq_right (by simp [hm0])]
  dsimp only
  rw [dite_eq_left (by simpa using he)]
  rfl

end WordLoops

/-! ## The insertion probe on `Nat` indices hits where the lookup does (no lawfulness) -/

section FusedN

variable [BEq α] [Hashable α] {ctrl : ByteArray} {keys : Array α} {mask : USize} {cap : Nat}
  {shift : UInt64} {a : α}

/-- The insertion probe hits exactly where the lookup does. -/
theorem insProbeN_inl_iff (hA : ArrN ctrl keys cap) {i : Nat} :
    insProbeN ctrl keys cap shift a hA = .inl i ↔ findN ctrl keys cap shift a hA = some i := by
  rw [← insProbeN_getLeft hA shift a, Sum.getLeft?_eq_some_iff]

/-- The insertion probe of `containsThenInsertN` (with fast path C) hits exactly where the lookup
does. -/
theorem insSlotN_inl_iff (hA : ArrN ctrl keys cap) {i : Nat} :
    insSlotN ctrl keys a cap (hashBits shift a) hA = .inl i ↔
      findN ctrl keys cap shift a hA = some i := by
  unfold insSlotN
  dsimp only
  split
  · rename_i hfast
    rw [Bool.and_eq_true, beq_iff_eq] at hfast
    have hn : findN ctrl keys cap shift a hA = none :=
      findLoopN_first hfast.1 (matchEmpty_ne_of_low hfast.2)
    simp [hn]
  · exact insProbeN_inl_iff hA

end FusedN

/-! ## The probes in a well-formed table -/

section Helpers

variable [BEq α] [Hashable α] {s : Slots α β} {size gl : Nat} {mask : USize} {shift : UInt64}

/-- A table with slots has a non-full slot: `size ≤ 7/8 · cap` (`WF.room`). -/
private theorem WF.exists_free (wf : WF s size gl mask shift) (hc : 0 < s.cap) :
    ∃ i < s.cap, ¬s.ctrl[i]! < 0x80 := by
  refine Classical.byContradiction fun hne => ?_
  have hall : ∀ i < s.cap, s.ctrl[i]! < 0x80 := fun i hi =>
    Classical.byContradiction fun h => hne ⟨i, hi, h⟩
  have hk := wf.keys_size hc
  have hv := wf.vals_size hc
  have hlen : s.entries.length = s.cap := by
    unfold Slots.entries
    rw [List.filterMap_length_eq_length.mpr, List.length_range]
    intro i hi
    have hi := List.mem_range.mp hi
    have hic : i < s.ctrl.size := by unfold Slots.cap at hi; omega
    have hf := hall i hi
    rw [getElem!_pos s.ctrl i hic] at hf
    simp [Slots.entryAt, getElem?_pos s.ctrl i hic, hf, getElem?_pos s.keys i (by omega),
      getElem?_pos s.vals i (by omega)]
  have h1 := wf.room
  have h2 := wf.size_eq
  have h8 := (wf.mirrored hc).le_cap
  unfold capacityOf at h1
  omega

/-- A completed miss proves `a` absent: a stored key `== a` has the hash of `a`, so the probe of
`a` reaches its slot (`ProbeInv`), which carries the tag of `a` (`TagInv`). -/
private theorem absent_of_post (wf : WF s size gl mask shift) {cap : Nat} (hcap : s.cap = cap)
    {a : α}
    (h : FindPost s.ctrl s.keys a cap (homeN (hashBits shift a) cap) (tagOf (hashBits shift a))
      none)
    [EquivBEq α] [LawfulHashable α] : s.Absent a := by
  subst hcap
  intro i kk hfull hk
  cases hb : (kk == a)
  · rfl
  · exfalso
    have hh : hashBits shift kk = hashBits shift a := by
      unfold hashBits; rw [LawfulHashable.hash_eq kk a hb]
    have ht := wf.tag i kk hfull hk
    have hr := wf.probe i kk hfull hk
    rw [hh] at ht hr
    obtain ⟨K, hK, J, hJ, hKJ, hne⟩ := hr
    subst hKJ
    have := h K hK J hJ hne ht kk hk
    rw [hb] at this
    cases this

/-- A lookup on `Nat` indices that finds a slot finds a hit. -/
theorem WF.findN_hit (wf : WF s size gl mask shift) (hA : ArrN s.ctrl s.keys (s.ctrl.size - 8))
    {a : α} {i : Nat} (he : findN s.ctrl s.keys (s.ctrl.size - 8) shift a hA = some i) :
    s.Hit shift a i := by
  have hc : 0 < s.cap := hA.pos
  have post := findN_post (cap := s.ctrl.size - 8) (wf.mirrored hc) wf.ctrl hA shift a
  rw [he] at post
  obtain ⟨hi, ht, hk⟩ := post
  exact ⟨⟨hi, by rw [ht]; exact tagOf_lt _⟩, ht, hk⟩

/-- A lookup on `Nat` indices that finds none proves `a` absent (lawful instances). -/
theorem WF.findN_absent (wf : WF s size gl mask shift)
    (hA : ArrN s.ctrl s.keys (s.ctrl.size - 8)) {a : α}
    (he : findN s.ctrl s.keys (s.ctrl.size - 8) shift a hA = none) [EquivBEq α]
    [LawfulHashable α] : s.Absent a := by
  have hc : 0 < s.cap := hA.pos
  have post := findN_post (cap := s.ctrl.size - 8) (wf.mirrored hc) wf.ctrl hA shift a
  rw [he] at post
  exact absent_of_post wf rfl post

/-- The insertion probe on `Nat` indices that finds no hit returns where the new key goes. -/
theorem WF.insProbeN_new (wf : WF s size gl mask shift)
    (hA : ArrN s.ctrl s.keys (s.ctrl.size - 8)) {a : α} {j : Nat}
    (he : insProbeN s.ctrl s.keys (s.ctrl.size - 8) shift a hA = .inr j) :
    NewSlot s shift a (hashBits shift a) j := by
  have hc : 0 < s.cap := hA.pos
  obtain ⟨hj, hfr, hreach⟩ := insProbeN_free (cap := s.ctrl.size - 8) (wf.mirrored hc) wf.ctrl
    (wf.exists_free hc) hA shift a he
  refine ⟨rfl, Or.inl ⟨hj, hfr, hreach⟩, ?_⟩
  intro _ _
  have hl := insProbeN_getLeft hA shift a
  rw [he, Sum.getLeft?_inr] at hl
  exact wf.findN_absent hA hl.symm

/-- Fast path C on `Nat` indices: the home slot of `a` is a `NewSlot`. -/
private theorem WF.fastN_new (wf : WF s size gl mask shift)
    (hA : ArrN s.ctrl s.keys (s.ctrl.size - 8)) {a : α}
    (hfast : (matchTag (ctrlWordN s.ctrl (homeN (hashBits shift a) (s.ctrl.size - 8))
        (hA.mod_word _)) (repTag (tagOf (hashBits shift a))) == 0 &&
      ctrlWordN s.ctrl (homeN (hashBits shift a) (s.ctrl.size - 8)) (hA.mod_word _) &&& 0xFF ==
        0xFF) = true) :
    NewSlot s shift a (hashBits shift a) (homeN (hashBits shift a) (s.ctrl.size - 8)) := by
  have hc : 0 < s.cap := hA.pos
  have hM := wf.mirrored hc
  have hp : homeN (hashBits shift a) (s.ctrl.size - 8) < s.ctrl.size - 8 := Nat.mod_lt _ hc
  rw [Bool.and_eq_true, beq_iff_eq] at hfast
  obtain ⟨hmt, hlow⟩ := hfast
  have hE := byte_zero_of_low hlow
  have hb := byte_wordN (cap := s.ctrl.size - 8) (pos := homeN (hashBits shift a) (s.ctrl.size - 8))
    (j := 0) (hw := hA.mod_word _) hM (by decide)
  rw [hb, Nat.add_zero, Nat.mod_eq_of_lt hp] at hE
  refine ⟨rfl, Or.inl ⟨hp, Or.inl hE, 0, by have := hM.le_cap; unfold Slots.cap at this ⊢; omega,
    0, by decide, ?_, fun k' hk' => absurd hk' (Nat.not_lt_zero _)⟩, ?_⟩
  · show (probePos (s.ctrl.size - 8) (homeN (hashBits shift a) (s.ctrl.size - 8)) 0 + 0) %
      (s.ctrl.size - 8) = _
    rw [Nat.add_zero, ← start_pos shift a, Nat.mod_eq_of_lt hp]
  · intro _ _
    exact wf.findN_absent hA (findLoopN_first hmt (matchEmpty_ne_of_low hlow))

/-- The shape facts of an allocated table on the machine-word path. -/
private theorem WF.wordFacts (wf : WF s size gl mask shift) (h : LoopU s.ctrl s.keys mask)
    (hc : 0 < s.cap) :
    Geom s.cap mask ∧ s.ctrl.size = s.cap + 8 ∧ ArrN s.ctrl s.keys s.cap :=
  have hsz := (wf.mirrored hc).size_eq
  ⟨wf.geom (smallMask_of_lt h.arr.small) hc, hsz,
    ⟨⟨hc, by omega⟩, by have := wf.keys_size hc; omega⟩⟩

end Helpers

section WordHelpers

variable [BEq α] [Hashable α] {ctrl : ByteArray} {keys : Array α} {mask : USize} {cap : Nat}
  {shift : UInt64} {a : α}

/-- The machine-word lookup is the one on `Nat` indices. -/
private theorem findU_toNat (hg : Geom cap mask) (h : LoopU ctrl keys mask)
    (hA : ArrN ctrl keys cap) :
    (if findU ctrl keys mask shift a h ≤ mask then some (findU ctrl keys mask shift a h).toNat
      else none) = findN ctrl keys cap shift a hA := by
  have hsm := h.arr.small
  have hmc := hg.mask_add_one
  have hh : (homeU (hashBits shift a) mask).toNat = homeN (hashBits shift a) cap := homeU_toNat hg
  have hp : (homeU (hashBits shift a) mask).toNat < cap := hh ▸ Nat.mod_lt _ hA.pos
  have hgw : ctrlWord ctrl (homeU (hashBits shift a) mask) (and_mask_word h.arr.word) =
      ctrlWordN ctrl (homeN (hashBits shift a) cap) (hA.mod_word _) :=
    (ctrlWord_eq_ctrlWordN (h' := hA.word_of_lt hp) (by omega)).trans (ctrlWordN_congr hh)
  exact (findLoop_toNat hg hA _ h.arr _ 0 _ _ stride_zero (isMask_matchTag _ _)
    (firstGroup h _) hp).trans
    (findLoopN_congr hh (by simp) hgw (congrArg (fun x => matchTag x _) hgw))

/-- The machine-word insertion probe is the one on `Nat` indices, in a well-formed table. -/
private theorem insProbeU_toNat {vals : Array β} {size gl : Nat}
    (wf : WF ⟨ctrl, keys, vals⟩ size gl mask shift) (hg : Geom cap mask)
    (hsz : ctrl.size = cap + 8) (h : LoopU ctrl keys mask) (hA : ArrN ctrl keys cap) :
    (if insProbeU ctrl keys mask shift a h ≤ mask then
      Sum.inl (insProbeU ctrl keys mask shift a h).toNat
      else Sum.inr (insProbeU ctrl keys mask shift a h - (mask + 1)).toNat) =
      insProbeN ctrl keys cap shift a hA := by
  have hsm := h.arr.small
  have hmc := hg.mask_add_one
  have hh : (homeU (hashBits shift a) mask).toNat = homeN (hashBits shift a) cap := homeU_toNat hg
  have hp : (homeU (hashBits shift a) mask).toNat < cap := hh ▸ Nat.mod_lt _ hA.pos
  have hgw : ctrlWord ctrl (homeU (hashBits shift a) mask) (and_mask_word h.arr.word) =
      ctrlWordN ctrl (homeN (hashBits shift a) cap) (hA.mod_word _) :=
    (ctrlWord_eq_ctrlWordN (h' := hA.word_of_lt hp) (by omega)).trans (ctrlWordN_congr hh)
  have hm1 : (mask + 1).toNat = cap := by rw [toNat_add_one hsm]; omega
  have hrel : InsRel mask cap (insProbeU ctrl keys mask shift a h)
      (findInsLoopN ctrl keys a cap (repTag (tagOf (hashBits shift a)))
        (homeU (hashBits shift a) mask).toNat (0 : USize).toNat
        (ctrlWord ctrl (homeU (hashBits shift a) mask) (and_mask_word h.arr.word))
        (matchTag (ctrlWord ctrl (homeU (hashBits shift a) mask) (and_mask_word h.arr.word))
          (repTag (tagOf (hashBits shift a)))) (mask + 1).toNat hA (isMask_matchTag _ _)) :=
    findInsLoop_toNat hg hA _ h.arr _ 0 _ _ (mask + 1) stride_zero (isMask_matchTag _ _)
      (firstGroup h _) hp (by omega)
  rw [findInsLoopN_congr (stride := (0 : USize).toNat) (stride' := 0)
      (m' := matchTag (ctrlWordN ctrl (homeN (hashBits shift a) cap)
      (hA.mod_word _)) (repTag (tagOf (hashBits shift a)))) (hm' := isMask_matchTag _ _) hh
      USize.toNat_zero hgw (congrArg (fun x => matchTag x _) hgw) hm1] at hrel
  -- the probe ends at a free slot, below `cap`
  have hcap : (⟨ctrl, keys, vals⟩ : Slots α β).cap = cap := by
    show ctrl.size - 8 = cap; omega
  have hc : 0 < (⟨ctrl, keys, vals⟩ : Slots α β).cap := by rw [hcap]; exact hA.pos
  have hM : Mirrored ctrl cap := hcap ▸ wf.mirrored hc
  have hctrl : ∀ i < cap, IsCtrl ctrl[i]! := hcap ▸ wf.ctrl
  have hfree : ∃ i < cap, ¬ctrl[i]! < 0x80 := hcap ▸ wf.exists_free hc
  have hfin : ∀ j, insProbeN ctrl keys cap shift a hA = .inr j → j < cap := fun j hj =>
    (insProbeN_free hM hctrl hfree hA shift a hj).1
  change InsRel mask cap _ (insProbeN ctrl keys cap shift a hA) at hrel
  generalize insProbeN ctrl keys cap shift a hA = n at hrel hfin
  rcases n with i | j
  · obtain ⟨hle, hi⟩ := hrel
    rw [ite_eq_left hle, hi]
  · obtain ⟨-, u, hu, hr⟩ := hrel
    have hj := hfin j rfl
    have hnle : ¬insProbeU ctrl keys mask shift a h ≤ mask := by
      rw [hr, USize.le_iff_toNat_le, USize.toNat_add, hm1]
      have h2 : 2 ^ 32 ≤ 2 ^ System.Platform.numBits := USize.le_size
      rw [Nat.mod_eq_of_lt (by omega)]
      omega
    rw [ite_eq_right hnle, hr, USize.add_sub_cancel, hu]

/-- In the unallocated table (no key cells), the lookup misses. -/
private theorem findU_unalloc (h : LoopU ctrl keys mask) (hk : keys.size = 0) :
    ¬findU ctrl keys mask shift a h ≤ mask := by
  rcases firstGroup h (hashBits shift a) with hk' | ⟨hm0, he⟩
  · omega
  · dsimp only [findU]
    rw [findLoop_first hm0 he]
    exact not_succ_le h.arr.small

/-- In the unallocated table, the insertion probe ends past the only slot `0`, at a slot below
8 (`1` or `2`, minus `mask + 1 = 1`). -/
private theorem insProbeU_unalloc (h : LoopU ctrl keys mask) (hk : keys.size = 0)
    (hm0 : mask = 0) :
    ¬insProbeU ctrl keys mask shift a h ≤ mask ∧
      (insProbeU ctrl keys mask shift a h - (mask + 1)).toNat < 8 := by
  subst hm0
  rcases firstGroup h (hashBits shift a) with hk' | ⟨hmt, he⟩
  · omega
  · have e : insProbeU ctrl keys 0 shift a h =
        insUpdU 0 (homeU (hashBits shift a) 0)
          (ctrlWord ctrl (homeU (hashBits shift a) 0) (and_mask_word h.arr.word)) (0 + 1) +
          (0 + 1) := findInsLoop_first hmt he
    have hu : (insUpdU 0 (homeU (hashBits shift a) 0)
        (ctrlWord ctrl (homeU (hashBits shift a) 0) (and_mask_word h.arr.word)) (0 + 1)).toNat ≤
        1 := by
      unfold insUpdU
      split
      · split
        · rw [USize.toNat_and, USize.toNat_zero, Nat.and_zero]; omega
        · simp
      · simp
    rw [e, USize.add_sub_cancel]
    refine ⟨?_, by omega⟩
    have h01 : ((0 : USize) + 1).toNat = 1 := by simp
    have h2 : 2 ^ 32 ≤ 2 ^ System.Platform.numBits := USize.le_size
    rw [USize.le_iff_toNat_le, USize.toNat_add, h01, Nat.mod_eq_of_lt (by omega),
      USize.toNat_zero]
    omega

/-- Fast path C applies only where the lookup misses (no lawfulness). -/
theorem fast_findU (h : LoopU ctrl keys mask)
    (hmt : (matchTag (ctrlWord ctrl (homeU (hashBits shift a) mask) (and_mask_word h.arr.word))
      (repTag (tagOf (hashBits shift a))) == 0) = true)
    (hg : (ctrlWord ctrl (homeU (hashBits shift a) mask) (and_mask_word h.arr.word) &&& 0xFF ==
      0xFF) = true) :
    ¬findU ctrl keys mask shift a h ≤ mask := by
  dsimp only [findU]
  rw [findLoop_first (beq_iff_eq.mp hmt) (matchEmpty_ne_of_low hg)]
  exact not_succ_le h.arr.small

end WordHelpers

section Spec

variable [BEq α] [Hashable α] {s : Slots α β} {size gl : Nat} {mask : USize} {shift : UInt64}

/-! ## The lookup probe -/

/-- A machine-word lookup that ends at a slot ends at a hit. -/
theorem WF.findU_hit (wf : WF s size gl mask shift) (h : LoopU s.ctrl s.keys mask) {a : α}
    (hi : findU s.ctrl s.keys mask shift a h ≤ mask) :
    s.Hit shift a (findU s.ctrl s.keys mask shift a h).toNat := by
  rcases Nat.eq_zero_or_pos s.cap with hc | hc
  · exact absurd hi (findU_unalloc h (wf.unalloc_of hc).keys_size)
  · obtain ⟨hg, -, hAN⟩ := wf.wordFacts h hc
    have e := findU_toNat (a := a) (shift := shift) hg h hAN
    rw [ite_eq_left hi] at e
    exact wf.findN_hit hAN e.symm

/-- A machine-word lookup that ends past the slots proves `a` absent (lawful instances). -/
theorem WF.findU_absent (wf : WF s size gl mask shift) (h : LoopU s.ctrl s.keys mask) {a : α}
    (hi : ¬findU s.ctrl s.keys mask shift a h ≤ mask) [EquivBEq α] [LawfulHashable α] :
    s.Absent a := by
  rcases Nat.eq_zero_or_pos s.cap with hc | hc
  · intro i _ hf; exact absurd hf.1 (by omega)
  · obtain ⟨hg, -, hAN⟩ := wf.wordFacts h hc
    have e := findU_toNat (a := a) (shift := shift) hg h hAN
    rw [ite_eq_right hi] at e
    exact wf.findN_absent hAN e.symm

/-! ## The insertion probe -/

/-- The machine-word insertion probe that ends at a slot ends at a hit. -/
theorem WF.insProbeU_hit (wf : WF s size gl mask shift) (h : LoopU s.ctrl s.keys mask) {a : α}
    (hr : insProbeU s.ctrl s.keys mask shift a h ≤ mask) :
    s.Hit shift a (insProbeU s.ctrl s.keys mask shift a h).toNat := by
  rcases Nat.eq_zero_or_pos s.cap with hc | hc
  · have hu := wf.unalloc_of hc
    exact absurd hr (insProbeU_unalloc h hu.keys_size hu.mask_eq).1
  · obtain ⟨hg, hsz, hAN⟩ := wf.wordFacts h hc
    have e := insProbeU_toNat (a := a) (vals := s.vals) wf hg hsz h hAN
    rw [ite_eq_left hr] at e
    exact wf.findN_hit hAN ((insProbeN_inl_iff hAN).mp e.symm)

/-- The machine-word insertion probe that ends past the slots ends at `mask + 1` plus the slot
where the new key goes. -/
theorem WF.insProbeU_new (wf : WF s size gl mask shift) (h : LoopU s.ctrl s.keys mask) {a : α}
    (hr : ¬insProbeU s.ctrl s.keys mask shift a h ≤ mask) :
    NewSlot s shift a (hashBits shift a)
      (insProbeU s.ctrl s.keys mask shift a h - (mask + 1)).toNat := by
  rcases Nat.eq_zero_or_pos s.cap with hc | hc
  · have hu := wf.unalloc_of hc
    refine ⟨rfl, Or.inr ⟨hc, (insProbeU_unalloc h hu.keys_size hu.mask_eq).2⟩, ?_⟩
    intro _ _ i _ hf; exact absurd hf.1 (by omega)
  · obtain ⟨hg, hsz, hAN⟩ := wf.wordFacts h hc
    have e := insProbeU_toNat (a := a) (vals := s.vals) wf hg hsz h hAN
    rw [ite_eq_right hr] at e
    exact wf.insProbeN_new hAN e.symm

/-- **Fast path C**: when no lane of the home group carries the tag and the home slot is EMPTY,
the new key goes to the home slot. -/
theorem WF.fast_new (wf : WF s size gl mask shift) (h : LoopU s.ctrl s.keys mask) {a : α}
    (hmt : (matchTag (ctrlWord s.ctrl (homeU (hashBits shift a) mask) (and_mask_word h.arr.word))
      (repTag (tagOf (hashBits shift a))) == 0) = true)
    (hg : (ctrlWord s.ctrl (homeU (hashBits shift a) mask) (and_mask_word h.arr.word) &&& 0xFF ==
      0xFF) = true) :
    NewSlot s shift a (hashBits shift a) (homeU (hashBits shift a) mask).toNat := by
  rcases Nat.eq_zero_or_pos s.cap with hc | hc
  · have hu := wf.unalloc_of hc
    refine ⟨rfl, Or.inr ⟨hc, ?_⟩, ?_⟩
    · unfold homeU; rw [hu.mask_eq, USize.toNat_and, USize.toNat_zero, Nat.and_zero]; omega
    · intro _ _ i _ hf; exact absurd hf.1 (by omega)
  · obtain ⟨hgeo, -, hAN⟩ := wf.wordFacts h hc
    have hM := wf.mirrored hc
    have hsm := h.arr.small
    have hmc := hgeo.mask_add_one
    have hh : (homeU (hashBits shift a) mask).toNat = homeN (hashBits shift a) s.cap :=
      homeU_toNat hgeo
    have hp : (homeU (hashBits shift a) mask).toNat < s.cap := hh ▸ Nat.mod_lt _ hc
    have hgw : ctrlWord s.ctrl (homeU (hashBits shift a) mask) (and_mask_word h.arr.word) =
        ctrlWordN s.ctrl (homeU (hashBits shift a) mask).toNat (hAN.word_of_lt hp) :=
      ctrlWord_eq_ctrlWordN (by omega)
    have hE := byte_zero_of_low (hgw ▸ hg)
    have hb := byte_wordN (j := 0) (hw := hAN.word_of_lt hp) hM (by decide)
    rw [hb, Nat.add_zero, Nat.mod_eq_of_lt hp] at hE
    refine ⟨rfl, Or.inl ⟨hp, Or.inl hE, 0, by have := hM.le_cap; omega, 0, by decide, ?_,
      fun k' hk' => absurd hk' (Nat.not_lt_zero _)⟩, ?_⟩
    · rw [Nat.add_zero, probePos_zero, hh]; simp [homeN]
    · intro _ _; exact wf.findU_absent h (fast_findU h hmt hg)

/-- The insertion probe of `containsThenInsertN` (with fast path C) that finds a slot finds a
hit. -/
theorem WF.insSlotN_hit (wf : WF s size gl mask shift)
    (hA : ArrN s.ctrl s.keys (s.ctrl.size - 8)) {a : α} {i : Nat}
    (he : insSlotN s.ctrl s.keys a (s.ctrl.size - 8) (hashBits shift a) hA = .inl i) :
    s.Hit shift a i :=
  wf.findN_hit hA ((insSlotN_inl_iff hA).mp he)

/-- The insertion probe of `containsThenInsertN` that finds no hit returns where the new key
goes. -/
theorem WF.insSlotN_new (wf : WF s size gl mask shift)
    (hA : ArrN s.ctrl s.keys (s.ctrl.size - 8)) {a : α} {j : Nat}
    (he : insSlotN s.ctrl s.keys a (s.ctrl.size - 8) (hashBits shift a) hA = .inr j) :
    NewSlot s shift a (hashBits shift a) j := by
  unfold insSlotN at he
  dsimp only at he
  split at he
  · rename_i hfast
    cases he
    exact wf.fastN_new hA hfast
  · exact wf.insProbeN_new hA he

/-- The insertion probe on `Nat` indices that finds a slot finds a hit. -/
theorem WF.insProbeN_hit (wf : WF s size gl mask shift)
    (hA : ArrN s.ctrl s.keys (s.ctrl.size - 8)) {a : α} {i : Nat}
    (he : insProbeN s.ctrl s.keys (s.ctrl.size - 8) shift a hA = .inl i) : s.Hit shift a i :=
  wf.findN_hit hA ((insProbeN_inl_iff hA).mp he)

end Spec

/-! ## The fused operations: the insertion probe hits where the lookup does (no lawfulness) -/

section Fused

variable [BEq α] [Hashable α] {ctrl : ByteArray} {keys : Array α} {mask : USize} {cap : Nat}
  {shift : UInt64} {a : α}

/-- The insertion probe ends at a slot exactly when the lookup does. (The invariant is needed only
on 32-bit platforms: in a full table of `2 ^ 31` slots, `ins + (mask + 1)` would wrap to `0`;
`WF.room` leaves a free slot.) -/
theorem WF.insProbeU_le_iff {vals : Array β} {size gl : Nat}
    (wf : WF ⟨ctrl, keys, vals⟩ size gl mask shift) (h : LoopU ctrl keys mask) :
    insProbeU ctrl keys mask shift a h ≤ mask ↔ findU ctrl keys mask shift a h ≤ mask := by
  constructor
  · intro hr
    rcases Nat.eq_zero_or_pos (⟨ctrl, keys, vals⟩ : Slots α β).cap with hc | hc
    · have hu := wf.unalloc_of hc
      exact absurd hr (insProbeU_unalloc h hu.keys_size hu.mask_eq).1
    · obtain ⟨hg, hsz, hAN⟩ := wf.wordFacts h hc
      have e1 := insProbeU_toNat (a := a) wf hg hsz h hAN
      rw [ite_eq_left hr] at e1
      have e2 := findU_toNat (a := a) (shift := shift) hg h hAN
      rw [(insProbeN_inl_iff hAN).mp e1.symm] at e2
      refine Classical.byContradiction fun hn => ?_
      rw [ite_eq_right hn] at e2
      cases e2
  · intro hr
    have e : insProbeU ctrl keys mask shift a h = findU ctrl keys mask shift a h :=
      findInsLoop_eq_findLoop _ h.arr _ _ _ _ _ _ _ (mask + 1) hr
    rw [e]
    exact hr

/-- Where the lookup hits, the insertion probe ends at the same slot. -/
theorem insProbeU_eq_findU (h : LoopU ctrl keys mask)
    (hr : findU ctrl keys mask shift a h ≤ mask) :
    insProbeU ctrl keys mask shift a h = findU ctrl keys mask shift a h :=
  findInsLoop_eq_findLoop _ h.arr _ _ _ _ _ _ _ (mask + 1) hr

end Fused

end SwissTable.Core.Swiss
