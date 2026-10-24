module

/-!
# Groups of control bytes for a core with the SwissTable layout

Definitions and lemmas that a SwissTable-style core (hashbrown's generic, non-SIMD layout) needs,
independent of keys and values. The selected core `SwissTable.Core.Swiss` (`Defs.lean` on) is built
on them; the lemmas are stated for any such core, so some of them are not used by this one.

## Layout assumed

`cap` slots, a power of two, at least 8. The control array `c : ByteArray` has `cap + 8` bytes:
byte `k < cap` is the control byte of slot `k`, and bytes `cap .. cap + 7` repeat bytes `0 .. 7`
(`Mirrored`). Control bytes use hashbrown's encoding (`IsCtrl`):

    EMPTY = 0xFF        DELETED = 0x80        FULL = 0x00 .. 0x7F (the 7-bit tag h2)

## Contents

* `ctrlWord c i h`: the 8 bytes from `i`, little-endian, read by 8 `ByteArray.uget`s that clang
  combines into one unaligned 64-bit load. `byte_ctrlWord`: byte `j` of it is
  `c[(i + j) % USize.size]`, the index computed in `USize`; `byte_ctrlWord'`: it is `c[i + j]`
  when `i + 8` does not wrap.
* Match masks. A *mask* (`IsMask`) has its set bits among the flag bits `8 * j + 7`; `flag m j` is
  bit `8 * j + 7`. For a group word `g`:
  * `matchTag g (repTag t)`: flag `j` iff byte `j` of `g` is `t`, for every byte `t` (the exact
    form, with no borrow between lanes: `flag_matchTag`);
  * `matchEmpty g`: flag `j` iff byte `j` is at least `0xC0`, which for control bytes is EMPTY;
  * `matchFree g`: flag `j` iff byte `j` has its top bit set (EMPTY or DELETED);
  * `matchFull g`: flag `j` iff byte `j` is below `0x80` (FULL).
* `lowestLane m`: the lane of the lowest flag of a nonzero mask, without a loop
  (`lowestLane_spec`); a lane below 8 for every mask, `0` for the zero mask (`lowestLane_lt`,
  `lowestLane_zero`). `clearLowest m` removes exactly that flag (`flag_clearLowest`).
* `Mirrored c cap`, `slotByte c cap k = c[k % cap]`, and `setCtrl`, which writes slot `i` and its
  mirror branch-free; `setCtrl` keeps `Mirrored` and changes exactly slot `i`
  (`mirrored_setCtrl`, `slotByte_setCtrl`). Under `Mirrored`, byte `j` of the group word at
  `p < cap` is the control byte of slot `(p + j) % cap` (`byte_ctrlWord_of_mirrored`).
* `Geom cap mask`: the table geometry a core keeps in its invariant (`mask + 1 = cap`, a power of
  two, `8 ≤ cap < USize.size`), with the slot-index lemmas restated over it (`Geom.*`).
* The erase rule (hashbrown's): `needsTombstone ea eb`, for the EMPTY masks of the groups at `i`
  and at `i - 8`, decides whether erasing slot `i` must write DELETED. When it is `false`, every
  8-slot window containing slot `i` already has an EMPTY slot
  (`exists_empty_of_needsTombstone_eq_false`), so writing EMPTY cannot cut a probe short; on
  masks, `needsTombstone_eq_false_iff` says it is `false` exactly then.
* Triangular probing over groups, as the core's probes do it: the `k`-th group starts at
  `probePos cap p₀ k = (p₀ + 8 * (k * (k + 1) / 2)) % cap`, which the loop computes as
  `pos ← (pos + stride) &&& mask` after `stride ← stride + 8` (`probe_step`). The first
  `cap / 8` groups cover every slot (`probe_cover`), each exactly once (`probe_unique`).

The lemmas about `setCtrl` assume `cap < USize.size`, so that slot `i + cap` of the mirror is an
index that does not wrap. Core Lean bounds no array size by `USize.size`, so a core must get it
from its allocation (`lg < System.Platform.numBits`) and keep it in its invariant (`Geom`).
The core's unallocated empty map (the 8 EMPTY bytes `emptyGroup`, `mask = 0`) is not `Mirrored`;
the core proves that case with `byte_ctrlWord` directly (`firstGroup` in `Proofs/Bounds.lean`).

## Use from other modules

The section is `public` but not `@[expose]`d: importing modules see the statements but cannot
unfold the definitions (`unfold`, `decide` and `rfl` through them fail). Every definition a core
reasons about therefore has an exported characterisation: `EMPTY_eq`, `DELETED_eq`,
`isCtrl_iff`, `lsbs_eq`, `msbs_eq`, `lows_eq`, `byte_def`, `flag_def`, `isMask_iff`,
`repTag_eq`, `slotByte_def`, `needsTombstone_eq`, `tri_def`, `probePos_def`. The `Decidable`
instances of `IsCtrl` and `IsMask` are stated on literals, so that `decide` works on them there.
`test/SwissTableTest/SwissGroupUse.lean` proves a lookup step and an erase step from another module
with these lemmas only.

## Design choices

* The tag match is the exact form, not hashbrown's borrow form `(x - lsbs) &&& ~~~x &&& msbs`,
  which the bake-off prototypes used. It costs one instruction more per group (5 against 4 on
  arm64), and the SwissF prototype measured it within ±2% of the borrow form (its "Measured
  alternatives" notes, `docs/bakeoff/SwissF.lean.txt`). It never flags a byte other than the tag,
  so a core needs no case for false positives and never compares a key for one.
* The erase rule is specified in the comparison form the core uses (`needsTombstone`), not in
  hashbrown's form that counts the EMPTY lanes before and after the slot. The bake-off's counting
  version (by smearing the masks) took the same decision on all 65536 pairs of masks (checked by
  a script, not proved) but cost more instructions; it has no lemma here.

## Proof method

`bv_decide` is not used: its proofs depend on a native-evaluation axiom. The word lemmas are
reduced to one byte at a time (`Lane.lane`, the byte `x / 256 ^ j % 256` of a natural number),
with `Nat.testBit` for the bitwise operations and a no-carry lemma (`Lane.lane_add`) for the one
addition of `matchTag`; the remaining facts about single bytes, and the 256 possible flag patterns
of a mask (for `lowestLane` and `clearLowest`), are checked by `decide +kernel`, whose proofs use
no axioms. Every theorem depends on at most `propext`, `Classical.choice` and `Quot.sound`.
-/

public section

namespace SwissTable.Core.Swiss

/-! ## Bytes of a natural number -/

namespace Lane

/-- Byte `j` of a natural number. -/
def lane (x j : Nat) : Nat := x / 256 ^ j % 256

theorem lane_def (x j : Nat) : lane x j = x / 256 ^ j % 256 := by unfold lane; rfl

theorem pow256 (j : Nat) : (256 : Nat) ^ j = 2 ^ (8 * j) := by
  rw [Nat.pow_mul]

theorem lane_lt (x j : Nat) : lane x j < 256 := Nat.mod_lt _ (by decide)

theorem testBit_lane (x j k : Nat) :
    (lane x j).testBit k = (decide (k < 8) && x.testBit (8 * j + k)) := by
  unfold lane
  rw [pow256, show (256 : Nat) = 2 ^ 8 from rfl, Nat.testBit_mod_two_pow,
    Nat.testBit_div_two_pow, Nat.add_comm k]

theorem testBit_eq_lane (x j k : Nat) (hk : k < 8) :
    x.testBit (8 * j + k) = (lane x j).testBit k := by
  simp [testBit_lane, hk]

theorem lane_and (x y j : Nat) : lane (x &&& y) j = lane x j &&& lane y j := by
  apply Nat.eq_of_testBit_eq; intro k
  simp only [testBit_lane, Nat.testBit_and]
  cases decide (k < 8) <;> simp

theorem lane_or (x y j : Nat) : lane (x ||| y) j = lane x j ||| lane y j := by
  apply Nat.eq_of_testBit_eq; intro k
  simp only [testBit_lane, Nat.testBit_or]
  cases decide (k < 8) <;> simp

theorem lane_xor (x y j : Nat) : lane (x ^^^ y) j = lane x j ^^^ lane y j := by
  apply Nat.eq_of_testBit_eq; intro k
  simp only [testBit_lane, Nat.testBit_xor]
  cases decide (k < 8) <;> simp

/-- Reducing modulo `2 ^ 64` keeps the low 8 bytes. -/
theorem lane_mod (x j : Nat) (hj : j < 8) : lane (x % 2 ^ 64) j = lane x j := by
  apply Nat.eq_of_testBit_eq; intro k
  simp only [testBit_lane, Nat.testBit_mod_two_pow]
  by_cases hk : k < 8
  · have : 8 * j + k < 64 := by omega
    simp [hk, this]
  · simp [hk]

/-- No carry out of the low `n` bytes when every byte sum is below 256. -/
theorem mod_add_mod_lt (a b : Nat) : ∀ n, (∀ k < n, lane a k + lane b k < 256) →
    a % 256 ^ n + b % 256 ^ n < 256 ^ n
  | 0, _ => by simp [Nat.mod_one]
  | n + 1, h => by
    have ih := mod_add_mod_lt a b n (fun k hk => h k (by omega))
    have hn := h n (by omega)
    unfold lane at hn
    rw [Nat.mod_pow_succ, Nat.mod_pow_succ, Nat.pow_succ]
    have : 256 ^ n * (a / 256 ^ n % 256) + 256 ^ n * (b / 256 ^ n % 256) ≤ 256 ^ n * 255 := by
      rw [← Nat.mul_add]; exact Nat.mul_le_mul_left _ (by omega)
    omega

/-- Byte `j` of a sum without carries: when every byte sum up to `j` is below 256. -/
theorem lane_add (a b j : Nat) (h : ∀ k ≤ j, lane a k + lane b k < 256) :
    lane (a + b) j = lane a j + lane b j := by
  have hlow := mod_add_mod_lt a b j (fun k hk => h k (by omega))
  have hj := h j (Nat.le_refl _)
  unfold lane at *
  have hP : 0 < 256 ^ j := Nat.pow_pos (by decide)
  have e : a + b = (a % 256 ^ j + b % 256 ^ j) + 256 ^ j * (a / 256 ^ j + b / 256 ^ j) := by
    have := Nat.mod_add_div a (256 ^ j); have := Nat.mod_add_div b (256 ^ j)
    rw [Nat.mul_add]; omega
  rw [e, Nat.add_mul_div_left _ _ hP, Nat.div_eq_of_lt hlow, Nat.zero_add, Nat.add_mod,
    Nat.mod_eq_of_lt hj]

private theorem xor_eq_zero_iff (a b : Nat) : a ^^^ b = 0 ↔ a = b := by
  constructor
  · intro h
    apply Nat.eq_of_testBit_eq; intro i
    have := congrArg (Nat.testBit · i) h
    simp only [Nat.testBit_xor, Nat.zero_testBit] at this
    cases ha : a.testBit i <;> cases hb : b.testBit i <;> simp_all
  · rintro rfl; exact Nat.xor_self a

/-- A natural number below `2 ^ 64` is the sum of its 8 bytes. -/
theorem eq_sum_lanes (x : Nat) (h : x < 2 ^ 64) :
    x = lane x 0 + 256 * lane x 1 + 256 ^ 2 * lane x 2 + 256 ^ 3 * lane x 3 + 256 ^ 4 * lane x 4
      + 256 ^ 5 * lane x 5 + 256 ^ 6 * lane x 6 + 256 ^ 7 * lane x 7 := by
  simp only [lane, Nat.reducePow, Nat.pow_zero, Nat.pow_one, Nat.div_one]
  omega

end Lane

open Lane

/-! ## Control bytes -/

/-- The control byte of an empty slot (never full since the last rebuild). -/
@[inline] def EMPTY : UInt8 := 0xFF

/-- The control byte of a tombstone. -/
@[inline] def DELETED : UInt8 := 0x80

/-- A control byte of hashbrown's encoding: EMPTY, DELETED, or a FULL tag below `0x80`. -/
def IsCtrl (b : UInt8) : Prop := b = EMPTY ∨ b = DELETED ∨ b < 0x80

theorem EMPTY_eq : EMPTY = 0xFF := by unfold EMPTY; rfl

theorem DELETED_eq : DELETED = 0x80 := by unfold DELETED; rfl

theorem isCtrl_iff {b : UInt8} : IsCtrl b ↔ b = EMPTY ∨ b = DELETED ∨ b < 0x80 := by
  unfold IsCtrl; exact Iff.rfl

/-- Stated on literals (instances are exposed), so that importing modules can `decide` `IsCtrl`. -/
instance instDecidableIsCtrl (b : UInt8) : Decidable (IsCtrl b) :=
  decidable_of_iff (b = 0xFF ∨ b = 0x80 ∨ b < 0x80) (by rw [isCtrl_iff, EMPTY_eq, DELETED_eq])

theorem DELETED_ne_EMPTY : DELETED ≠ EMPTY := by rw [DELETED_eq, EMPTY_eq]; decide

theorem isCtrl_EMPTY : IsCtrl EMPTY := Or.inl rfl

theorem isCtrl_DELETED : IsCtrl DELETED := Or.inr (Or.inl rfl)

theorem isCtrl_of_lt {b : UInt8} (h : b < 0x80) : IsCtrl b := Or.inr (Or.inr h)

/-! ## Words, bytes and flags -/

/-- `0x01` in every byte. -/
@[inline] def lsbs : UInt64 := 0x0101010101010101

/-- `0x80` in every byte: the flag bits. -/
@[inline] def msbs : UInt64 := 0x8080808080808080

/-- `0x7F` in every byte: the bits below the flags. -/
@[inline] def lows : UInt64 := 0x7F7F7F7F7F7F7F7F

/-- Byte `j < 8` of a word, little-endian. -/
@[inline] def byte (w : UInt64) (j : Nat) : UInt8 := (w >>> (8 * j).toUInt64).toUInt8

/-- The flag of lane `j` of a mask: bit `8 * j + 7`. -/
def flag (m : UInt64) (j : Nat) : Bool := m.toNat.testBit (8 * j + 7)

/-- A mask: every set bit is a flag bit `8 * j + 7`. -/
def IsMask (m : UInt64) : Prop := m &&& lows = 0

theorem lsbs_eq : lsbs = 0x0101010101010101 := by unfold lsbs; rfl

theorem msbs_eq : msbs = 0x8080808080808080 := by unfold msbs; rfl

theorem lows_eq : lows = 0x7F7F7F7F7F7F7F7F := by unfold lows; rfl

theorem byte_def (w : UInt64) (j : Nat) : byte w j = (w >>> (8 * j).toUInt64).toUInt8 := by
  unfold byte; rfl

theorem flag_def (m : UInt64) (j : Nat) : flag m j = m.toNat.testBit (8 * j + 7) := by
  unfold flag; rfl

theorem isMask_iff {m : UInt64} : IsMask m ↔ m &&& 0x7F7F7F7F7F7F7F7F = 0 := by
  unfold IsMask; rw [lows_eq]

/-- Stated on literals (instances are exposed), so that importing modules can `decide` `IsMask`. -/
instance instDecidableIsMask (m : UInt64) : Decidable (IsMask m) :=
  decidable_of_iff (m &&& 0x7F7F7F7F7F7F7F7F = 0) isMask_iff.symm

theorem isMask_zero : IsMask 0 := by rw [isMask_iff]; decide

theorem flag_zero (j : Nat) : flag 0 j = false := by
  rw [flag_def, UInt64.toNat_zero, Nat.zero_testBit]

theorem toNat_byte (w : UInt64) {j : Nat} (hj : j < 8) : (byte w j).toNat = lane w.toNat j := by
  have h64 : 8 * j % 2 ^ 64 % 64 = 8 * j := by omega
  simp only [byte, UInt64.toNat_toUInt8, UInt64.toNat_shiftRight, Nat.toUInt64_eq,
    UInt64.toNat_ofNat', h64, Nat.shiftRight_eq_div_pow, lane, pow256]

/-- `byte` is the masked shift. -/
theorem byte_eq_and (w : UInt64) (j : Nat) :
    (w >>> (8 * j).toUInt64 &&& 0xFF).toUInt8 = byte w j := by
  apply UInt8.toNat_inj.mp
  simp only [byte, UInt64.toNat_toUInt8, UInt64.toNat_and]
  rw [show (0xFF : UInt64).toNat = 2 ^ 8 - 1 from rfl, Nat.and_two_pow_sub_one_eq_mod,
    Nat.mod_mod]

theorem testBit_byte (w : UInt64) {j : Nat} (hj : j < 8) (k : Nat) :
    (byte w j).toNat.testBit k = (decide (k < 8) && w.toNat.testBit (8 * j + k)) := by
  rw [toNat_byte w hj, testBit_lane]

theorem flag_eq_lane (m : UInt64) (j : Nat) : flag m j = (lane m.toNat j).testBit 7 := by
  simp [flag, testBit_lane]

theorem flag_eq_byte (m : UInt64) {j : Nat} (hj : j < 8) :
    flag m j = (byte m j).toNat.testBit 7 := by
  rw [flag_eq_lane, toNat_byte m hj]

/-- No flag beyond lane 7. -/
theorem flag_of_le (m : UInt64) {j : Nat} (hj : 8 ≤ j) : flag m j = false := by
  unfold flag
  apply Nat.testBit_lt_two_pow
  exact Nat.lt_of_lt_of_le m.toNat_lt (Nat.pow_le_pow_right (by decide) (by omega))

theorem byte_ext {w w' : UInt64} (h : ∀ j < 8, byte w j = byte w' j) : w = w' := by
  apply UInt64.toNat_inj.mp
  rw [eq_sum_lanes w.toNat w.toNat_lt, eq_sum_lanes w'.toNat w'.toNat_lt]
  have e : ∀ j < 8, lane w.toNat j = lane w'.toNat j := fun j hj => by
    rw [← toNat_byte w hj, ← toNat_byte w' hj, h j hj]
  rw [e 0 (by decide), e 1 (by decide), e 2 (by decide), e 3 (by decide), e 4 (by decide),
    e 5 (by decide), e 6 (by decide), e 7 (by decide)]

/-! ## The group word -/

theorem add_lit_lt {n : Nat} {i : USize} (h : i.toNat + 8 ≤ n) (k : Nat) (hk : k < 8) :
    (i + USize.ofNat k).toNat < n := by
  rw [USize.toNat_add, USize.toNat_ofNat']
  have : k % 2 ^ System.Platform.numBits = k :=
    Nat.mod_eq_of_lt (Nat.lt_of_lt_of_le (by omega) USize.le_size)
  rw [this]
  exact Nat.lt_of_le_of_lt (Nat.mod_le _ _) (by omega)

/-- The 8 control bytes from `i`, little-endian: byte `j` is `c[i + j]` (`byte_ctrlWord`). Eight
byte loads that clang combines into one unaligned 64-bit load. -/
@[inline] def ctrlWord (c : @& ByteArray) (i : USize) (h : i.toNat + 8 ≤ c.size) : UInt64 :=
  (c.uget i (by omega)).toUInt64 |||
  ((c.uget (i + USize.ofNat 1) (add_lit_lt h 1 (by decide))).toUInt64 <<< 8) |||
  ((c.uget (i + USize.ofNat 2) (add_lit_lt h 2 (by decide))).toUInt64 <<< 16) |||
  ((c.uget (i + USize.ofNat 3) (add_lit_lt h 3 (by decide))).toUInt64 <<< 24) |||
  ((c.uget (i + USize.ofNat 4) (add_lit_lt h 4 (by decide))).toUInt64 <<< 32) |||
  ((c.uget (i + USize.ofNat 5) (add_lit_lt h 5 (by decide))).toUInt64 <<< 40) |||
  ((c.uget (i + USize.ofNat 6) (add_lit_lt h 6 (by decide))).toUInt64 <<< 48) |||
  ((c.uget (i + USize.ofNat 7) (add_lit_lt h 7 (by decide))).toUInt64 <<< 56)

/-- The bytes of 8 bytes placed at shifts `0, 8, …, 56`. -/
theorem lane_shift8 : ∀ b < 256, ∀ s < 8, ∀ j < 8,
    lane ((b <<< (8 * s)) % 2 ^ 64) j = if j = s then b else 0 := by
  decide +kernel

theorem byte_or8 (b₀ b₁ b₂ b₃ b₄ b₅ b₆ b₇ : UInt8) {j : Nat} (hj : j < 8) :
    byte (b₀.toUInt64 ||| (b₁.toUInt64 <<< 8) ||| (b₂.toUInt64 <<< 16) |||
      (b₃.toUInt64 <<< 24) ||| (b₄.toUInt64 <<< 32) ||| (b₅.toUInt64 <<< 40) |||
      (b₆.toUInt64 <<< 48) ||| (b₇.toUInt64 <<< 56)) j =
      [b₀, b₁, b₂, b₃, b₄, b₅, b₆, b₇][j] := by
  apply UInt8.toNat_inj.mp
  rw [toNat_byte _ hj]
  have l : ∀ (b : UInt8) (s sh : Nat), s < 8 → sh = 8 * s →
      lane ((b.toNat <<< sh) % 2 ^ 64) j = if j = s then b.toNat else 0 :=
    fun b s sh hs hsh => hsh ▸ lane_shift8 b.toNat b.toNat_lt s hs j hj
  have l0 : lane b₀.toNat j = if j = 0 then b₀.toNat else 0 := by
    have := l b₀ 0 0 (by decide) rfl
    rwa [Nat.shiftLeft_zero, Nat.mod_eq_of_lt (Nat.lt_trans b₀.toNat_lt
      (by decide))] at this
  simp only [UInt64.toNat_or, UInt64.toNat_shiftLeft, UInt8.toNat_toUInt64, lane_or,
    UInt64.toNat_ofNat, Nat.reducePow, Nat.reduceMod]
  rw [l0, l b₁ 1 8 (by decide) rfl, l b₂ 2 16 (by decide) rfl, l b₃ 3 24 (by decide) rfl,
    l b₄ 4 32 (by decide) rfl, l b₅ 5 40 (by decide) rfl, l b₆ 6 48 (by decide) rfl,
    l b₇ 7 56 (by decide) rfl]
  rcases j with _ | _ | _ | _ | _ | _ | _ | _ | j <;> simp
  omega

private theorem uget_eq_getElem (c : ByteArray) (i : USize) (h : i.toNat < c.size) :
    c.uget i h = c[i.toNat] := by
  cases c; rfl

theorem toNat_add_lit (i : USize) (k : Nat) (hk : k < 8) :
    (i + USize.ofNat k).toNat = (i.toNat + k) % USize.size := by
  rw [USize.toNat_add, USize.toNat_ofNat',
    Nat.mod_eq_of_lt (Nat.lt_of_lt_of_le (by omega : k < 2 ^ 32) USize.le_size)]

/-- Byte `j` of the group word at `i` is `c[i + j]`, the index computed in `USize` (it wraps only
for arrays of `USize.size` bytes or more, which cannot exist; see `byte_ctrlWord'`). -/
theorem byte_ctrlWord (c : ByteArray) (i : USize) (h : i.toNat + 8 ≤ c.size) {j : Nat}
    (hj : j < 8) :
    byte (ctrlWord c i h) j =
      c[(i.toNat + j) % USize.size]'(Nat.lt_of_le_of_lt (Nat.mod_le _ _) (by omega)) := by
  unfold ctrlWord
  rw [byte_or8 _ _ _ _ _ _ _ _ hj]
  have g : ∀ (k : Nat) (hk : k < 8) (hu : (i + USize.ofNat k).toNat < c.size),
      c.uget (i + USize.ofNat k) hu =
        c[(i.toNat + k) % USize.size]'(Nat.lt_of_le_of_lt (Nat.mod_le _ _) (by omega)) :=
    fun k hk hu => by rw [uget_eq_getElem]; congr 1; exact toNat_add_lit i k hk
  have g0 : c.uget i (by omega) =
      c[(i.toNat + 0) % USize.size]'(Nat.lt_of_le_of_lt (Nat.mod_le _ _) (by omega)) := by
    rw [uget_eq_getElem]; congr 1; rw [Nat.add_zero, Nat.mod_eq_of_lt (USize.toNat_lt_size i)]
  rw [g0, g 1 (by decide), g 2 (by decide), g 3 (by decide), g 4 (by decide), g 5 (by decide),
    g 6 (by decide), g 7 (by decide)]
  rcases j with _ | _ | _ | _ | _ | _ | _ | _ | j <;> simp
  all_goals omega

/-- `byte_ctrlWord` when `i + 8` does not wrap. -/
theorem byte_ctrlWord' (c : ByteArray) (i : USize) (h : i.toNat + 8 ≤ c.size)
    (hw : i.toNat + 8 ≤ USize.size) {j : Nat} (hj : j < 8) :
    byte (ctrlWord c i h) j = c[i.toNat + j] := by
  rw [byte_ctrlWord c i h hj]
  congr 1
  exact Nat.mod_eq_of_lt (by omega)

/-! ## Matching a group -/

/-- The byte `t` in every byte of a word. -/
@[inline] def repTag (t : UInt8) : UInt64 := t.toUInt64 * lsbs

/-- The lanes of `g` equal to the byte replicated in `rep`: flag `j` is set exactly when byte `j`
of `g` is `t`, for `rep = repTag t` and every byte `t` (`flag_matchTag`). With `y = g ^^^ rep`,
lane `j` of `y` is zero iff its low 7 bits are zero (`(y &&& lows) + lows` then has bit 7 of the
lane clear; the sum of two lanes below `0x80` never carries into the next lane) and its bit 7 is
zero. -/
@[inline] def matchTag (g rep : UInt64) : UInt64 :=
  let y := g ^^^ rep
  ~~~(((y &&& lows) + lows) ||| y) &&& msbs

/-- The lanes of `g` with bits 7 and 6 set, i.e. at least `0xC0`: for control bytes, EMPTY. -/
@[inline] def matchEmpty (g : UInt64) : UInt64 := g &&& (g <<< 1) &&& msbs

/-- The lanes of `g` with bit 7 set: for control bytes, EMPTY or DELETED. -/
@[inline] def matchFree (g : UInt64) : UInt64 := g &&& msbs

/-- The lanes of `g` with bit 7 clear: for control bytes, FULL. -/
@[inline] def matchFull (g : UInt64) : UInt64 := ~~~g &&& msbs

theorem lane_lows : ∀ j < 8, lane lows.toNat j = 127 := by decide +kernel

theorem testBit_msbs : ∀ j < 8, msbs.toNat.testBit (8 * j + 7) = true := by decide +kernel

theorem testBit_lows : ∀ i < 64, i % 8 ≠ 7 → lows.toNat.testBit i = true := by decide +kernel

theorem msbs_and_lows : msbs &&& lows = 0 := by decide

theorem repTag_eq (t : UInt8) : repTag t = t.toUInt64 * 0x0101010101010101 := by
  unfold repTag; rw [lsbs_eq]

/-- The replicated tag in hashbrown's form `x * lsbs`, for `x < 256`, is `repTag x.toUInt8`. -/
theorem repTag_toUInt8 {x : UInt64} (hx : x < 256) :
    repTag x.toUInt8 = x * 0x0101010101010101 := by
  have hx' : x.toNat < 256 := UInt64.lt_iff_toNat_lt.mp hx
  have e : x.toUInt8.toUInt64 = x := by
    apply UInt64.toNat_inj.mp
    rw [UInt8.toNat_toUInt64, UInt64.toNat_toUInt8, Nat.mod_eq_of_lt hx']
  rw [repTag_eq, e]

theorem and_7F_lt (x : UInt64) : x &&& 0x7F < 256 := by
  rw [UInt64.lt_iff_toNat_lt, UInt64.toNat_and]
  exact Nat.lt_of_le_of_lt Nat.and_le_right (by decide)

/-- The tag `h2 = (q &&& 0x7F).toUInt8` (the core's `tagOf`) is FULL. -/
theorem toUInt8_and_7F_lt (x : UInt64) : (x &&& 0x7F).toUInt8 < 0x80 := by
  rw [UInt8.lt_iff_toNat_lt, UInt64.toNat_toUInt8, UInt64.toNat_and]
  exact Nat.lt_of_le_of_lt (Nat.mod_le _ _) (Nat.lt_of_le_of_lt Nat.and_le_right (by decide))

theorem lane_repTag (t : UInt8) {j : Nat} (hj : j < 8) : lane (repTag t).toNat j = t.toNat := by
  have key : ∀ t < 256, ∀ j < 8, lane (t * lsbs.toNat % 2 ^ 64) j = t := by decide +kernel
  simp only [repTag, UInt64.toNat_mul, UInt8.toNat_toUInt64]
  exact key t.toNat t.toNat_lt j hj

theorem testBit_not (z : UInt64) (i : Nat) :
    (~~~z).toNat.testBit i = (decide (i < 64) && !z.toNat.testBit i) := by
  show (~~~z).toBitVec.toNat.testBit i = _
  rw [UInt64.toBitVec_not, BitVec.testBit_toNat, BitVec.getLsbD_not]; rfl

theorem isMask_and_msbs (x : UInt64) : IsMask (x &&& msbs) := by
  unfold IsMask; rw [UInt64.and_assoc, msbs_and_lows, UInt64.and_zero]

theorem flag_and_msbs (x : UInt64) {j : Nat} (hj : j < 8) : flag (x &&& msbs) j = flag x j := by
  simp only [flag, UInt64.toNat_and, Nat.testBit_and, testBit_msbs j hj, Bool.and_true]

/-- The bits of a mask: only flag bits. -/
theorem testBit_of_isMask {m : UInt64} (hm : IsMask m) (i : Nat) :
    m.toNat.testBit i = (decide (i < 64) && decide (i % 8 = 7) && flag m (i / 8)) := by
  by_cases h64 : i < 64
  · by_cases h7 : i % 8 = 7
    · have : i = 8 * (i / 8) + 7 := by omega
      simp only [h64, h7, decide_true, Bool.true_and, flag]
      rw [← this]
    · have h0 := congrArg (fun x : UInt64 => x.toNat.testBit i) hm
      simp only [UInt64.toNat_and, Nat.testBit_and, testBit_lows i h64 h7, Bool.and_true,
        UInt64.toNat_zero, Nat.zero_testBit] at h0
      simp [h0, h7]
  · simp only [h64, decide_false, Bool.false_and]
    exact Nat.testBit_lt_two_pow
      (Nat.lt_of_lt_of_le m.toNat_lt (Nat.pow_le_pow_right (by decide) (by omega)))

theorem isMask_matchTag (g rep : UInt64) : IsMask (matchTag g rep) := isMask_and_msbs _

theorem isMask_matchEmpty (g : UInt64) : IsMask (matchEmpty g) := isMask_and_msbs _

theorem isMask_matchFree (g : UInt64) : IsMask (matchFree g) := isMask_and_msbs _

theorem isMask_matchFull (g : UInt64) : IsMask (matchFull g) := isMask_and_msbs _

/-- **Exact tag match.** Flag `j` of `matchTag g (repTag t)` is set iff byte `j` of `g` is `t`. -/
theorem flag_matchTag (g : UInt64) (t : UInt8) {j : Nat} (hj : j < 8) :
    flag (matchTag g (repTag t)) j = (byte g j == t) := by
  have key : ∀ v < 256, (!(((v &&& 127) + 127).testBit 7 || v.testBit 7)) = (v == 0) := by
    decide +kernel
  unfold matchTag
  rw [flag_and_msbs _ hj]
  unfold flag
  rw [testBit_not, UInt64.toNat_or, Nat.testBit_or, testBit_eq_lane _ j 7 (by decide),
    testBit_eq_lane (g ^^^ repTag t).toNat j 7 (by decide)]
  have hy : lane (g ^^^ repTag t).toNat j = lane g.toNat j ^^^ t.toNat := by
    rw [UInt64.toNat_xor, lane_xor, lane_repTag t hj]
  have hS : lane (((g ^^^ repTag t) &&& lows) + lows).toNat j =
      (lane (g ^^^ repTag t).toNat j &&& 127) + 127 := by
    rw [UInt64.toNat_add, lane_mod _ _ hj, lane_add]
    · rw [UInt64.toNat_and, lane_and, lane_lows j hj]
    · intro k hk
      rw [UInt64.toNat_and, lane_and, lane_lows k (by omega)]
      have : lane (g ^^^ repTag t).toNat k &&& 127 ≤ 127 := Nat.and_le_right
      omega
  have hv : lane g.toNat j ^^^ t.toNat < 256 :=
    Nat.xor_lt_two_pow (n := 8) (lane_lt _ _) t.toNat_lt
  rw [hS, hy, key _ hv, decide_eq_true (show 8 * j + 7 < 64 by omega), Bool.true_and]
  rw [Bool.eq_iff_iff, beq_iff_eq, beq_iff_eq, xor_eq_zero_iff, ← toNat_byte g hj,
    UInt8.toNat_inj]

/-- Flag `j` of `matchEmpty g` is set iff byte `j` of `g` is at least `0xC0`. -/
theorem flag_matchEmpty (g : UInt64) {j : Nat} (hj : j < 8) :
    flag (matchEmpty g) j = decide (0xC0 ≤ byte g j) := by
  have key : ∀ v < 256, (v.testBit 7 && v.testBit 6) = decide (192 ≤ v) := by decide +kernel
  unfold matchEmpty
  rw [flag_and_msbs _ hj]
  unfold flag
  simp only [UInt64.toNat_and, Nat.testBit_and, UInt64.toNat_shiftLeft, Nat.testBit_mod_two_pow,
    Nat.testBit_shiftLeft]
  simp only [UInt64.toNat_ofNat, Nat.reducePow, Nat.reduceMod]
  rw [show 8 * j + 7 - 1 = 8 * j + 6 by omega, decide_eq_true (show 8 * j + 7 < 64 by omega),
    decide_eq_true (show 8 * j + 7 ≥ 1 by omega), Bool.true_and, Bool.true_and,
    testBit_eq_lane _ j 7 (by decide), testBit_eq_lane _ j 6 (by decide), ← toNat_byte g hj,
    key _ (byte g j).toNat_lt]
  simp [UInt8.le_iff_toNat_le]

/-- Flag `j` of `matchFree g` is set iff byte `j` of `g` is at least `0x80`. -/
theorem flag_matchFree (g : UInt64) {j : Nat} (hj : j < 8) :
    flag (matchFree g) j = decide (0x80 ≤ byte g j) := by
  have key : ∀ v < 256, v.testBit 7 = decide (128 ≤ v) := by decide +kernel
  unfold matchFree
  rw [flag_and_msbs _ hj, flag_eq_byte g hj, key _ (byte g j).toNat_lt]
  simp [UInt8.le_iff_toNat_le]

/-- Flag `j` of `matchFull g` is set iff byte `j` of `g` is below `0x80`. -/
theorem flag_matchFull (g : UInt64) {j : Nat} (hj : j < 8) :
    flag (matchFull g) j = decide (byte g j < 0x80) := by
  have key : ∀ v < 256, (!v.testBit 7) = decide (v < 128) := by decide +kernel
  unfold matchFull
  rw [flag_and_msbs _ hj]
  unfold flag
  rw [testBit_not, decide_eq_true (show 8 * j + 7 < 64 by omega), Bool.true_and,
    testBit_eq_lane _ j 7 (by decide), ← toNat_byte g hj, key _ (byte g j).toNat_lt]
  simp [UInt8.lt_iff_toNat_lt]

theorem isCtrl_le_iff {b : UInt8} (h : IsCtrl b) : 0xC0 ≤ b ↔ b = EMPTY := by
  rcases h with rfl | rfl | h
  · decide
  · decide
  · have : b ≠ EMPTY := by
      intro e; subst e; exact absurd h (by decide)
    simp only [this, iff_false, UInt8.not_le]
    rw [UInt8.lt_iff_toNat_lt] at h ⊢
    exact Nat.lt_trans h (by decide)

theorem isCtrl_free_iff {b : UInt8} (h : IsCtrl b) : 0x80 ≤ b ↔ b = EMPTY ∨ b = DELETED := by
  rcases h with rfl | rfl | h
  · decide
  · decide
  · have h1 : b ≠ EMPTY := by
      intro e; subst e; exact absurd h (by decide)
    have h2 : b ≠ DELETED := by
      intro e; subst e; exact absurd h (by decide)
    simp only [h1, h2, or_self, iff_false, UInt8.not_le]
    exact h

/-- For a control byte, flag `j` of `matchEmpty g` is set iff byte `j` is EMPTY. -/
theorem flag_matchEmpty_ctrl (g : UInt64) {j : Nat} (hj : j < 8) (h : IsCtrl (byte g j)) :
    flag (matchEmpty g) j = (byte g j == EMPTY) := by
  rw [flag_matchEmpty g hj, Bool.eq_iff_iff, decide_eq_true_iff, beq_iff_eq]
  exact isCtrl_le_iff h

/-- For a control byte, flag `j` of `matchFree g` is set iff byte `j` is EMPTY or DELETED. -/
theorem flag_matchFree_ctrl (g : UInt64) {j : Nat} (hj : j < 8) (h : IsCtrl (byte g j)) :
    flag (matchFree g) j = (byte g j == EMPTY || byte g j == DELETED) := by
  rw [flag_matchFree g hj, Bool.eq_iff_iff, decide_eq_true_iff, Bool.or_eq_true, beq_iff_eq,
    beq_iff_eq]
  exact isCtrl_free_iff h

/-- The bits of `matchTag`: bit `i` is set iff `i = 8 * j + 7` with `j < 8` and byte `j` of `g`
is `t`. -/
theorem testBit_matchTag (g : UInt64) (t : UInt8) (i : Nat) :
    (matchTag g (repTag t)).toNat.testBit i =
      (decide (i < 64) && decide (i % 8 = 7) && (byte g (i / 8) == t)) := by
  rw [testBit_of_isMask (isMask_matchTag _ _)]
  by_cases h : i < 64
  · rw [flag_matchTag g t (by omega)]
  · simp [h]

/-! ## The lowest flag -/

/-- `lowestLane` as a `UInt64`: isolate the lowest set bit `2 ^ (8 * j + 7)`, shift it to
`2 ^ (8 * j) = 256 ^ j`, and multiply by `0x0001020304050607`, whose byte `7 - j` is `j`; the top
byte of the product is `j`. -/
@[inline] def lowestLane64 (m : UInt64) : UInt64 :=
  (((m &&& (0 - m)) >>> 7) * 0x0001020304050607) >>> 56

/-- The lane of the lowest flag of a nonzero mask (`lowestLane_spec`), with no loop. -/
@[inline] def lowestLane (m : UInt64) : USize := (lowestLane64 m).toUSize

/-- The mask without its lowest flag (`flag_clearLowest`). -/
@[inline] def clearLowest (m : UInt64) : UInt64 := m &&& (m - 1)

/-- The number with flag bits `f₀ … f₇`. -/
def spread (f₀ f₁ f₂ f₃ f₄ f₅ f₆ f₇ : Bool) : Nat :=
  f₀.toNat * 2 ^ 7 + f₁.toNat * 2 ^ 15 + f₂.toNat * 2 ^ 23 + f₃.toNat * 2 ^ 31 +
  f₄.toNat * 2 ^ 39 + f₅.toNat * 2 ^ 47 + f₆.toNat * 2 ^ 55 + f₇.toNat * 2 ^ 63

/-- A mask is determined by its 8 flags. -/
theorem eq_spread {m : UInt64} (hm : IsMask m) :
    m = UInt64.ofNat (spread (flag m 0) (flag m 1) (flag m 2) (flag m 3) (flag m 4) (flag m 5)
      (flag m 6) (flag m 7)) := by
  have hlt : ∀ f₀ f₁ f₂ f₃ f₄ f₅ f₆ f₇ : Bool,
      spread f₀ f₁ f₂ f₃ f₄ f₅ f₆ f₇ < 2 ^ 64 := by
    decide +kernel
  have key : ∀ v < 256, v &&& 127 = 0 → v = 128 * (v.testBit 7).toNat := by decide +kernel
  apply UInt64.toNat_inj.mp
  rw [UInt64.toNat_ofNat', Nat.mod_eq_of_lt (hlt _ _ _ _ _ _ _ _)]
  have hl : ∀ k < 8, lane m.toNat k = 128 * (flag m k).toNat := by
    intro k hk
    have h0 : lane m.toNat k &&& 127 = 0 := by
      have := congrArg (fun x : UInt64 => lane x.toNat k) hm
      simp only [UInt64.toNat_and, lane_and, lane_lows k hk, UInt64.toNat_zero] at this
      rw [this]; simp [lane]
    rw [flag_eq_lane]
    exact key _ (lane_lt _ _) h0
  have e := eq_sum_lanes m.toNat m.toNat_lt
  rw [hl 0 (by decide), hl 1 (by decide), hl 2 (by decide), hl 3 (by decide), hl 4 (by decide),
    hl 5 (by decide), hl 6 (by decide), hl 7 (by decide)] at e
  rw [e]; unfold spread
  simp only [Nat.reducePow]
  omega

/-- To prove a property of every mask, check its 256 flag patterns (with `decide +kernel`, which
only works in this module: elsewhere the definitions are sealed). -/
theorem forall_mask (P : UInt64 → Prop)
    (h : ∀ f₀ f₁ f₂ f₃ f₄ f₅ f₆ f₇ : Bool,
      P (UInt64.ofNat (spread f₀ f₁ f₂ f₃ f₄ f₅ f₆ f₇)))
    {m : UInt64} (hm : IsMask m) : P m := by
  rw [eq_spread hm]; exact h _ _ _ _ _ _ _ _

/-- Two masks with the same flags are equal. -/
theorem mask_ext {m m' : UInt64} (hm : IsMask m) (hm' : IsMask m')
    (h : ∀ j < 8, flag m j = flag m' j) : m = m' := by
  rw [eq_spread hm, eq_spread hm', h 0 (by decide), h 1 (by decide), h 2 (by decide),
    h 3 (by decide), h 4 (by decide), h 5 (by decide), h 6 (by decide), h 7 (by decide)]

/-- A mask is zero iff it has no flag. -/
theorem isMask_eq_zero_iff {m : UInt64} (hm : IsMask m) : m = 0 ↔ ∀ j < 8, flag m j = false :=
  forall_mask (fun m => m = 0 ↔ ∀ j < 8, flag m j = false) (by decide +kernel) hm

theorem toNat_lowestLane {m : UInt64} (h : (lowestLane64 m).toNat < 8) :
    (lowestLane m).toNat = (lowestLane64 m).toNat := by
  simp only [lowestLane, UInt64.toNat_toUSize]
  exact Nat.mod_eq_of_lt (Nat.lt_of_lt_of_le h (Nat.le_trans (by decide) USize.le_size))

/-- **Lowest flag.** For a nonzero mask, `lowestLane m` is a lane `< 8` whose flag is set, with no
flag below it. -/
theorem lowestLane_spec {m : UInt64} (hm : IsMask m) (h0 : m ≠ 0) :
    (lowestLane m).toNat < 8 ∧ flag m (lowestLane m).toNat = true ∧
      ∀ k < (lowestLane m).toNat, flag m k = false := by
  have := forall_mask (fun m => m ≠ 0 → (lowestLane64 m).toNat < 8 ∧
      flag m (lowestLane64 m).toNat = true ∧
      ∀ k < 8, k < (lowestLane64 m).toNat → flag m k = false)
    (by decide +kernel) hm h0
  obtain ⟨h8, hf, hb⟩ := this
  rw [toNat_lowestLane h8]
  exact ⟨h8, hf, fun k hk => hb k (by omega) hk⟩

theorem isMask_clearLowest {m : UInt64} (hm : IsMask m) : IsMask (clearLowest m) :=
  forall_mask (fun m => IsMask (clearLowest m)) (by decide +kernel) hm

/-- **Clearing the lowest flag** removes exactly flag `lowestLane m`. -/
theorem flag_clearLowest {m : UInt64} (hm : IsMask m) (h0 : m ≠ 0) (k : Nat) :
    flag (clearLowest m) k = (flag m k && k != (lowestLane m).toNat) := by
  have := forall_mask (fun m => m ≠ 0 → (lowestLane64 m).toNat < 8 ∧
      ∀ k < 8, flag (clearLowest m) k = (flag m k && k != (lowestLane64 m).toNat))
    (by decide +kernel) hm h0
  obtain ⟨h8, hc⟩ := this
  rw [toNat_lowestLane h8]
  by_cases hk : k < 8
  · exact hc k hk
  · rw [flag_of_le _ (by omega), flag_of_le _ (by omega), Bool.false_and]

/-- `clearLowest` makes progress: the mask decreases. -/
theorem clearLowest_lt {m : UInt64} (hm : IsMask m) (h0 : m ≠ 0) :
    (clearLowest m).toNat < m.toNat :=
  forall_mask (fun m => m ≠ 0 → (clearLowest m).toNat < m.toNat)
    (by decide +kernel) hm h0

/-- `lowestLane` is a lane of the group for every mask, `0` included, so a slot index computed
from it is in bounds without a test of the mask. -/
theorem lowestLane_lt {m : UInt64} (hm : IsMask m) : (lowestLane m).toNat < 8 := by
  have h8 := forall_mask (fun m => (lowestLane64 m).toNat < 8) (by decide +kernel) hm
  rw [toNat_lowestLane h8]; exact h8

/-- `lowestLane64` is a lane of the group for every mask (the `Nat`-index loops read it). -/
theorem lowestLane64_lt {m : UInt64} (hm : IsMask m) : (lowestLane64 m).toNat < 8 :=
  forall_mask (fun m => (lowestLane64 m).toNat < 8) (by decide +kernel) hm

/-- On masks, `lowestLane` and `lowestLane64` are the same lane. -/
theorem toNat_lowestLane_of_isMask {m : UInt64} (hm : IsMask m) :
    (lowestLane m).toNat = (lowestLane64 m).toNat :=
  toNat_lowestLane (lowestLane64_lt hm)

/-- The lane of the zero mask is `0`. -/
theorem lowestLane_zero : lowestLane 0 = 0 := by
  have h : (lowestLane64 0).toNat = 0 := by decide +kernel
  apply USize.toNat_inj.mp
  rw [toNat_lowestLane (by omega), h, USize.toNat_zero]

/-- The first step of `lowestLane`: `(m &&& (0 - m)) >>> 7`, the lowest flag of a nonzero mask
moved to the bottom of its lane, is `256 ^ lowestLane m`. -/
theorem isolate_shift {m : UInt64} (hm : IsMask m) (h0 : m ≠ 0) :
    ((m &&& (0 - m)) >>> 7).toNat = 256 ^ (lowestLane m).toNat := by
  have := forall_mask (fun m => m ≠ 0 → (lowestLane64 m).toNat < 8 ∧
      ((m &&& (0 - m)) >>> 7).toNat = 256 ^ (lowestLane64 m).toNat) (by decide +kernel) hm h0
  rw [toNat_lowestLane this.1]; exact this.2

/-- A mask is below `256 ^ j` iff it has no flag in lane `j` or above. -/
theorem mask_lt_pow_iff {m : UInt64} (hm : IsMask m) {j : Nat} (hj : j ≤ 8) :
    m.toNat < 256 ^ j ↔ ∀ l < 8, j ≤ l → flag m l = false := by
  have := forall_mask
    (fun m => ∀ j < 9, (m.toNat < 256 ^ j ↔ ∀ l < 8, j ≤ l → flag m l = false))
    (by decide +kernel) hm
  exact this j (by omega)

/-! ## Slot indices in `USize` -/

private theorem toNat_eight : (8 : USize).toNat = 8 := by simp

/-- A power of two `cap ≤ USize.size` divides `USize.size`. -/
theorem dvd_usize_size {cap n : Nat} (hcap : cap = 2 ^ n) (h : cap ≤ USize.size) :
    cap ∣ USize.size := by
  subst hcap
  exact Nat.pow_dvd_pow 2 ((Nat.pow_le_pow_iff_right (by decide)).mp h)

theorem toNat_and_mask {x mask : USize} {cap n : Nat} (hcap : cap = 2 ^ n)
    (hmask : mask.toNat + 1 = cap) : (x &&& mask).toNat = x.toNat % cap := by
  rw [USize.toNat_and, show mask.toNat = 2 ^ n - 1 by omega, Nat.and_two_pow_sub_one_eq_mod, hcap]

/-- The slot `(a + b) &&& mask` of a table of `cap = mask + 1` slots, a power of two. -/
theorem toNat_add_and_mask {a b mask : USize} {cap n : Nat} (hcap : cap = 2 ^ n)
    (hmask : mask.toNat + 1 = cap) : ((a + b) &&& mask).toNat = (a.toNat + b.toNat) % cap := by
  have : cap ≤ USize.size := by have := USize.toNat_lt_size mask; omega
  rw [toNat_and_mask hcap hmask, USize.toNat_add, Nat.mod_mod_of_dvd _ (dvd_usize_size hcap this)]

/-- The slot `(a - b) &&& mask`, for `b ≤ cap`: `a - b` modulo `cap`. -/
theorem toNat_sub_and_mask {a b mask : USize} {cap n : Nat} (hcap : cap = 2 ^ n)
    (hmask : mask.toNat + 1 = cap) (hb : b.toNat ≤ cap) :
    ((a - b) &&& mask).toNat = (a.toNat + (cap - b.toNat)) % cap := by
  have hle : cap ≤ USize.size := by have := USize.toNat_lt_size mask; omega
  have hdvd := dvd_usize_size hcap hle
  obtain ⟨K, hK⟩ := hdvd
  have hK1 : cap ≤ cap * K := by
    rcases K with _ | K
    · rw [Nat.mul_zero] at hK; have := USize.le_size; omega
    · exact Nat.le_mul_of_pos_right _ (by omega)
  have hsub : cap * (K - 1) = cap * K - cap := Nat.mul_sub_one cap K
  have hS : 2 ^ System.Platform.numBits = USize.size := rfl
  rw [toNat_and_mask hcap hmask, USize.toNat_sub, hS, Nat.mod_mod_of_dvd _ ⟨K, hK⟩, hK,
    show cap * K - b.toNat + a.toNat = (a.toNat + (cap - b.toNat)) + cap * (K - 1) by omega,
    Nat.add_mul_mod_self_left]

/-- The index `((i - 8) &&& mask) + 8` that `setCtrl` writes besides `i`: `i + cap` for the first
8 slots (their mirror), `i` itself for the others. -/
theorem toNat_mirrorIdx {i mask : USize} {cap n : Nat} (hcap : cap = 2 ^ n) (h8 : 8 ≤ cap)
    (hmask : mask.toNat + 1 = cap) (hsize : cap < USize.size) (hi : i.toNat < cap) :
    (((i - 8) &&& mask) + 8).toNat = if i.toNat < 8 then i.toNat + cap else i.toNat := by
  -- `USize.size = cap * K` with `K ≥ 2`
  obtain ⟨K, hK⟩ := dvd_usize_size hcap (Nat.le_of_lt hsize)
  have hK2 : cap * 2 ≤ cap * K := by
    apply Nat.mul_le_mul_left
    rcases K with _ | _ | K
    · rw [Nat.mul_zero] at hK; omega
    · rw [Nat.mul_one] at hK; omega
    · omega
  have hsub : cap * (K - 1) = cap * K - cap := Nat.mul_sub_one cap K
  have hS : 2 ^ System.Platform.numBits = USize.size := rfl
  rw [USize.toNat_add, toNat_and_mask hcap hmask, USize.toNat_sub, toNat_eight, hS, hK]
  split
  · have e1 : cap * K - 8 + i.toNat = (cap - 8 + i.toNat) + cap * (K - 1) := by omega
    rw [Nat.mod_eq_of_lt (show cap * K - 8 + i.toNat < cap * K by omega), e1,
      Nat.add_mul_mod_self_left, Nat.mod_eq_of_lt (show cap - 8 + i.toNat < cap by omega),
      Nat.mod_eq_of_lt (show cap - 8 + i.toNat + 8 < cap * K by omega)]
    omega
  · have e1 : cap * K - 8 + i.toNat = (i.toNat - 8) + cap * K * 1 := by omega
    rw [e1, Nat.add_mul_mod_self_left, Nat.mod_eq_of_lt (show i.toNat - 8 < cap * K by omega),
      Nat.mod_eq_of_lt (show i.toNat - 8 < cap by omega),
      Nat.mod_eq_of_lt (show i.toNat - 8 + 8 < cap * K by omega)]
    omega

/-! ## The mirrored control array -/

/-- The control array of a table of `cap` slots: `cap` (a power of two, at least 8) control
bytes, then a copy of the first 8. -/
structure Mirrored (c : ByteArray) (cap : Nat) : Prop where
  size_eq : c.size = cap + 8
  pow_two : ∃ n, cap = 2 ^ n
  le_cap : 8 ≤ cap
  mirror : ∀ j (hj : j < 8), c[cap + j]'(by omega) = c[j]'(by omega)

/-- The control byte of slot `k % cap`. -/
def slotByte (c : ByteArray) (cap k : Nat) : UInt8 := c[k % cap]!

theorem slotByte_def (c : ByteArray) (cap k : Nat) : slotByte c cap k = c[k % cap]! := by
  unfold slotByte; rfl

theorem slotByte_mod (c : ByteArray) (cap k : Nat) :
    slotByte c cap (k % cap) = slotByte c cap k := by
  simp [slotByte]

/-- Every byte of a mirrored control array is the control byte of its slot. -/
theorem Mirrored.getElem_eq {c : ByteArray} {cap : Nat} (h : Mirrored c cap) (x : Nat)
    (hx : x < c.size) : c[x] = slotByte c cap x := by
  have hs := h.size_eq
  have h8 := h.le_cap
  unfold slotByte
  rw [getElem!_pos c (x % cap) (Nat.lt_of_lt_of_le (Nat.mod_lt _ (by omega)) (by omega))]
  by_cases hxc : x < cap
  · simp only [Nat.mod_eq_of_lt hxc]
  · obtain ⟨d, rfl⟩ : ∃ d, x = cap + d := ⟨x - cap, by omega⟩
    have hd : d < 8 := by omega
    have : (cap + d) % cap = d := by
      rw [Nat.add_mod_left, Nat.mod_eq_of_lt (by omega)]
    simp only [this]
    exact h.mirror d hd

theorem Mirrored.lt_size {c : ByteArray} {cap : Nat} (h : Mirrored c cap) {i : USize}
    (hi : i.toNat < cap) : i.toNat < c.size := by
  have := h.size_eq; omega

theorem Mirrored.mask_lt {c : ByteArray} {cap : Nat} (h : Mirrored c cap) {mask : USize}
    (hmask : mask.toNat + 1 = cap) : mask.toNat + 8 < c.size := by
  have := h.size_eq; omega

theorem Mirrored.slotByte_eq {c : ByteArray} {cap : Nat} (h : Mirrored c cap) {k : Nat}
    (hk : k < cap) : slotByte c cap k = c[k]'(by have := h.size_eq; omega) :=
  (h.getElem_eq k _).symm

private theorem size_uset (c : ByteArray) (i : USize) (b : UInt8) (h : i.toNat < c.size) :
    (c.uset i b h).size = c.size := by
  cases c; simp [ByteArray.uset, ByteArray.size]

private theorem getElem_uset (c : ByteArray) (i : USize) (b : UInt8) (h : i.toNat < c.size) (k : Nat)
    (hk : k < c.size) :
    (c.uset i b h)[k]'(by rw [size_uset]; exact hk) = if i.toNat = k then b else c[k] := by
  cases c; simp [ByteArray.uset, ByteArray.getElem_eq_getElem_data, Array.getElem_set]

theorem mirrorIdx_lt {n : Nat} {i mask : USize} (hm : mask.toNat + 8 < n) :
    (((i - 8) &&& mask) + 8).toNat < n := by
  rw [USize.toNat_add, toNat_eight, USize.toNat_and]
  have := Nat.and_le_right (n := (i - 8).toNat) (m := mask.toNat)
  exact Nat.lt_of_le_of_lt (Nat.mod_le _ _) (by omega)

/-- Write control byte `b` of slot `i` and its mirror: the index `((i - 8) &&& mask) + 8` is
`i + cap` when `i < 8` and `i` otherwise (`toNat_mirrorIdx`), so the second write needs no
branch. -/
@[inline] def setCtrl (c : ByteArray) (mask i : USize) (b : UInt8) (hi : i.toNat < c.size)
    (hm : mask.toNat + 8 < c.size) : ByteArray :=
  (c.uset i b hi).uset (((i - 8) &&& mask) + 8) b (by rw [size_uset]; exact mirrorIdx_lt hm)

theorem size_setCtrl (c : ByteArray) (mask i : USize) (b : UInt8) (hi : i.toNat < c.size)
    (hm : mask.toNat + 8 < c.size) : (setCtrl c mask i b hi hm).size = c.size := by
  simp only [setCtrl, size_uset]

theorem getElem_setCtrl (c : ByteArray) (mask i : USize) (b : UInt8) (hi : i.toNat < c.size)
    (hm : mask.toNat + 8 < c.size) (k : Nat) (hk : k < c.size) :
    (setCtrl c mask i b hi hm)[k]'(by rw [size_setCtrl]; exact hk) =
      if (((i - 8) &&& mask) + 8).toNat = k then b else if i.toNat = k then b else c[k] := by
  simp only [setCtrl]
  rw [getElem_uset _ _ _ _ k (by rw [size_uset]; exact hk), getElem_uset _ _ _ _ k hk]

/-- **`setCtrl` keeps the mirror.** -/
theorem mirrored_setCtrl {c : ByteArray} {cap : Nat} (h : Mirrored c cap) {mask i : USize}
    (b : UInt8) (hi : i.toNat < c.size) (hm : mask.toNat + 8 < c.size)
    (hmask : mask.toNat + 1 = cap) (hsize : cap < USize.size) (hic : i.toNat < cap) :
    Mirrored (setCtrl c mask i b hi hm) cap := by
  obtain ⟨n, hcap⟩ := h.pow_two
  have hs := h.size_eq
  have h8 := h.le_cap
  have hidx := toNat_mirrorIdx hcap h8 hmask hsize hic
  refine ⟨by rw [size_setCtrl]; exact hs, h.pow_two, h8, fun j hj => ?_⟩
  rw [getElem_setCtrl _ _ _ _ _ _ _ (by omega), getElem_setCtrl _ _ _ _ _ _ _ (by omega), hidx,
    h.mirror j hj]
  repeat' split
  all_goals first | rfl | omega

/-- **`setCtrl` writes exactly slot `i`**, as seen through `slotByte`. -/
theorem slotByte_setCtrl {c : ByteArray} {cap : Nat} (h : Mirrored c cap) {mask i : USize}
    (b : UInt8) (hi : i.toNat < c.size) (hm : mask.toNat + 8 < c.size)
    (hmask : mask.toNat + 1 = cap) (hsize : cap < USize.size) (hic : i.toNat < cap) (k : Nat) :
    slotByte (setCtrl c mask i b hi hm) cap k =
      if k % cap = i.toNat then b else slotByte c cap k := by
  obtain ⟨n, hcap⟩ := h.pow_two
  have hs := h.size_eq
  have h8 := h.le_cap
  have hidx := toNat_mirrorIdx hcap h8 hmask hsize hic
  have hkc : k % cap < cap := Nat.mod_lt _ (by omega)
  rw [← slotByte_mod, (mirrored_setCtrl h b hi hm hmask hsize hic).slotByte_eq hkc,
    getElem_setCtrl _ _ _ _ _ _ _ (by omega), hidx, ← slotByte_mod c, h.slotByte_eq hkc]
  repeat' split
  all_goals first | rfl | omega

/-- **The group word under the mirror.** Byte `j` of the group word at `p` (a slot, so that
`p + 8 ≤ cap + 8`: `Mirrored.group_bound`) is the control byte of slot `(p + j) % cap`. -/
theorem byte_ctrlWord_of_mirrored {c : ByteArray} {cap : Nat} (h : Mirrored c cap)
    (hcap : cap ≤ USize.size) {p : USize} (hw : p.toNat + 8 ≤ c.size)
    {j : Nat} (hj : j < 8) :
    byte (ctrlWord c p hw) j = slotByte c cap ((p.toNat + j) % cap) := by
  obtain ⟨n, hpow⟩ := h.pow_two
  rw [byte_ctrlWord c p hw hj, h.getElem_eq, ← slotByte_mod c cap,
    Nat.mod_mod_of_dvd _ (dvd_usize_size hpow hcap), slotByte_mod]

theorem Mirrored.group_bound {c : ByteArray} {cap : Nat} (h : Mirrored c cap) {p : USize}
    (hp : p.toNat < cap) : p.toNat + 8 ≤ c.size := by
  have := h.size_eq; omega

/-- Tag match of the group at `p`: flag `j` iff slot `(p + j) % cap` holds `t`. -/
theorem flag_matchTag_ctrlWord {c : ByteArray} {cap : Nat} (h : Mirrored c cap)
    (hcap : cap ≤ USize.size) {p : USize} (hw : p.toNat + 8 ≤ c.size) (t : UInt8) {j : Nat}
    (hj : j < 8) :
    flag (matchTag (ctrlWord c p hw) (repTag t)) j =
      (slotByte c cap ((p.toNat + j) % cap) == t) := by
  rw [flag_matchTag _ t hj, byte_ctrlWord_of_mirrored h hcap hw hj]

/-- Empty match of the group at `p`, for a control array of control bytes. -/
theorem flag_matchEmpty_ctrlWord {c : ByteArray} {cap : Nat} (h : Mirrored c cap)
    (hcap : cap ≤ USize.size) (hctrl : ∀ k < cap, IsCtrl (slotByte c cap k)) {p : USize}
    (hw : p.toNat + 8 ≤ c.size) {j : Nat} (hj : j < 8) :
    flag (matchEmpty (ctrlWord c p hw)) j =
      (slotByte c cap ((p.toNat + j) % cap) == EMPTY) := by
  have hb := byte_ctrlWord_of_mirrored h hcap hw hj
  have h8 := h.le_cap
  rw [flag_matchEmpty_ctrl _ hj (by rw [hb]; exact hctrl _ (Nat.mod_lt _ (by omega))), hb]

/-- Free match of the group at `p`, for a control array of control bytes. -/
theorem flag_matchFree_ctrlWord {c : ByteArray} {cap : Nat} (h : Mirrored c cap)
    (hcap : cap ≤ USize.size) (hctrl : ∀ k < cap, IsCtrl (slotByte c cap k)) {p : USize}
    (hw : p.toNat + 8 ≤ c.size) {j : Nat} (hj : j < 8) :
    flag (matchFree (ctrlWord c p hw)) j =
      (slotByte c cap ((p.toNat + j) % cap) == EMPTY ||
        slotByte c cap ((p.toNat + j) % cap) == DELETED) := by
  have hb := byte_ctrlWord_of_mirrored h hcap hw hj
  have h8 := h.le_cap
  rw [flag_matchFree_ctrl _ hj (by rw [hb]; exact hctrl _ (Nat.mod_lt _ (by omega))), hb]

/-- Full match of the group at `p`: flag `j` iff slot `(p + j) % cap` is below `0x80`. -/
theorem flag_matchFull_ctrlWord {c : ByteArray} {cap : Nat} (h : Mirrored c cap)
    (hcap : cap ≤ USize.size) {p : USize} (hw : p.toNat + 8 ≤ c.size) {j : Nat} (hj : j < 8) :
    flag (matchFull (ctrlWord c p hw)) j =
      decide (slotByte c cap ((p.toNat + j) % cap) < 0x80) := by
  rw [flag_matchFull _ hj, byte_ctrlWord_of_mirrored h hcap hw hj]

/-- No slot of the group at `p` holds `t` iff its tag mask is zero. -/
theorem matchTag_ctrlWord_eq_zero_iff {c : ByteArray} {cap : Nat} (h : Mirrored c cap)
    (hcap : cap ≤ USize.size) {p : USize} (hw : p.toNat + 8 ≤ c.size) (t : UInt8) :
    matchTag (ctrlWord c p hw) (repTag t) = 0 ↔
      ∀ j < 8, slotByte c cap ((p.toNat + j) % cap) ≠ t := by
  rw [isMask_eq_zero_iff (isMask_matchTag _ _)]
  constructor
  · intro H j hj
    have := H j hj
    rwa [flag_matchTag_ctrlWord h hcap hw t hj, beq_eq_false_iff_ne] at this
  · intro H j hj
    rw [flag_matchTag_ctrlWord h hcap hw t hj, beq_eq_false_iff_ne]
    exact H j hj

/-- No slot of the group at `p` is EMPTY iff its empty mask is zero. -/
theorem matchEmpty_ctrlWord_eq_zero_iff {c : ByteArray} {cap : Nat} (h : Mirrored c cap)
    (hcap : cap ≤ USize.size) (hctrl : ∀ k < cap, IsCtrl (slotByte c cap k)) {p : USize}
    (hw : p.toNat + 8 ≤ c.size) :
    matchEmpty (ctrlWord c p hw) = 0 ↔
      ∀ j < 8, slotByte c cap ((p.toNat + j) % cap) ≠ EMPTY := by
  rw [isMask_eq_zero_iff (isMask_matchEmpty _)]
  constructor
  · intro H j hj
    have := H j hj
    rwa [flag_matchEmpty_ctrlWord h hcap hctrl hw hj, beq_eq_false_iff_ne] at this
  · intro H j hj
    rw [flag_matchEmpty_ctrlWord h hcap hctrl hw hj, beq_eq_false_iff_ne]
    exact H j hj

/-- No slot of the group at `p` is EMPTY or DELETED iff its free mask is zero. -/
theorem matchFree_ctrlWord_eq_zero_iff {c : ByteArray} {cap : Nat} (h : Mirrored c cap)
    (hcap : cap ≤ USize.size) (hctrl : ∀ k < cap, IsCtrl (slotByte c cap k)) {p : USize}
    (hw : p.toNat + 8 ≤ c.size) :
    matchFree (ctrlWord c p hw) = 0 ↔
      ∀ j < 8, slotByte c cap ((p.toNat + j) % cap) ≠ EMPTY ∧
        slotByte c cap ((p.toNat + j) % cap) ≠ DELETED := by
  rw [isMask_eq_zero_iff (isMask_matchFree _)]
  constructor
  · intro H j hj
    have := H j hj
    rwa [flag_matchFree_ctrlWord h hcap hctrl hw hj, Bool.or_eq_false_iff, beq_eq_false_iff_ne,
      beq_eq_false_iff_ne] at this
  · intro H j hj
    rw [flag_matchFree_ctrlWord h hcap hctrl hw hj, Bool.or_eq_false_iff, beq_eq_false_iff_ne,
      beq_eq_false_iff_ne]
    exact H j hj

/-- No slot of the group at `p` is FULL (below `0x80`) iff its full mask is zero. -/
theorem matchFull_ctrlWord_eq_zero_iff {c : ByteArray} {cap : Nat} (h : Mirrored c cap)
    (hcap : cap ≤ USize.size) {p : USize} (hw : p.toNat + 8 ≤ c.size) :
    matchFull (ctrlWord c p hw) = 0 ↔
      ∀ j < 8, ¬ slotByte c cap ((p.toNat + j) % cap) < 0x80 := by
  rw [isMask_eq_zero_iff (isMask_matchFull _)]
  constructor
  · intro H j hj
    have := H j hj
    rwa [flag_matchFull_ctrlWord h hcap hw hj, decide_eq_false_iff_not] at this
  · intro H j hj
    rw [flag_matchFull_ctrlWord h hcap hw hj, decide_eq_false_iff_not]
    exact H j hj

/-! ## The table geometry -/

/-- The geometry of a table, as a core keeps it in its invariant: `cap = mask + 1` slots, a power
of two, at least 8 and below `USize.size`. The last bound makes the mirror index of `setCtrl` and
`i + 8` free of wrapping; it must come from the core's allocation (core Lean bounds no array size
by `USize.size`). -/
structure Geom (cap : Nat) (mask : USize) : Prop where
  mask_add_one : mask.toNat + 1 = cap
  pow_two : ∃ n, cap = 2 ^ n
  le_cap : 8 ≤ cap
  lt_size : cap < USize.size

theorem Geom.cap_le_size {cap : Nat} {mask : USize} (hg : Geom cap mask) : cap ≤ USize.size :=
  Nat.le_of_lt hg.lt_size

theorem Geom.toNat_and_mask {cap : Nat} {mask : USize} (hg : Geom cap mask) (x : USize) :
    (x &&& mask).toNat = x.toNat % cap :=
  let ⟨_, hcap⟩ := hg.pow_two
  SwissTable.Core.Swiss.toNat_and_mask hcap hg.mask_add_one

theorem Geom.and_mask_lt {cap : Nat} {mask : USize} (hg : Geom cap mask) (x : USize) :
    (x &&& mask).toNat < cap := by
  rw [hg.toNat_and_mask]; exact Nat.mod_lt _ (by have := hg.le_cap; omega)

theorem Geom.toNat_add_and_mask {cap : Nat} {mask : USize} (hg : Geom cap mask) (a b : USize) :
    ((a + b) &&& mask).toNat = (a.toNat + b.toNat) % cap :=
  let ⟨_, hcap⟩ := hg.pow_two
  SwissTable.Core.Swiss.toNat_add_and_mask hcap hg.mask_add_one

theorem Geom.toNat_sub_and_mask {cap : Nat} {mask : USize} (hg : Geom cap mask) (a : USize)
    {b : USize} (hb : b.toNat ≤ cap) :
    ((a - b) &&& mask).toNat = (a.toNat + (cap - b.toNat)) % cap :=
  let ⟨_, hcap⟩ := hg.pow_two
  SwissTable.Core.Swiss.toNat_sub_and_mask hcap hg.mask_add_one hb

/-- The group before slot `i`, as the erase rule reads it: `(i - 8) &&& mask` is
`(i + cap - 8) % cap`. -/
theorem Geom.toNat_sub_eight_and_mask {cap : Nat} {mask : USize} (hg : Geom cap mask)
    (i : USize) : ((i - 8) &&& mask).toNat = (i.toNat + (cap - 8)) % cap := by
  rw [hg.toNat_sub_and_mask i (by rw [toNat_eight]; exact hg.le_cap), toNat_eight]

theorem Geom.mirrored_setCtrl {c : ByteArray} {cap : Nat} {mask i : USize} (hg : Geom cap mask)
    (h : Mirrored c cap) (b : UInt8) (hi : i.toNat < c.size) (hm : mask.toNat + 8 < c.size)
    (hic : i.toNat < cap) : Mirrored (setCtrl c mask i b hi hm) cap :=
  SwissTable.Core.Swiss.mirrored_setCtrl h b hi hm hg.mask_add_one hg.lt_size hic

theorem Geom.slotByte_setCtrl {c : ByteArray} {cap : Nat} {mask i : USize} (hg : Geom cap mask)
    (h : Mirrored c cap) (b : UInt8) (hi : i.toNat < c.size) (hm : mask.toNat + 8 < c.size)
    (hic : i.toNat < cap) (k : Nat) :
    slotByte (setCtrl c mask i b hi hm) cap k =
      if k % cap = i.toNat then b else slotByte c cap k :=
  SwissTable.Core.Swiss.slotByte_setCtrl h b hi hm hg.mask_add_one hg.lt_size hic k

/-! ## The erase rule -/

/-- **The erase rule** (hashbrown's): whether erasing the full slot `i` must write DELETED rather
than EMPTY, from `ea` and `eb`, the EMPTY masks of the groups at `i` (slots `i … i + 7`) and at
`(i - 8) &&& mask` (slots `i - 8 … i - 1`). A probe passes over an 8-slot window only when the
window has no EMPTY slot, so EMPTY is safe exactly when every window containing `i` already has
one. hashbrown tests `leading_zeros eb + trailing_zeros ea ≥ 8` (in lanes); this is the same test
without counting: `ea` has no flag, or every flag of `eb` is in a lane below the lowest flag of
`ea` (`needsTombstone_eq_false_iff`). -/
@[inline] def needsTombstone (ea eb : UInt64) : Bool := ea == 0 || eb < (ea &&& (0 - ea)) >>> 7

theorem needsTombstone_eq (ea eb : UInt64) :
    needsTombstone ea eb = (ea == 0 || eb < (ea &&& (0 - ea)) >>> 7) := by
  unfold needsTombstone; rfl

/-- **The erase rule, on masks.** When `needsTombstone ea eb = false`, every window `d < 8`
(lanes `8 - d … 7` of `eb`, then lanes `0 … 7 - d` of `ea`) has a flag (no bound on `d` is
needed). -/
theorem window_of_needsTombstone_eq_false {ea eb : UInt64} (hea : IsMask ea) (heb : IsMask eb)
    (h : needsTombstone ea eb = false) (d : Nat) :
    (∃ l < 8, 8 ≤ l + d ∧ flag eb l = true) ∨ (∃ l < 8, l + d < 8 ∧ flag ea l = true) := by
  rw [needsTombstone_eq, Bool.or_eq_false_iff, beq_eq_false_iff_ne, decide_eq_false_iff_not] at h
  obtain ⟨h0, hlt⟩ := h
  obtain ⟨ha8, haf, -⟩ := lowestLane_spec hea h0
  have hb : ¬ ∀ l < 8, (lowestLane ea).toNat ≤ l → flag eb l = false := by
    rw [← mask_lt_pow_iff heb (by omega), ← isolate_shift hea h0]
    exact fun h' => hlt (UInt64.lt_iff_toNat_lt.mpr h')
  by_cases had : (lowestLane ea).toNat + d < 8
  · exact Or.inr ⟨_, ha8, had, haf⟩
  · refine Or.inl (Classical.byContradiction fun hne => hb fun l hl hal => ?_)
    cases hf : flag eb l
    · rfl
    · exact absurd ⟨l, hl, by omega, hf⟩ hne

/-- **The erase rule is hashbrown's**: when lane 0 of `ea` (slot `i` itself, which is full) has no
flag, `needsTombstone ea eb = false` iff every window `d < 8` has a flag. -/
theorem needsTombstone_eq_false_iff {ea eb : UInt64} (hea : IsMask ea) (heb : IsMask eb)
    (h0 : flag ea 0 = false) :
    needsTombstone ea eb = false ↔ ∀ d < 8,
      (∃ l < 8, 8 ≤ l + d ∧ flag eb l = true) ∨ (∃ l < 8, l + d < 8 ∧ flag ea l = true) := by
  refine ⟨fun h d _ => window_of_needsTombstone_eq_false hea heb h d, fun hw => ?_⟩
  rw [needsTombstone_eq, Bool.or_eq_false_iff, beq_eq_false_iff_ne, decide_eq_false_iff_not]
  have hne : ea ≠ 0 := by
    rintro rfl
    rcases hw 0 (by decide) with ⟨l, hl, h8, -⟩ | ⟨l, -, -, hf⟩
    · omega
    · rw [flag_zero] at hf; exact Bool.false_ne_true hf
  refine ⟨hne, fun hlt => ?_⟩
  obtain ⟨ha8, haf, hmin⟩ := lowestLane_spec hea hne
  have ha1 : 1 ≤ (lowestLane ea).toNat := by
    refine Nat.pos_of_ne_zero fun h => ?_
    rw [h, h0] at haf; exact Bool.false_ne_true haf
  have hall := (mask_lt_pow_iff heb (Nat.le_of_lt ha8)).mp
    (by rw [← isolate_shift hea hne]; exact UInt64.lt_iff_toNat_lt.mp hlt)
  rcases hw (8 - (lowestLane ea).toNat) (by omega) with ⟨l, hl, h8, hf⟩ | ⟨l, hl, h8, hf⟩
  · rw [hall l hl (by omega)] at hf; exact Bool.false_ne_true hf
  · rw [hmin l (by omega)] at hf; exact Bool.false_ne_true hf

/-- **The erase rule, on slots.** When `needsTombstone` is `false` for the EMPTY masks of the
groups at `i` and at `(i - 8) &&& mask`, every 8-slot window containing slot `i` (the group at any
`p` with `(p + l₀) % cap = i`, `l₀ < 8`) already has an EMPTY slot. So writing EMPTY at `i`
cannot stop a probe early: a window that a probe passed before the erase had no EMPTY slot, so it
does not contain `i`. -/
theorem exists_empty_of_needsTombstone_eq_false {c : ByteArray} {cap : Nat} {mask i : USize}
    (h : Mirrored c cap) (hg : Geom cap mask) (hctrl : ∀ k < cap, IsCtrl (slotByte c cap k))
    (hw : i.toNat + 8 ≤ c.size) (hw' : ((i - 8) &&& mask).toNat + 8 ≤ c.size)
    (hrule : needsTombstone (matchEmpty (ctrlWord c i hw))
      (matchEmpty (ctrlWord c ((i - 8) &&& mask) hw')) = false)
    {p l₀ : Nat} (hl₀ : l₀ < 8) (hp : (p + l₀) % cap = i.toNat) :
    ∃ l < 8, slotByte c cap ((p + l) % cap) = EMPTY := by
  have h8 := hg.le_cap
  have hcs := hg.cap_le_size
  rcases window_of_needsTombstone_eq_false (isMask_matchEmpty _) (isMask_matchEmpty _) hrule l₀
    with ⟨l, hl, hle, hf⟩ | ⟨l, hl, hlt, hf⟩
  · refine ⟨l + l₀ - 8, by omega, ?_⟩
    rw [flag_matchEmpty_ctrlWord h hcs hctrl hw' hl, beq_iff_eq, hg.toNat_sub_eight_and_mask,
      Nat.mod_add_mod] at hf
    rw [← Nat.add_mod_right (p + (l + l₀ - 8)) cap,
      show p + (l + l₀ - 8) + cap = (p + l₀) + (cap - 8 + l) by omega,
      ← Nat.mod_add_mod (p + l₀) cap (cap - 8 + l), hp, ← Nat.add_assoc]
    exact hf
  · refine ⟨l + l₀, by omega, ?_⟩
    rw [flag_matchEmpty_ctrlWord h hcs hctrl hw hl, beq_iff_eq] at hf
    rw [show p + (l + l₀) = (p + l₀) + l by omega, ← Nat.mod_add_mod (p + l₀) cap l, hp]
    exact hf

/-! ## Triangular probing over groups -/

/-- `0 + 1 + ⋯ + k`. -/
def tri (k : Nat) : Nat := k * (k + 1) / 2

theorem tri_def (k : Nat) : tri k = k * (k + 1) / 2 := by unfold tri; rfl

theorem tri_zero : tri 0 = 0 := by simp [tri]

theorem tri_succ (k : Nat) : tri (k + 1) = tri k + (k + 1) := by
  unfold tri
  rw [show (k + 1) * (k + 1 + 1) = k * (k + 1) + (k + 1) * 2 by grind,
    Nat.add_mul_div_right _ _ (by decide)]

theorem two_mul_tri (k : Nat) : 2 * tri k = k * (k + 1) := by
  induction k with
  | zero => simp [tri]
  | succ k ih => rw [tri_succ, Nat.mul_add, ih]; grind

/-- The start of group `k` of the triangular probe from slot `p₀`: `p₀ + 8 * (0 + 1 + ⋯ + k)`
modulo `cap`. -/
def probePos (cap p₀ k : Nat) : Nat := (p₀ + 8 * tri k) % cap

theorem probePos_def (cap p₀ k : Nat) : probePos cap p₀ k = (p₀ + 8 * tri k) % cap := by
  unfold probePos; rfl

theorem probePos_zero (cap p₀ : Nat) : probePos cap p₀ 0 = p₀ % cap := by
  simp [probePos, tri_zero]

theorem probePos_lt {cap : Nat} (h : 0 < cap) (p₀ k : Nat) : probePos cap p₀ k < cap :=
  Nat.mod_lt _ h

theorem probePos_succ (cap p₀ k : Nat) :
    probePos cap p₀ (k + 1) = (probePos cap p₀ k + 8 * (k + 1)) % cap := by
  unfold probePos
  rw [Nat.mod_add_mod, tri_succ, Nat.mul_add, Nat.add_assoc]

/-- **One probe step in `USize`**, as the core computes it: from the group `pos` of step `k`
with `stride = 8 * k`, `stride + 8` and `(pos + (stride + 8)) &&& mask` are those of step
`k + 1`. -/
theorem probe_step {pos stride mask : USize} {cap n p₀ k : Nat} (hcap : cap = 2 ^ n)
    (hmask : mask.toNat + 1 = cap) (hpos : pos.toNat = probePos cap p₀ k)
    (hstride : stride.toNat = 8 * k) (hk : 8 * (k + 1) < USize.size) :
    (stride + 8).toNat = 8 * (k + 1) ∧
      ((pos + (stride + 8)) &&& mask).toNat = probePos cap p₀ (k + 1) := by
  have hs : (stride + 8).toNat = 8 * (k + 1) := by
    rw [USize.toNat_add, toNat_eight, hstride, Nat.mod_eq_of_lt (by omega)]; omega
  refine ⟨hs, ?_⟩
  rw [toNat_add_and_mask hcap hmask, hpos, hs, probePos_succ]

/-- `probe_step` over the table geometry. -/
theorem Geom.probe_step {cap : Nat} {mask pos stride : USize} {p₀ k : Nat} (hg : Geom cap mask)
    (hpos : pos.toNat = probePos cap p₀ k) (hstride : stride.toNat = 8 * k)
    (hk : 8 * (k + 1) < USize.size) :
    (stride + 8).toNat = 8 * (k + 1) ∧
      ((pos + (stride + 8)) &&& mask).toNat = probePos cap p₀ (k + 1) :=
  let ⟨_, hcap⟩ := hg.pow_two
  SwissTable.Core.Swiss.probe_step hcap hg.mask_add_one hpos hstride hk

/-- An odd factor does not help divide by a power of two. -/
private theorem pow_two_dvd_of_odd_mul {u : Nat} (hu : u % 2 = 1) :
    ∀ {n v : Nat}, 2 ^ n ∣ u * v → 2 ^ n ∣ v
  | 0, v, _ => by simp
  | n + 1, v, h => by
    have h2 : 2 ∣ u * v := Nat.dvd_trans ⟨2 ^ n, by rw [Nat.pow_succ, Nat.mul_comm]⟩ h
    have hv : v % 2 = 0 := by
      have := Nat.mod_eq_zero_of_dvd h2
      rwa [Nat.mul_mod, hu, Nat.one_mul, Nat.mod_mod] at this
    obtain ⟨w, rfl⟩ := Nat.dvd_of_mod_eq_zero hv
    have hw : 2 ^ n ∣ u * w := by
      rw [Nat.pow_succ, Nat.mul_comm (2 ^ n) 2, show u * (2 * w) = 2 * (u * w) by grind] at h
      exact Nat.dvd_of_mul_dvd_mul_left (by decide) h
    rw [Nat.pow_succ, Nat.mul_comm (2 ^ n) 2]
    exact Nat.mul_dvd_mul_left 2 (pow_two_dvd_of_odd_mul hu hw)

/-- Distinct triangular numbers below `2 ^ m` differ modulo `2 ^ m`. -/
theorem tri_mod_ne {m a b : Nat} (hab : a < b) (hb : b < 2 ^ m) :
    tri a % 2 ^ m ≠ tri b % 2 ^ m := by
  intro h
  obtain ⟨d, rfl⟩ : ∃ d, b = a + d := ⟨b - a, by omega⟩
  have hd : 0 < d := by omega
  have h2 : 2 * tri (a + d) = 2 * tri a + d * (2 * a + d + 1) := by
    rw [two_mul_tri, two_mul_tri]; grind
  have hle : tri a ≤ tri (a + d) := by omega
  have hD : 2 ^ m ∣ tri (a + d) - tri a :=
    Nat.dvd_of_mod_eq_zero (Nat.sub_mod_eq_zero_of_mod_eq h.symm)
  have hD2 : 2 ^ (m + 1) ∣ d * (2 * a + d + 1) := by
    have : d * (2 * a + d + 1) = 2 * (tri (a + d) - tri a) := by omega
    rw [this, Nat.pow_succ, Nat.mul_comm (2 ^ m) 2]
    exact Nat.mul_dvd_mul_left 2 hD
  have hpow : 2 ^ (m + 1) = 2 * 2 ^ m := by rw [Nat.pow_succ, Nat.mul_comm]
  rcases Nat.mod_two_eq_zero_or_one d with hdp | hdp
  · have he : (2 * a + d + 1) % 2 = 1 := by omega
    have := Nat.le_of_dvd hd
      (pow_two_dvd_of_odd_mul he (by rwa [Nat.mul_comm] at hD2))
    omega
  · have := Nat.le_of_dvd (by omega) (pow_two_dvd_of_odd_mul hdp hD2)
    omega

theorem tri_mod_inj {m a b : Nat} (ha : a < 2 ^ m) (hb : b < 2 ^ m)
    (h : tri a % 2 ^ m = tri b % 2 ^ m) : a = b := by
  rcases Nat.lt_trichotomy a b with hab | hab | hab
  · exact absurd h (tri_mod_ne hab hb)
  · exact hab
  · exact absurd h.symm (tri_mod_ne hab ha)

theorem cap_facts {cap n : Nat} (hcap : cap = 2 ^ n) (h8 : 8 ≤ cap) :
    cap = 8 * (cap / 8) ∧ cap / 8 = 2 ^ (n - 3) := by
  have hn : 3 ≤ n := by
    rw [hcap] at h8; exact (Nat.pow_le_pow_iff_right (by decide : 1 < 2)).mp h8
  have hd : cap / 8 = 2 ^ (n - 3) := by
    rw [hcap, show (8 : Nat) = 2 ^ 3 from rfl, Nat.pow_div hn (by decide)]
  refine ⟨?_, hd⟩
  rw [hd, hcap, show (8 : Nat) = 2 ^ 3 from rfl, ← Nat.pow_add]
  congr 1; omega

/-- Slot `j` of group `k`, with the group offset reduced. -/
theorem probe_slot_eq {cap n : Nat} (hcap : cap = 2 ^ n) (h8 : 8 ≤ cap) (p₀ k j : Nat) :
    (probePos cap p₀ k + j) % cap = (p₀ + (8 * (tri k % (cap / 8)) + j)) % cap := by
  obtain ⟨h8G, -⟩ := cap_facts hcap h8
  unfold probePos
  rw [Nat.mod_add_mod]
  have e : p₀ + 8 * tri k + j =
      p₀ + (8 * (tri k % (cap / 8)) + j) + cap * (tri k / (cap / 8)) := by
    have := Nat.div_add_mod (tri k) (cap / 8)
    have e2 : cap * (tri k / (cap / 8)) = 8 * ((cap / 8) * (tri k / (cap / 8))) := by
      rw [← Nat.mul_assoc, ← h8G]
    omega
  rw [e, Nat.add_mul_mod_self_left]

private theorem mod_two_cases {x cap : Nat} (hx : x < 2 * cap) :
    x % cap = if x < cap then x else x - cap := by
  split
  · exact Nat.mod_eq_of_lt ‹_›
  · rw [Nat.mod_eq_sub_mod (by omega), Nat.mod_eq_of_lt (by omega)]

private theorem add_mod_inj {cap p o₁ o₂ : Nat} (h₁ : o₁ < cap) (h₂ : o₂ < cap)
    (h : (p + o₁) % cap = (p + o₂) % cap) : o₁ = o₂ := by
  have hc : 0 < cap := by omega
  have e : ∀ o < cap, (p + o) % cap = (p % cap + o) % cap := fun o ho => by
    rw [Nat.add_mod, Nat.mod_eq_of_lt ho]
  rw [e o₁ h₁, e o₂ h₂] at h
  have hr := Nat.mod_lt p hc
  generalize p % cap = r at h hr
  rw [mod_two_cases (x := r + o₁) (by omega), mod_two_cases (x := r + o₂) (by omega)] at h
  split at h <;> split at h <;> omega

/-- **Uniqueness.** The first `cap / 8` groups of a probe are disjoint: a slot is lane `j` of
group `k` for at most one `(k, j)`. -/
theorem probe_unique {cap n p₀ k₁ k₂ j₁ j₂ : Nat} (hcap : cap = 2 ^ n) (h8 : 8 ≤ cap)
    (hk₁ : k₁ < cap / 8) (hk₂ : k₂ < cap / 8) (hj₁ : j₁ < 8) (hj₂ : j₂ < 8)
    (h : (probePos cap p₀ k₁ + j₁) % cap = (probePos cap p₀ k₂ + j₂) % cap) :
    k₁ = k₂ ∧ j₁ = j₂ := by
  obtain ⟨h8G, hG⟩ := cap_facts hcap h8
  rw [probe_slot_eq hcap h8, probe_slot_eq hcap h8] at h
  have hr₁ := Nat.mod_lt (tri k₁) (show 0 < cap / 8 by omega)
  have hr₂ := Nat.mod_lt (tri k₂) (show 0 < cap / 8 by omega)
  have ho := add_mod_inj (by omega) (by omega) h
  have hj : j₁ = j₂ := by omega
  have ht : tri k₁ % (cap / 8) = tri k₂ % (cap / 8) := by omega
  rw [hG] at ht hk₁ hk₂
  exact ⟨tri_mod_inj hk₁ hk₂ ht, hj⟩

/-- An injective map of `[0, n)` into itself is onto. -/
private theorem exists_eq_of_injOn {n : Nat} (f : Nat → Nat) (hf : ∀ x < n, f x < n)
    (hinj : ∀ x < n, ∀ y < n, f x = f y → x = y) {s : Nat} (hs : s < n) :
    ∃ x < n, f x = s := by
  refine Classical.byContradiction fun hne => ?_
  have hnd : ((List.range n).map f).Nodup := by
    unfold List.Nodup
    rw [List.pairwise_map]
    exact List.Pairwise.imp_of_mem (fun ha hb hab heq =>
      hab (hinj _ (List.mem_range.mp ha) _ (List.mem_range.mp hb) heq)) List.nodup_range
  have hns : s ∉ (List.range n).map f := by
    intro hm
    obtain ⟨x, hx, rfl⟩ := List.mem_map.mp hm
    exact hne ⟨x, List.mem_range.mp hx, rfl⟩
  have hsub : s :: (List.range n).map f ⊆ List.range n := by
    intro y hy
    rcases List.mem_cons.mp hy with rfl | hy
    · exact List.mem_range.mpr hs
    · obtain ⟨x, hx, rfl⟩ := List.mem_map.mp hy
      exact List.mem_range.mpr (hf x (List.mem_range.mp hx))
  have := (List.nodup_cons.mpr ⟨hns, hnd⟩).length_le_of_subset hsub
  simp only [List.length_cons, List.length_map, List.length_range] at this
  omega

/-- **Coverage.** For `cap` a power of two, at least 8, the first `cap / 8` groups of the probe
from any `p₀` cover every slot: slot `s` is lane `j` of group `k` for some `k < cap / 8` and
`j < 8` (unique by `probe_unique`). -/
theorem probe_cover {cap n : Nat} (p₀ : Nat) (hcap : cap = 2 ^ n) (h8 : 8 ≤ cap) {s : Nat}
    (hs : s < cap) : ∃ k < cap / 8, ∃ j < 8, (probePos cap p₀ k + j) % cap = s := by
  obtain ⟨h8G, -⟩ := cap_facts hcap h8
  obtain ⟨x, hx, hfx⟩ := exists_eq_of_injOn (n := cap)
    (fun x => (probePos cap p₀ (x / 8) + x % 8) % cap)
    (fun x _ => Nat.mod_lt _ (by omega))
    (fun x hx y hy hxy => by
      obtain ⟨h1, h2⟩ := probe_unique hcap h8 (by omega) (by omega) (Nat.mod_lt x (by decide))
        (Nat.mod_lt y (by decide)) hxy
      omega) hs
  exact ⟨x / 8, by omega, x % 8, Nat.mod_lt x (by decide), hfx⟩

end SwissTable.Core.Swiss
