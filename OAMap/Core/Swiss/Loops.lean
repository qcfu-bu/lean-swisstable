module

public import OAMap.Core.Swiss.Proofs.Bounds

/-!
# The SwissTable core: the loops on raw arrays (executable code, frozen)

The probes (`findLoop`, `findInsLoop`, `findFree` and their `Nat` counterparts), the rebuild's
move loops, the traversals and the bulk passes, on the arrays of a table rather than on `Table`,
so that the proof files after this one can state their specifications and the operations
(`Build.lean`, `Table.lean`) can use them. The algorithms, the layout and the measurements are
documented in `OAMap/Core/Swiss/Table.lean`.

Every array bound and every termination measure is discharged by a lemma of
`OAMap/Core/Swiss/Proofs/Bounds.lean` from the erased hypotheses of `Defs.lean` (`ArrU`, `LoopU`,
`ArrN`, ...), which the callers obtain from the invariant. The `…N` loops are the same algorithms
on `Nat` indices, for tables beyond `2 ^ 31` slots (and for the bulk passes at every size).
-/

set_option cleanup.letToHave false
-- Some erased hypotheses (`if h : …`) are used only by the termination proofs, which the linter
-- does not count as uses.
set_option linter.unusedVariables false

@[expose] public section

universe u v w w'

namespace OAMap.Core.Swiss

variable {α : Type u} {β : Type v}

/-! ## Probes on machine words (`mask < 2 ^ 31`) -/

/-- The slot of a key `== a` from the group at `pos` (the probe's step `stride`, group word `g`,
tag matches `m` still to try) on, or `mask + 1` when the probe ends without one. -/
@[specialize] def findLoop [BEq α] (ctrl : @& ByteArray) (keys : @& Array α) (a : @& α)
    (mask : USize) (rep : UInt64) (pos stride : USize) (g m : UInt64) (hA : ArrU ctrl mask)
    (hs : stride.toNat ≤ mask.toNat) (hm : IsMask m)
    (hk : mask.toNat < keys.size ∨ (m = 0 ∧ matchEmpty g ≠ 0)) : USize :=
  if h : m != 0 then
    let i := (pos + lowestLane m) &&& mask
    if keys.uget i (and_mask_lt (keys_of_ne hk h)) == a then i
    else findLoop ctrl keys a mask rep pos stride g (clearLowest m) hA hs (isMask_clearLowest hm)
      (Or.inl (keys_of_ne hk h))
  else if he : matchEmpty g != 0 then mask + 1
  else
    let stride := stride + 8
    if hgt : stride > mask then mask + 1
    else
      let pos := (pos + stride) &&& mask
      let g := ctrlWord ctrl pos (and_mask_word hA.word)
      findLoop ctrl keys a mask rep pos stride g (matchTag g rep) hA (le_of_not_gt' hgt)
        (isMask_matchTag g rep) (Or.inl (keys_of_empty hk he))
termination_by (mask.toNat + 8 - stride.toNat, m.toNat)
decreasing_by
  all_goals first
    | exact lex_lane hm h
    | exact lex_group hA.small hs hgt

/-- The slot of a key `== a`, or `mask + 1`. -/
@[inline] def findU [BEq α] [Hashable α] (ctrl : ByteArray) (keys : Array α) (mask : USize)
    (shift : UInt64) (a : α) (h : LoopU ctrl keys mask) : USize :=
  let q := hashBits shift a
  let pos := homeU q mask
  let rep := repTag (tagOf q)
  let g := ctrlWord ctrl pos (and_mask_word h.arr.word)
  findLoop ctrl keys a mask rep pos 0 g (matchTag g rep) h.arr stride_zero (isMask_matchTag g rep)
    (firstGroup h q)

/-- `findLoop`, also remembering the first EMPTY or DELETED slot `ins` passed (`ins > mask`: none
yet): the slot `i ≤ mask` of a key `== a`, or `mask + 1 + ins`. -/
@[specialize] def findInsLoop [BEq α] (ctrl : @& ByteArray) (keys : @& Array α) (a : @& α)
    (mask : USize) (rep : UInt64) (pos stride : USize) (g m : UInt64) (ins : USize)
    (hA : ArrU ctrl mask) (hs : stride.toNat ≤ mask.toNat) (hm : IsMask m)
    (hk : mask.toNat < keys.size ∨ (m = 0 ∧ matchEmpty g ≠ 0)) : USize :=
  if h : m != 0 then
    let i := (pos + lowestLane m) &&& mask
    if keys.uget i (and_mask_lt (keys_of_ne hk h)) == a then i
    else findInsLoop ctrl keys a mask rep pos stride g (clearLowest m) ins hA hs
      (isMask_clearLowest hm) (Or.inl (keys_of_ne hk h))
  else
    let ins := if ins > mask then
        let f := matchFree g
        if f != 0 then (pos + lowestLane f) &&& mask else ins
      else ins
    if he : matchEmpty g != 0 then ins + (mask + 1)
    else
      let stride := stride + 8
      if hgt : stride > mask then ins + (mask + 1)
      else
        let pos := (pos + stride) &&& mask
        let g := ctrlWord ctrl pos (and_mask_word hA.word)
        findInsLoop ctrl keys a mask rep pos stride g (matchTag g rep) ins hA (le_of_not_gt' hgt)
          (isMask_matchTag g rep) (Or.inl (keys_of_empty hk he))
termination_by (mask.toNat + 8 - stride.toNat, m.toNat)
decreasing_by
  all_goals first
    | exact lex_lane hm h
    | exact lex_group hA.small hs hgt

/-- The first EMPTY or DELETED slot of the probe from the group at `pos` (step `stride`), or
`mask + 1` when the probe ends without one. -/
def findFree (ctrl : @& ByteArray) (mask pos stride : USize) (hA : ArrU ctrl mask)
    (hp : pos.toNat ≤ mask.toNat) (hs : stride.toNat ≤ mask.toNat) : USize :=
  let f := matchFree (ctrlWord ctrl pos (word_of_le hA.word hp))
  if f != 0 then (pos + lowestLane f) &&& mask
  else
    let stride := stride + 8
    if hgt : stride > mask then mask + 1
    else findFree ctrl mask ((pos + stride) &&& mask) stride hA (and_mask_le _ _)
      (le_of_not_gt' hgt)
termination_by mask.toNat + 8 - stride.toNat
decreasing_by exact sub_group hA.small hs hgt

/-- `findFree` ends at a slot or at `mask + 1` (a fact the rebuild's loop takes as an erased
argument, `freeBound`). -/
def FreeBound (mask : USize) : Prop :=
  ∀ (c : ByteArray) (pos stride : USize) (hA : ArrU c mask) (hp : pos.toNat ≤ mask.toNat)
    (hs : stride.toNat ≤ mask.toNat), (findFree c mask pos stride hA hp hs).toNat ≤ mask.toNat + 1

/-! ## Probes on `Nat` indices (tables beyond `2 ^ 31` slots) -/

/-- `findLoop` on `Nat` indices, for a table of `cap` slots: the slot of a key `== a`, if the
probe finds one. -/
@[specialize] def findLoopN [BEq α] (ctrl : @& ByteArray) (keys : @& Array α) (a : @& α)
    (cap : Nat) (rep : UInt64) (pos stride : Nat) (g m : UInt64) (hA : ArrN ctrl keys cap)
    (hm : IsMask m) : Option Nat :=
  if h : m != 0 then
    let i := (pos + (lowestLane64 m).toNat) % cap
    if keys[i]'(hA.mod_keys _) == a then some i
    else findLoopN ctrl keys a cap rep pos stride g (clearLowest m) hA (isMask_clearLowest hm)
  else if matchEmpty g != 0 then none
  else
    let stride := stride + 8
    if hle : cap ≤ stride then none
    else
      let pos := (pos + stride) % cap
      let g := ctrlWordN ctrl pos (hA.mod_word _)
      findLoopN ctrl keys a cap rep pos stride g (matchTag g rep) hA (isMask_matchTag g rep)
termination_by (cap + 8 - stride, m.toNat)
decreasing_by
  all_goals first
    | exact lex_lane hm h
    | exact lex_groupN hle

/-- The slot of a key `== a` in a table of `cap` slots, if any (`findU` on `Nat` indices). -/
@[specialize] def findN [BEq α] [Hashable α] (ctrl : @& ByteArray) (keys : @& Array α)
    (cap : Nat) (shift : UInt64) (a : @& α) (hA : ArrN ctrl keys cap) : Option Nat :=
  let q := hashBits shift a
  let pos := homeN q cap
  let rep := repTag (tagOf q)
  let g := ctrlWordN ctrl pos (hA.mod_word _)
  findLoopN ctrl keys a cap rep pos 0 g (matchTag g rep) hA (isMask_matchTag g rep)

/-- `findInsLoop` on `Nat` indices: `.inl i` at the slot `i` of a key `== a`, else `.inr ins`
with `ins` the first free slot passed (`cap` when none). -/
@[specialize] def findInsLoopN [BEq α] (ctrl : @& ByteArray) (keys : @& Array α) (a : @& α)
    (cap : Nat) (rep : UInt64) (pos stride : Nat) (g m : UInt64) (ins : Nat)
    (hA : ArrN ctrl keys cap) (hm : IsMask m) : Nat ⊕ Nat :=
  if h : m != 0 then
    let i := (pos + (lowestLane64 m).toNat) % cap
    if keys[i]'(hA.mod_keys _) == a then .inl i
    else findInsLoopN ctrl keys a cap rep pos stride g (clearLowest m) ins hA
      (isMask_clearLowest hm)
  else
    let ins := if cap ≤ ins then
        let f := matchFree g
        if f != 0 then (pos + (lowestLane64 f).toNat) % cap else ins
      else ins
    if matchEmpty g != 0 then .inr ins
    else
      let stride := stride + 8
      if hle : cap ≤ stride then .inr ins
      else
        let pos := (pos + stride) % cap
        let g := ctrlWordN ctrl pos (hA.mod_word _)
        findInsLoopN ctrl keys a cap rep pos stride g (matchTag g rep) ins hA
          (isMask_matchTag g rep)
termination_by (cap + 8 - stride, m.toNat)
decreasing_by
  all_goals first
    | exact lex_lane hm h
    | exact lex_groupN hle

/-- The insertion probe of `Table.containsThenInsert` on `Nat` indices, for a table of `cap`
slots, with fast path C: `.inl i` at the slot `i` of a key `== a`, else `.inr j` with `j` the
first free slot of the probe. -/
@[inline] def insSlotN [BEq α] (ctrl : ByteArray) (keys : Array α) (a : α) (cap : Nat)
    (q : UInt64) (hA : ArrN ctrl keys cap) : Nat ⊕ Nat :=
  let pos := homeN q cap
  let rep := repTag (tagOf q)
  let g := ctrlWordN ctrl pos (hA.mod_word _)
  let mt := matchTag g rep
  if mt == 0 && g &&& 0xFF == 0xFF then .inr pos
  else findInsLoopN ctrl keys a cap rep pos 0 g mt cap hA (isMask_matchTag g rep)

/-- `findFree` on `Nat` indices: the first free slot of the probe from `pos`, or `cap`. -/
def findFreeN (ctrl : @& ByteArray) (cap pos stride : Nat) (hA : CtrlN ctrl cap)
    (hp : pos < cap) : Nat :=
  let f := matchFree (ctrlWordN ctrl pos (hA.word_of_lt hp))
  if f != 0 then (pos + (lowestLane64 f).toNat) % cap
  else
    let stride := stride + 8
    if hle : cap ≤ stride then cap
    else findFreeN ctrl cap ((pos + stride) % cap) stride hA (Nat.mod_lt _ hA.pos)
termination_by cap + 8 - stride
decreasing_by exact sub_groupN hle

/-- `findFreeN` ends at a slot or at `cap` (an erased argument of the rebuild's loop,
`freeBoundN`). -/
def FreeBoundN (cap : Nat) : Prop :=
  ∀ (c : ByteArray) (pos stride : Nat) (hA : CtrlN c cap) (hp : pos < cap),
    findFreeN c cap pos stride hA hp ≤ cap

/-! ## The insertion probes from the home group (specification only)

The inserts start the insertion probe inline (`containsThenInsert` tests the home group for
fast path C first); these are the same terms, for the statements of the probe lemmas. -/

/-- The machine-word insertion probe for `a` from its home group, as `containsThenInsert`,
`getThenInsertIfNew?` and `alter` run it. -/
@[reducible] def insProbeU [BEq α] [Hashable α] (ctrl : ByteArray) (keys : Array α) (mask : USize)
    (shift : UInt64) (a : α) (h : LoopU ctrl keys mask) : USize :=
  findInsLoop ctrl keys a mask (repTag (tagOf (hashBits shift a))) (homeU (hashBits shift a) mask)
    0 (ctrlWord ctrl (homeU (hashBits shift a) mask) (and_mask_word h.arr.word))
    (matchTag (ctrlWord ctrl (homeU (hashBits shift a) mask) (and_mask_word h.arr.word))
      (repTag (tagOf (hashBits shift a))))
    (mask + 1) h.arr stride_zero (isMask_matchTag _ _) (firstGroup h (hashBits shift a))

/-- The insertion probe on `Nat` indices for `a` from its home group, as
`getThenInsertIfNewN` and `alterN` run it. -/
@[reducible] def insProbeN [BEq α] [Hashable α] (ctrl : ByteArray) (keys : Array α) (cap : Nat)
    (shift : UInt64) (a : α) (hA : ArrN ctrl keys cap) : Nat ⊕ Nat :=
  findInsLoopN ctrl keys a cap (repTag (tagOf (hashBits shift a))) (homeN (hashBits shift a) cap)
    0 (ctrlWordN ctrl (homeN (hashBits shift a) cap) (hA.mod_word _))
    (matchTag (ctrlWordN ctrl (homeN (hashBits shift a) cap) (hA.mod_word _))
      (repTag (tagOf (hashBits shift a))))
    cap hA (isMask_matchTag _ _)

/-! ## Rebuild: moving the entries into fresh arrays -/

/-- Move every FULL slot `i ≤ omask` of the old table into the new one, at the first free slot of
its probe there (hash recomputed, no key comparison). -/
@[specialize] def moveLoop [Hashable α] (oc : @& ByteArray) (ok : @& Array α) (ov : @& Array β)
    (omask i : USize) (nc : ByteArray) (nk : Array α) (nv : Array β) (nmask : USize)
    (nshift : UInt64) (hO : MoveSrcU oc ok ov omask) (hN : MoveDstU nc nk nv nmask)
    (hff : FreeBound nmask) : ByteArray × Array α × Array β :=
  if hi : i > omask then (nc, nk, nv)
  else if oc.uget i (hO.ctrl_lt hi) &&& 0x80 == 0 then
    let k := ok.uget i (hO.keys_lt hi)
    let q := hashBits nshift k
    let j := findFree nc nmask (homeU q nmask) 0 hN.arr (and_mask_le _ _) stride_zero
    moveLoop oc ok ov omask (i + 1)
      (setCtrl nc nmask j (tagOf q) (hN.ctrl_lt (hff ..)) hN.mirror)
      (nk.uset j k (hN.keys_lt (hff ..)))
      (nv.uset j (ov.uget i (hO.vals_lt hi)) (hN.vals_lt (hff ..)))
      nmask nshift hO (hN.write (size_setCtrl ..) (Array.size_uset _) (Array.size_uset _)) hff
  else moveLoop oc ok ov omask (i + 1) nc nk nv nmask nshift hO hN hff
termination_by omask.toNat + 1 - i.toNat
decreasing_by all_goals exact move_dec hO.small hi

/-- `moveLoop` on `Nat` indices: the old table has `ocap` slots, the new one `ncap`. -/
@[specialize] def moveLoopN [Hashable α] (oc : @& ByteArray) (ok : @& Array α) (ov : @& Array β)
    (ocap i : Nat) (nc : ByteArray) (nk : Array α) (nv : Array β) (ncap : Nat)
    (nshift : UInt64) (hO : MoveSrcN oc ok ov ocap) (hN : MoveDstN nc nk nv ncap)
    (hff : FreeBoundN ncap) : ByteArray × Array α × Array β :=
  if h : i < ocap then
    if oc[i]'(hO.ctrl_lt h) &&& 0x80 == 0 then
      let k := ok[i]'(hO.keys_lt h)
      let q := hashBits nshift k
      let j := findFreeN nc ncap (homeN q ncap) 0 hN.ctrlN (Nat.mod_lt _ hN.pos)
      moveLoopN oc ok ov ocap (i + 1)
        (setCtrlN nc ncap j (tagOf q) (hN.ctrl_lt (hff ..)) hN.word hN.pos)
        (nk.set j k (hN.keys_lt (hff ..))) (nv.set j (ov[i]'(hO.vals_lt h)) (hN.vals_lt (hff ..)))
        ncap nshift hO (hN.write (size_setCtrlN ..) (Array.size_set _) (Array.size_set _)) hff
    else moveLoopN oc ok ov ocap (i + 1) nc nk nv ncap nshift hO hN hff
  else (nc, nk, nv)
termination_by ocap - i

/-! ## Traversals on machine words -/

/-- `foldM` from the full lanes `fm` of the group at `p` on, slot order; `cap` slots. -/
@[specialize] def foldMLoop {ε : Type w} {m : Type w → Type w'} [Monad m] (f : ε → α → β → m ε)
    (ctrl : @& ByteArray) (keys : @& Array α) (vals : @& Array β) (cap p : USize) (fm : UInt64)
    (acc : ε) (hF : FoldU ctrl keys vals cap) (hp : GroupAt cap p) (hm : IsMask fm) : m ε :=
  if h : fm != 0 then
    let i := p + lowestLane fm
    do
      let acc ← f acc (keys.uget i (hF.lane_keys hp hm)) (vals.uget i (hF.lane_vals hp hm))
      foldMLoop f ctrl keys vals cap p (clearLowest fm) acc hF hp (isMask_clearLowest hm)
  else
    let p := p + 8
    if hlt : p < cap then
      foldMLoop f ctrl keys vals cap p (matchFull (ctrlWord ctrl p (hF.next_word hp hlt))) acc hF
        (hF.next_group hp hlt) (isMask_matchFull _)
    else pure acc
termination_by (cap.toNat + 8 - p.toNat, fm.toNat)
decreasing_by
  all_goals first
    | exact lex_lane hm h
    | exact lex_fold hF.small hp hlt

/-- `forIn` from the full lanes `fm` of the group at `p` on, slot order, with early exit. -/
@[specialize] def forInLoop {ε : Type w} {m : Type w → Type w'} [Monad m]
    (f : α → β → ε → m (ForInStep ε)) (ctrl : @& ByteArray) (keys : @& Array α)
    (vals : @& Array β) (cap p : USize) (fm : UInt64) (acc : ε) (hF : FoldU ctrl keys vals cap)
    (hp : GroupAt cap p) (hm : IsMask fm) : m ε :=
  if h : fm != 0 then
    let i := p + lowestLane fm
    do
      match ← f (keys.uget i (hF.lane_keys hp hm)) (vals.uget i (hF.lane_vals hp hm)) acc with
      | .done acc => pure acc
      | .yield acc =>
        forInLoop f ctrl keys vals cap p (clearLowest fm) acc hF hp (isMask_clearLowest hm)
  else
    let p := p + 8
    if hlt : p < cap then
      forInLoop f ctrl keys vals cap p (matchFull (ctrlWord ctrl p (hF.next_word hp hlt))) acc hF
        (hF.next_group hp hlt) (isMask_matchFull _)
    else pure acc
termination_by (cap.toNat + 8 - p.toNat, fm.toNat)
decreasing_by
  all_goals first
    | exact lex_lane hm h
    | exact lex_fold hF.small hp hlt

/-- Fold over the full lanes `fm` of the group at `p`, highest lane first. -/
@[specialize] def foldRevGroup {ε : Type w} (f : ε → α → β → ε) (keys : @& Array α)
    (vals : @& Array β) (p : USize) (fm : UInt64) (acc : ε) (hp : RevGroupU keys vals p)
    (hm : IsMask fm) : ε :=
  if h : fm != 0 then
    let i := p + lowestLane fm
    f (foldRevGroup f keys vals p (clearLowest fm) acc hp (isMask_clearLowest hm))
      (keys.uget i (hp.lane_keys hm)) (vals.uget i (hp.lane_vals hm))
  else acc
termination_by fm.toNat
decreasing_by exact clearLowest_lt_of hm h

/-- `foldRev` over the groups below slot `p`, last group first. -/
@[specialize] def foldRevLoop {ε : Type w} (f : ε → α → β → ε) (ctrl : @& ByteArray)
    (keys : @& Array α) (vals : @& Array β) (p : USize) (acc : ε) (hp : RevAtU ctrl keys vals p) :
    ε :=
  if h : p < 8 then acc
  else
    let p := p - 8
    let acc := foldRevGroup f keys vals p (matchFull (ctrlWord ctrl p (hp.word_sub h))) acc
      (hp.group h) (isMask_matchFull _)
    foldRevLoop f ctrl keys vals p acc (hp.next h)
termination_by p.toNat
decreasing_by exact rev_dec h

/-! ## Traversals on `Nat` indices -/

/-- `foldMLoop` on `Nat` indices. -/
@[specialize] def foldMLoopN {ε : Type w} {m : Type w → Type w'} [Monad m] (f : ε → α → β → m ε)
    (ctrl : @& ByteArray) (keys : @& Array α) (vals : @& Array β) (cap p : Nat) (fm : UInt64)
    (acc : ε) (hF : FoldN ctrl keys vals cap) (hp : GroupAtN cap p) (hm : IsMask fm) : m ε :=
  if h : fm != 0 then
    let i := p + (lowestLane64 fm).toNat
    do
      let acc ← f acc (keys[i]'(hF.lane_keys hp hm)) (vals[i]'(hF.lane_vals hp hm))
      foldMLoopN f ctrl keys vals cap p (clearLowest fm) acc hF hp (isMask_clearLowest hm)
  else
    let p := p + 8
    if hlt : p < cap then
      foldMLoopN f ctrl keys vals cap p (matchFull (ctrlWordN ctrl p (hF.next_word hlt))) acc hF
        (hF.next_group hp hlt) (isMask_matchFull _)
    else pure acc
termination_by (cap + 8 - p, fm.toNat)
decreasing_by
  all_goals first
    | exact lex_lane hm h
    | exact lex_foldN hlt

/-- `forInLoop` on `Nat` indices. -/
@[specialize] def forInLoopN {ε : Type w} {m : Type w → Type w'} [Monad m]
    (f : α → β → ε → m (ForInStep ε)) (ctrl : @& ByteArray) (keys : @& Array α)
    (vals : @& Array β) (cap p : Nat) (fm : UInt64) (acc : ε) (hF : FoldN ctrl keys vals cap)
    (hp : GroupAtN cap p) (hm : IsMask fm) : m ε :=
  if h : fm != 0 then
    let i := p + (lowestLane64 fm).toNat
    do
      match ← f (keys[i]'(hF.lane_keys hp hm)) (vals[i]'(hF.lane_vals hp hm)) acc with
      | .done acc => pure acc
      | .yield acc =>
        forInLoopN f ctrl keys vals cap p (clearLowest fm) acc hF hp (isMask_clearLowest hm)
  else
    let p := p + 8
    if hlt : p < cap then
      forInLoopN f ctrl keys vals cap p (matchFull (ctrlWordN ctrl p (hF.next_word hlt))) acc hF
        (hF.next_group hp hlt) (isMask_matchFull _)
    else pure acc
termination_by (cap + 8 - p, fm.toNat)
decreasing_by
  all_goals first
    | exact lex_lane hm h
    | exact lex_foldN hlt

/-- `foldRevGroup` on `Nat` indices. -/
@[specialize] def foldRevGroupN {ε : Type w} (f : ε → α → β → ε) (keys : @& Array α)
    (vals : @& Array β) (p : Nat) (fm : UInt64) (acc : ε) (hp : RevGroupN keys vals p)
    (hm : IsMask fm) : ε :=
  if h : fm != 0 then
    let i := p + (lowestLane64 fm).toNat
    f (foldRevGroupN f keys vals p (clearLowest fm) acc hp (isMask_clearLowest hm))
      (keys[i]'(hp.lane_keys hm)) (vals[i]'(hp.lane_vals hm))
  else acc
termination_by fm.toNat
decreasing_by exact clearLowest_lt_of hm h

/-- `foldRevLoop` on `Nat` indices. -/
@[specialize] def foldRevLoopN {ε : Type w} (f : ε → α → β → ε) (ctrl : @& ByteArray)
    (keys : @& Array α) (vals : @& Array β) (p : Nat) (acc : ε) (hp : RevAtN ctrl keys vals p) :
    ε :=
  if h : p < 8 then acc
  else
    let p := p - 8
    let acc := foldRevGroupN f keys vals p (matchFull (ctrlWordN ctrl p (hp.word_sub h))) acc
      (hp.group h) (isMask_matchFull _)
    foldRevLoopN f ctrl keys vals p acc (hp.next h)
termination_by p

/-! ## Bulk passes (on `Nat` indices) -/

/-- The first full slot from slot `i` on, if any. -/
def firstFull (ctrl : @& ByteArray) (cap i : Nat) (hc : cap ≤ ctrl.size) : Option Nat :=
  if h : i < cap then
    if ctrl[i]'(Nat.lt_of_lt_of_le h hc) < 0x80 then some i else firstFull ctrl cap (i + 1) hc
  else none
termination_by cap - i

/-- The first full slot from slot `i` on whose entry `f` maps to `some`, with that value. -/
@[specialize] def firstSome {γ : Type w} (f : α → β → Option γ) (ctrl : @& ByteArray)
    (keys : @& Array α) (vals : @& Array β) (cap i : Nat) (hA : FoldN ctrl keys vals cap) :
    Option (Nat × γ) :=
  if h : i < cap then
    if ctrl[i]'(hA.ctrl_lt h) < 0x80 then
      match f (keys[i]'(hA.keys_lt h)) (vals[i]'(hA.vals_lt h)) with
      | some c => some (i, c)
      | none => firstSome f ctrl keys vals cap (i + 1) hA
    else firstSome f ctrl keys vals cap (i + 1) hA
  else none
termination_by cap - i

/-- `filterMap`'s pass over cells `i .. cap` (cell `cap` is the placeholder), building the new
value array `out`: the entries of slots below `i0` were rejected (`firstSome`), slot `i0` maps to
`c0`, and every later entry is mapped now; a rejected entry is erased in place (`eraseCtrlN`, its
key cell gets the placeholder key), and every free cell of `out` gets `c0`. -/
@[specialize] def filterMapLoop {γ : Type w} (f : α → β → Option γ) (vals : @& Array β)
    (cap i0 : Nat) (c0 : γ) (i : Nat) (ctrl : ByteArray) (keys : Array α) (size gl : Nat)
    (out : Array γ) (hA : FMArr ctrl keys vals cap) : ByteArray × Array α × Nat × Nat × Array γ :=
  if h : i < cap then
    if ctrl[i]'(hA.ctrl_lt h) < 0x80 then
      if i < i0 then
        match he : eraseCtrlN ctrl size gl cap i h hA.word with
        | (ctrl, gl) =>
          let keys := keys.set i (keys[cap]'hA.keys) (hA.keys_lt h)
          filterMapLoop f vals cap i0 c0 (i + 1) ctrl keys (size - 1) gl (out.push c0)
            (hA.erase he (Array.size_set _))
      else if i = i0 then
        filterMapLoop f vals cap i0 c0 (i + 1) ctrl keys size gl (out.push c0) hA
      else
        match f (keys[i]'(hA.keys_lt h)) (vals[i]'(hA.vals_lt h)) with
        | some c => filterMapLoop f vals cap i0 c0 (i + 1) ctrl keys size gl (out.push c) hA
        | none =>
          match he : eraseCtrlN ctrl size gl cap i h hA.word with
          | (ctrl, gl) =>
            let keys := keys.set i (keys[cap]'hA.keys) (hA.keys_lt h)
            filterMapLoop f vals cap i0 c0 (i + 1) ctrl keys (size - 1) gl (out.push c0)
              (hA.erase he (Array.size_set _))
    else filterMapLoop f vals cap i0 c0 (i + 1) ctrl keys size gl (out.push c0) hA
  else (ctrl, keys, size, gl, out.push c0)
termination_by cap - i

end OAMap.Core.Swiss
