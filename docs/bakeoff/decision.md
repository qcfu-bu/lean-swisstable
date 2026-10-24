# Decision: Swiss table (control bytes, load 7/8, triangular group probing), always rebuilt into a fresh table, with the three measured fixes

Build the verified drop-in on the **swiss** layout. Use the judges' fixes B (tombstone rule) and C (insert fast path). Replace swiss's in-place rehash with a rebuild into a fresh table. Fix A becomes unnecessary because the in-place rehash it repaired is gone. I measured the fresh-table rebuild today. Against swiss with A+B+C it costs 1.8% on churn (geomean over 32 cells, worst cell 1.07x), 0.99x on churn-get, and 1.00x on insert. There were 0 checksum mismatches over 70 cells × {std, in-place, fresh}.

The cost of this choice is about 400–800 more proof lines than Dense and 700–1,400 more than Soa62. That is 5–15% of a project of roughly 8–10k lines once the shared Std port (3–4k lines) is counted. In return it is the fastest layout and has the fewest cells slower than Std.

## Why not the alternatives
- **Soa62** (the proof judge's pick) fails the speed goal. Its miss geomean is 1.64x Std, 3.12x at 10^7, and churn is 1.20x.
- **Dense at load 1/2** (the drop-in judge's pick). I recomputed it from `fidjudge2/d12.csv` and `ctl.csv` over the same 512 non-dense cells.
  - Overall it ties swiss: 0.55 against 0.56. The swiss figure is unfixed, with the 4 bug cells left out.
  - It loses far more cells: 58 above 1.10x and 15 above 1.5x, against 35 and 5 for swiss. Its worst cells are rand 1000 erase-alt 2.49, churn 1.99 and miss 1.77.
  - It loses on in-cache lookups: getd-shuf 0.90 vs 0.70, getopt-shuf 0.62 vs 0.49, miss 0.81 vs 0.58.
  - It uses more memory: 0.99x Std pre-sized and 1.61x grown (up to 2.31x), against 0.62x and 1.03x for swiss.
  - It wins on insert (0.42 vs 0.70), insert-cap (0.70 vs 0.90) and fold (0.15 vs 0.28).
  - Its fidelity advantages are about resource use, not the API: it keeps no erased objects alive and copies a shared map more cheaply. At the API and lemma level the two are equal. Neither needs `Inhabited`, both replace the stored key on insert, and both keep the old key in `getThenInsertIfNew?`.
- **SwissH** is slower overall (0.71 vs 0.64) and costs about 250 more proof lines.
- **Robin** keeps erased objects alive: 28,381 dead pairs after erasing all 10^5 entries.

## Exact layout and algorithms
- **Fields:**
  - `ctrl : ByteArray` of cap + 8 bytes, where bytes cap..cap+7 mirror bytes 0..7.
  - `keys : Array α` and `vals : Array β`, cap + 1 cells each; cell cap holds the placeholder.
  - `size`, `growthLeft`, `mask = cap − 1 : USize`, `shift = 57 − lg : UInt64`, `reqCap`.
  - cap = 2^lg with lg ≥ 3.
- **Control bytes:** EMPTY = 0xFF, DELETED = 0x80, FULL = 0b0hhhhhhh where hhhhhhh is h2.
- **Hash:** q = (hash a · 0x9E3779B97F4A7C15) >>> shift; home = (q >>> 7) & mask; h2 = q & 0x7F. Hashes are not stored, and growth recomputes `hash`, as Std does.
- **Group and matching:**
  - A group is the 8 bytes starting at pos, read as one little-endian UInt64 (eight `uget`s OR'ed together compile to one load).
  - The h2 match is the exact per-lane form `~~~(((x &&& 0x7F…) + 0x7F…) ||| x) &&& 0x80…` with x = g ^^^ h2·0x01…. It costs 1–2 instructions more than the borrow trick and is within ±2% in speed. It has no false positives and can be proved one lane at a time.
  - matchEmpty = `g &&& (g <<< 1) &&& H`; matchFree = `g &&& H`.
  - The lowest set lane is `((m &&& −m) >>> 7) · 0x0001020304050607 >>> 56`.
- **Probe:** triangular over groups, posₖ = (home + 8·k(k+1)/2) & mask for k < cap/8.
  - Lookups stop at the first group that contains an EMPTY byte.
  - Insert makes one pass and remembers the first EMPTY or DELETED slot it passes.
  - The sequence is a function that comes with a coverage lemma, so linear group steps can be swapped in.
- **Load:** capacity = cap/8·7, with the invariant growthLeft + size + #DELETED ≤ capacity.
- **Insert:**
  - **Fast path (C):** if the home byte is EMPTY and no lane of the home group matches h2, write at home.
  - Otherwise probe once. A hit replaces both key and value, which is Std's semantics.
  - A miss writes at the first free slot. If that slot is EMPTY and growthLeft = 0, rebuild first: at the same cap when size + 1 ≤ capacity/2, otherwise at double the cap.
- **Rebuild:** always into fresh arrays. Each FULL slot moves to the first free slot of its probe, with no key comparisons. There is no `rehash_in_place`.
- **Erase:**
  - Write EMPTY (growthLeft + 1) only if every 8-window containing the slot has another EMPTY. The test is `ea = 0 ∨ eb < lowbit(ea)`. Otherwise write DELETED.
  - **Tombstone rule (B):** if tombstones exceed capacity/4, set growthLeft := 0.
  - The erased cell gets the placeholder. Erase never shrinks the table, as in Std.
- **Placeholders:**
  - `∅` and `emptyWithCapacity` allocate nothing: a shared 8-byte EMPTY ctrl, mask 0, `#[]` arrays. The first insert allocates the table and uses its own pair as the placeholder.
  - **Change from the prototype:** every rebuild takes the inserting pair as the new placeholder. At most one erased pair stays alive, and only until the next rebuild. The prototype keeps the first pair ever inserted for the map's whole life.
- **Traversal:** fold, `forIn`, `toList`, keys and values go a group at a time over the FULL mask, as SwissH does.
- **Machine words:** `USize` loops for tables of at most 2^31 slots and executable Nat loops beyond, following OAMap's `slotFor` pattern. HashSet is `HashMap α Unit`, as in Std.

## Measured standing against Std
Columns: swiss geomean of min ns over 32 non-dense cells per workload, split n ≤ 10^5 / n > 10^5, worst cell, number of cells above 1.10x, and the dense-key geomean (max). Source: the full run, unfixed, with the 4 bug cells (churn at n=100000) left out.

| workload | geomean (small/large) | worst cell | >1.10x | dense keys |
|---|---|---|---|---|
| getd-shuf | 0.70 (0.70/0.70) | 0.90 | 0 | 1.12 (1.7) |
| getopt-shuf | 0.49 | 0.70 | 0 | 0.48 |
| getd (in order) | 0.78 (0.92/0.66) | 1.65 rand 1000 | 5 | 3.74 (12.4) |
| getopt | 0.47 | 0.70 | 0 | 1.42 (4.8) |
| miss | 0.58 (0.67/0.51) | 1.18 rand 100000 | 2 | 0.52 |
| insert | 0.70 | 0.98 | 0 | 2.21 (6.3) |
| insert-cap | 0.90 (0.85/0.96) | 1.76 flat 10^7 | 6 | 2.83 (9.6) |
| reinsert | 0.52 | 0.94 | 0 | 2.07 (7.0) |
| hashcons | 0.57 | 0.82 | 0 | 0.57 |
| erase-alt | 0.63 | 1.26 rand 1536 | 1 | 0.59 |
| erase-all | 0.68 | 1.58 rand 1536 | 4 | 0.63 |
| erase-alt-get | 0.87 (1.05/0.73) | 1.36 rand 1536 | 6 | 1.05 |
| churn | 0.77 (0.99/0.64) | 1.44 rand 1536 | 3 | 2.10 (6.9) |
| churn-get | 0.90 (1.06/0.76) | 1.50 flat 98304 | 8 | 1.00 |
| fold | 0.28 | 0.63 | 0 | 0.76 |
| free | 0.10 | 0.39 | 0 | 0.21 |

**Effect of the fixes**, measured by the perf judge (ratios to Std):

| fix | cells and change |
|---|---|
| A (now replaced by the fresh-table rebuild) | churn n=100000: rand 6.03→1.01, flat 9.06→0.91, string 10.21→0.96, struct 3.73→0.52 |
| B | churn-get rand 1536 1.47→0.98; churn-get 98304 flat/string/struct 1.27/1.36/1.16 → 0.84/0.81/1.05 |
| C, gains | insert-cap 10^7 rand 1.20→0.74, flat 1.80→0.71, string 1.24→0.94; flat insert-cap 6.3M 1.46→0.69 |
| C, costs | rand 1000 insert-cap 0.99→1.16; rand 98304 insert-cap 0.73→0.87 |

**Fresh-table rebuild vs std** (my run): churn worst cells are rand 1536 1.26 and flat 1536 1.22. One churn-get cell, string 1536, went from 0.81 to 1.05; it is probably noise and should be re-checked.

**Memory per entry:** 1.03x Std grown from empty (0.67–1.36), 0.62x pre-sized (0.50–0.82).

## Risks
1. **Cells still slower than Std:** about 20–25 non-dense cells above 1.10x, worst about 1.6x.
   - In-cache erase at load ~0.75: rand 1536 erase-all 1.58. Every open-addressing layout loses this cell (dense 3.01).
   - Lookups over tombstones with no insert after them (erase-alt-get): 6 cells at 1.11–1.36.
   - In-order getd at n ≤ 10^5: 1.11–1.65, which is 0.3–0.8 ns in absolute terms.
   - Miss at n=100000: 1.13–1.18. Swiss sits at load 0.76 there while Std is at 0.38.
   - Struct insert-cap: 1.30 at 10^7, cause unexplained.
2. **Consecutive Nat keys:** 7–12x Std at n ≥ 6.3M on in-order getd, insert-cap, reinsert and churn. This comes from the Fibonacci home slot and applies to every layout.
3. **Shared (persistent) maps with heap keys** cost 3–5x Std per copy-on-write update: String 10^6 24.9 ms vs 8.52, String 1000 9.49 µs vs 1.96. Nat keys are cheaper than Std (2.10 vs 8.97 ms). This cannot be fixed within this layout; document it.
4. **At most one erased pair stays referenced** until the next rebuild. This matters for values that close when the last reference drops (`IO.FS.Handle`). Without `Inhabited` or unsafe code, one is the minimum.
5. **Proof risk.** The two riskiest pieces are removed: the in-place rehash (800–1,500 lines) and the borrow-trick lemma (40–80 lines). What remains:
   - SWAR lemmas without `bv_decide`, which adds an axiom.
   - The triangular coverage lemma, 150–300 lines with no Mathlib.
6. **Generated code is fragile.**
   - The bug-A pattern (a reference-count raise just before an array update) can come back in any loop.
   - Fuel arguments, proof terms or the Nat fallback can change the generated code. Fix E's size gate did this: 241 vs 171 instructions/op.
   - So re-measure instructions/op after every change to the code, and add a check to `check_spec` for `lean_inc_ref` immediately followed by `lean_array_uset`.
7. **Deferred DHashMap** cannot use `vals : Array β` directly and will need sigma cells.

## Verification order
0. **Freeze the code.** Start from SwissF and add the exact match, the group-at-a-time fold, measure-terminated loops (no `partial`), the Nat/`USize` split at 2^31 slots, and the placeholder refresh. Re-run a matrix subset and accept within ±3% of SwissF.
1. **`Swiss/Word.lean`**, which can run in parallel with steps 3–4:
   - `load8` equals the 8 little-endian bytes, including through the mirror;
   - per-lane exact match, `matchEmpty` and `matchFree`;
   - lowest lane by `decide` over the 8 single-bit cases;
   - `m &&& (m − 1)` clears the lowest lane and decreases;
   - the erase test is equivalent to the window condition.
2. **Probe sequence.** Prove coverage: k(k+1)/2 is a bijection mod 2^m. If this stalls, ship linear group steps first, which need 0 lines and cost +9% on misses (rand 98304: 5.98 vs 5.48 ns).
3. **Model and `WF`.**
   - Reuse OAMap's `Slots`, `entryAt`, `entries` and `Shape`. `Shape` gains the unallocated case.
   - `TagInv` (ctrl byte = h2 of the key's hash) holds unconditionally, because a key is replaced only after an exact h2 match.
   - New fields: the mirror, byte classes, distinct keys (under `EquivBEq`), the window invariant (windows before a key's own window hold no EMPTY; under `LawfulHashable`, like `ProbeInv`), the count invariant, and `size_eq`.
4. **Probe lemma.** Generalise `walk_spec` and `walk_home` from slots to groups. Keep the statement shapes of `slotOf_of_beq`, `slotOf_absent`, `entries_pairwise` and `lookup_entries`.
5. **Insert.** Reuse `Insert.lean`: `setNew`, `setVal`, `entries_setNew_perm`, `TagInv.setNew`. Add the EMPTY/DELETED accounting and the lemma that the fast path equals the general path.
6. **Rebuild.** Reuse `Grow.lean`: `WF.empty`, `WF.grow`, `entries_grow_perm`. One proof covers both same-size and doubling rebuilds.
7. **Erase.** New: clearing a slot corresponds to `eraseKey`. The EMPTY step comes from the erase-test lemma in step 1; rule B is only accounting.
8. **Machine words equal the model.** Follow the `Fast.lean` pattern: `uget_eq_tagAt`, `uset_eq_setIfInBounds`, `probeU_toNat`.
9. **List model.** `toList` is up to permutation of `insertEntry`/`eraseKey`, and each query equals its list version, through `Std.Internal.List` (it imports cleanly).
10. **Std port:** 678 HashMap lemmas, 320 HashSet lemmas and 22 iterator lemmas via a `simp_to_model` analogue, plus the instances.

## Tuning ideas to carry over
- **C ungated** for now. Gate it by size only once a gate no longer changes the generated code; ungated it costs 16–20% on in-cache insert-cap.
- **D, lookup speculation at cap ≥ 2^20.** At 10^7, rand getd-shuf went 18.9→13.8, flat 50.4→37.5, struct 179→155. Ungated it costs in cache: rand 98304 getd-shuf 3.2→5.6. Needs codegen work first.
- **Group-at-a-time fold and `forIn`:** SwissH measured 0.20 against swiss's 0.28.
- **Keep `insertNew` inlined:** −15 to −33 instructions/op.
- **Tombstone cleanup from erase at a cap/4 or cap/2 threshold**, for erase-alt-get. Only cap/8 has been tested, and it made churn 2x slower.
- **Investigate struct insert-cap at 10^7.** h2 false positives were simulated at 1.5% and are ruled out.
- **Test the branch-predictor guess** for small-n in-order getd.
- **A HashSet table without vals:** about 9 instead of 17 B/slot, but it needs its own proof route. Do it after the port.
- **Do not change the Fibonacci home** for consecutive keys. An identity-like home packs them into one full run, and misses into that run would degrade badly.

Files are in /private/tmp/claude-501/-Users-qcfu-Projects-wnetkat/285881d0-ec47-495c-9169-fcc228e9dc96/scratchpad/synth/:
- `oab/Proto/SwissF/Map.lean`: SwissC with the fresh-table rebuild and the placeholder refresh.
- `res_f.jsonl`, `res_f.log`: today's run.
- `cmpf.py`, `d12b.py`, `sw.py`: the comparison scripts.

Nothing I started is still running.