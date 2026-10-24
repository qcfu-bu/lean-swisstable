# OAMap

A verified drop-in replacement for `Std.HashMap` and `Std.HashSet` (Lean v4.35.0, core and Std
only): `OAMap.HashMap α β` and `OAMap.HashSet α`, with Std's public theorems, definitions and
instances reproduced under the same names, statements, binders and attributes.

The design is fixed in [`docs/ARCHITECTURE.md`](docs/ARCHITECTURE.md); the supporting studies are
`docs/proofs.md`, `docs/parity.md`, `docs/inventory.md` (with `tools/inventory.json`), and the
experiments they cite are in `docs/experiments/` (`Mock2.lean`, `modtest/`, ...). These documents
were written in a separate design directory: where they say "this directory", read
`docs/experiments/` for the mocks and `modtest/`, `test/Parity.lean` for the checker, `tools/`
for the scripts (including `tools2/secdeps.py`, now `tools/secdeps.py`) and `tools/data/` for
the JSON inputs.

Status: complete. The library runs on the SwissTable core `OAMap.Core.Swiss`, the winner of the
benchmark bake-off (`docs/bakeoff/decision.md`, below), selected by `OAMap/Core/Table.lean`. Every
proof is complete: no `sorry`, and every constant of the library (4187, core included) depends only
on `propext`, `Classical.choice` and `Quot.sound`. Parity with Std reports 1140 of 1140 Std
declarations ok, 0 missing and 0 extras (structure internals and `Internal` included; 30 names
ignored, see below). The layers above the core were developed and proved against the list-backed
reference core `OAMap.Core.ListRef`, which is kept and still checked against the contract; the
switch changed no line above the core. The nine `HashMap/Lemmas/*.lean` files and
`HashSet/{Basic,Lemmas,DecidableEquiv}.lean` are generated from Std's text (below), with hand proofs
where no generated proof compiled (kept in `tools/data/hand.json`; each file's docstring lists
them). On the bake-off's benchmark matrix `OAMap.HashMap` takes 0.55 of `Std.HashMap`'s time per
operation (geometric mean over 512 cells, section "Performance").

## Build and test

```sh
lake build                 # the library OAMap (default target): every proof
lake test                  # the test library OAMapTest (below)
lake exe oamap-bench       # OAMap.HashMap against Std.HashMap (section "Performance")
tools/ci.sh                # all of these (the benchmark only built), plus the text and C checks
```

`lake test` builds `test/OAMapTest.lean`, whose modules log an error (failing the build) when
their check fails:

| module | check |
|---|---|
| `CoreSpec` | the selected core provides the 23 definitions and 22 lemmas of the contract (§3.4) |
| `CoreSpecListRef` | the same text against the reference core `OAMap.Core.ListRef` (a separate root of the test library: the two cores define the same names) |
| `AuditListRef` | `Audit`'s checks on the reference core, which the library no longer imports (a third root, for the same reason) |
| `SealCheck` | modules above the core use only the 45 contract names, import no core directly, and never `import all` |
| `Audit` | every constant of `OAMap` uses only `propext`, `Classical.choice`, `Quot.sound`; no axiom, `opaque`, `partial`, `unsafe`, `implemented_by`, `extern` (the compiler's `f._unsafe_rec` helper of a safe definition `f` by well-founded recursion, in the same module, is exempt from the `partial`/`unsafe` test only; the checks are `AuditLib.lean`'s) |
| `ParityRun` | statement, attribute and axiom parity with `Std.HashMap`/`Std.HashSet` |
| `Cbv` | `by cbv` closes the same goals as on Std |
| `Unverified` | `#guard` tests for the functions without Std lemmas, and the exact slot counts (`Internal.numBuckets`) of the SwissTable core |
| `Semantics` | `#guard` tests of the key and value each operation keeps, one traversal order, and the scoping of `~m` |
| `SwissGroupUse` | a lookup step and an erase step proved from another module with the exported lemmas of `OAMap.Core.Swiss.Group` only |

**Gates (on since the Merge).** `ParityRun` fails on any difference from Std outside its `ignore`
list: errors, warnings and extras (`failOnWarning := true`). The list has 30 names: the 16 iterator
declarations (checked by `tools/srccheck.py` instead) and the 14 structure internals of `HashMap`
and `HashMap.Equiv` that mention `inner`, a core table rather than a `DHashMap`. Only `Raw` is
excluded; `Internal` and the other structure internals are checked. `Audit` fails on any dependency
on `sorryAx` (`failOnSorry := true`).

## Performance

`OAMap.HashMap` against `Std.HashMap` on the bake-off's full matrix: the bake-off harness
`oabench2` (outside this repository; `bench/` has its workloads, below), 16 timed workloads × 5 key
types × 8 sizes from 1000 to 10^7, one process per cell, the minimum ns per operation over at least
5 repetitions (3 at n ≥ 4·10^6), Apple M5 Pro at 4.25–4.67 GHz on every cell, 1480 cells with 0
checksum mismatches (`docs/bakeoff/lib-results.csv`; the harness's tables are in
`lib-summary.txt`). Ratios below 1 are faster than Std. Per workload: the geometric mean of
OAMap/Std over the 32 non-dense cells (`rand`, `flat`, `struct`, `string` keys × 8 sizes), split
n ≤ 10^5 / n > 10^5; the worst cell; the cells above 1.10; the dense keys `0 .. n-1` (geometric
mean and maximum); and the bake-off prototype `swiss` on the same cells
(`docs/bakeoff/fullrun-results.csv`; without the fixes of the decision, and without its 4 cells of
churn at n = 100000, where it was 3.7–10x Std).

| workload | OAMap/Std (small/large) | worst cell | > 1.10 | dense (max) | `swiss` |
|---|---|---|---|---|---|
| getd-shuf | 0.68 (0.68/0.68) | 1.08 flat 10^7 | 0 | 1.14 (1.8) | 0.70 |
| getopt-shuf | 0.50 (0.54/0.46) | 0.74 struct 100000 | 0 | 0.51 (0.6) | 0.49 |
| getd (in order) | 0.76 (0.91/0.64) | 1.65 rand 1000 | 6 | 3.82 (11.8) | 0.78 |
| getopt (in order) | 0.48 (0.53/0.44) | 0.72 struct 100000 | 0 | 1.49 (4.5) | 0.47 |
| miss | 0.58 (0.66/0.50) | 1.20 rand 100000 | 2 | 0.52 (1.6) | 0.58 |
| insert | 0.69 (0.75/0.65) | 0.94 struct 1000 | 0 | 1.74 (3.7) | 0.70 |
| insert-cap | 0.84 (0.96/0.73) | 1.11 string 100000 | 2 | 2.22 (5.9) | 0.90 |
| reinsert | 0.52 (0.54/0.51) | 0.85 string 10^7 | 0 | 1.95 (6.5) | 0.52 |
| hashcons | 0.57 (0.60/0.54) | 0.78 struct 98304 | 0 | 0.55 (1.0) | 0.57 |
| erase-alt | 0.66 (0.76/0.58) | 1.29 rand 1536 | 1 | 0.63 (0.8) | 0.63 |
| erase-all | 0.72 (0.87/0.61) | 1.63 rand 1536 | 3 | 0.66 (0.8) | 0.68 |
| erase-alt-get | 0.85 (1.04/0.69) | 1.37 rand 1536 | 6 | 1.09 (1.3) | 0.87 |
| churn | 0.75 (0.86/0.66) | 1.25 flat 1536 | 2 | 2.12 (7.3) | 0.77 |
| churn-get | 0.82 (0.91/0.73) | 1.21 string 1536 | 1 | 1.03 (1.5) | 0.90 |
| fold | 0.20 (0.32/0.13) | 0.59 struct 1536 | 0 | 0.68 (0.8) | 0.28 |
| free | 0.10 (0.18/0.05) | 0.39 struct 1000 | 0 | 0.21 (0.3) | 0.10 |
| **all timed** | **0.55** (512 cells) | | 23 (3 above 1.5) | 1.00 | 0.56 (35, 5 above 1.5) |

By key type: rand 0.49, flat 0.60, struct 0.54, string 0.56, dense 1.00. Some absolute
figures (ns per operation, Std → OAMap): rand at 10^6, `getD` shuffled 14.8 → 9.3, miss
11.0 → 2.4, insert 44.9 → 23.5, erase 46.4 → 23.8, `fold` 9.2 → 1.6; string at 10^6, `getD`
shuffled 29.8 → 22.4, insert 104.6 → 63.4.

* **The slower cells** are the ones the bake-off decision predicted: in-cache erasing at load 0.75
  (rand 1536: erase-all 1.63, erase-alt 1.29), lookups over tombstones with no insert after them
  (erase-alt-get, 6 cells at 1.15–1.37), in-order `getD` (rand and flat at n ≤ 1536: 1.23–1.65,
  0.7–1.1 ns more per lookup; rand at 100000 and 10^6, string at 1536: 1.10–1.14), and misses at
  n = 100000 (1.12–1.20; the table is at load 0.76 there, Std's buckets at 0.38).
* **Dense keys** (`0 .. n-1`, consecutive `Nat`s) are Std's best case (its bucket index is
  collision-free and sequential) and cost OAMap's multiplicative hash its locality: 3.9–11.8x Std
  on in-order `getD`, `insert-cap`, reinsert and churn at n ≥ 10^6, and 1.00 over all dense cells.
* **Against the frozen core.** On the 16 cells per workload of the freeze run
  (`docs/bakeoff/freeze-results.csv`: rand, flat, struct, string × 1000, 98304, 10^6, 10^7) the
  frozen core `final` measured 0.55 and the library measures 0.56, every workload within 0.04
  (churn-get 0.77 vs 0.81 is the largest gap, across two runs whose Std times also differ). The
  instructions per operation are the same (ratio 1.0002 over 36 cells, at most 1.0028): the
  public API adds nothing to the core's code.
* **Memory** (maximum RSS of a cell above that of its keys, per entry, n ≥ 98304): 1.03x Std for
  a map grown from empty (0.68–1.36x; e.g. 55 against 46 bytes at 10^7) and 0.63x for one created
  with `emptyWithCapacity n` (0.51–0.82x; 30 against 46 bytes at 10^7), as the prototype measured.
* Not measured here: updating a map that is shared (persistent use) first copies its arrays, as
  Std copies its bucket array; the bake-off measured 3–5x Std per such copy-on-write update with
  `String` keys, and less than Std with `Nat` keys.

`lake exe oamap-bench` runs the same workloads in the repository (`bench/Main.lean`, the harness's
modules in `bench/Bench/` without its hardware counters): with no arguments, 13 workloads at `rand`
and `string` keys for n = 1000, 100000, 1000000, each cell in its own process, printing Std's and
OAMap's ns per operation and the geometric means (under a minute; on the machine above, 0.63
over its 78 cells, with 0 checksum mismatches); `compare` takes `--keys`, `--sizes`,
`--workloads`, `--reps` and `--min-ms`, and `oamap-bench <std|oamap> <key> <n> <workload>` runs one
cell and prints the harness's `RESULT` line.

## Parity

```sh
lake build OAMap Parity && lake env lean test/OAMapTest/ParityRun.lean
```

runs the checker alone (about 1 s) and writes `.lake/parity.json`. For a to-do list, set
`showMissingStatements := true` in the configuration (see `docs/parity.md`).

## Selecting the core

`OAMap/Core/Table.lean` selects the core with one `public import` line:

```sh
tools/select-core.sh             # print the current core
tools/select-core.sh swiss       # the SwissTable core (the selection)
tools/select-core.sh listref     # the list-backed reference core
lake build OAMapTest.CoreSpec    # the acceptance test for the selected core
```

With `listref` selected everything builds and passes except the exact slot counts in
`Unverified.lean`, which are the SwissTable core's.

### The SwissTable core

`OAMap/Core/Swiss/` (9,756 lines: 1,779 of code, the 1,349-line control-byte library `Group.lean`,
6,610 of proofs) is hashbrown's generic (non-SIMD) layout, as `docs/bakeoff/decision.md` fixes it:
a control byte per slot (EMPTY, DELETED, or FULL with a 7-bit tag of the hash) in groups of 8 read
as one word, keys and values in two arrays, load 7/8, triangular probing over groups, insertion
fast path at the home slot, tombstones by hashbrown's window rule, every rebuild into a fresh table
with no key comparison, an empty map that allocates no array, and at most one erased pair kept alive
(the placeholder of free cells) until the next rebuild. `Table.lean`'s docstring records the
layout, the algorithms, the code shape chosen by measurement and the proof structure.

* Code (`Defs`, `Loops`, `Build`, `Table`), with no `sorry`: every array bound and termination
  measure is a lemma, and every table carries its invariant `Swiss.WF` as the erased field
  `Table.wf`. Every operation runs on `USize` indices on tables of at most `2 ^ 31` slots and on
  `Nat` indices beyond (the same algorithms, executable too).
* `Group.lean`: the SWAR groups (word read through the mirrored tail, the exact per-lane tag match,
  `matchEmpty`/`matchFree`/`matchFull`, lowest lane, the triangular probe's coverage, the erase
  rule), proved without `bv_decide`.
* Proofs, eight files under `Proofs/`: `Bounds`, `Probe`, `Rebuild`, `Write`, `Bulk` (the lemmas the
  code and the contract proofs build on), and `Query`, `Update`, `Traverse` (the 22 contract
  lemmas). Each file's header describes its proof.
* The proofs ride along as erased arguments, so the generated code is the frozen version's: on the
  bake-off harness `OAMap.HashMap` executes the same instructions per operation as the frozen core
  (ratio 1.0002 over 36 cells, at most 1.0028), and `tools/check_c.py` checks the C of the API at
  `Nat` and `String` keys.

## Tools

* `tools/ci.sh`, `tools/select-core.sh`: above.
* `tools/audit.py`: text-level audit of `OAMap/` (every file is a `module`; no `sorry`, `admit`,
  `native_decide`, `bv_decide`, `implemented_by`, `extern`, `unsafe`, `partial`, `opaque`, `axiom`,
  `import all` outside comments and strings).
* `tools/port.py`, `split.py`, `portcheck.py`: the porting pipeline of `docs/proofs.md` §6 and
  ARCHITECTURE.md §6.2.
  * `python3 -I tools/port.py lemmas` regenerates `OAMap/HashMap/Lemmas/*.lean`,
    `OAMap/HashMap/Lemmas.lean` and `OAMap/HashSet/{Basic,Lemmas,DecidableEquiv}.lean` from Std's
    sources (the toolchain's `src/lean/Std/Data`). `split.py` cuts Std's `HashMap/Lemmas.lean` at
    the line numbers of ARCHITECTURE.md §2.2 and gives every file the scopes and `variable`s
    active at its cut; `port.py` keeps Std's statements and commands as text and lists candidate
    proofs for every theorem from Std's proof chain.
  * `python3 -I tools/portcheck.py [MODULE ...]` builds the generated modules in order and, for each
    theorem whose proof fails, moves to its next candidate or to a `-- REVIEW` `sorry`. Its choices
    are recorded in `tools/data/review.json`, which `port.py lemmas` reads.
  * Hand proofs (56) live in `tools/data/hand.json` (Std name ↦ the text after the statement), never
    in the generated files; `port.py` emits them and lists them in each file's docstring.
    `python3 -I tools/port.py lemmas --check` fails when a generated file differs from what
    `port.py` produces, and `tools/ci.sh` runs it, so the files are always reproducible from Std's
    sources, `tools/data/` and `hand.json`. To change a proof, edit `hand.json` and run
    `port.py lemmas --force`.
  * The original study scripts (`chain.py`, `extract.py`, `extract2.py`, `classify.py`,
    `classify2.py`, `secdeps.py`) and their JSON inputs (`tools/data/`) are kept; from
    `tools/data/`, `python3 -I ../port.py hmchain.json dhm.json raw0.json hm.json all_hm.json
    OUT.lean` still reproduces the study's `auto_all.lean` exactly.
* `tools/gen_basic.py`: generates `OAMap/HashMap/Basic.lean` and `AdditionalOperations.lean`
  from Std's text (`python3 -I tools/gen_basic.py STD_DATA_DIR tools/inventory.json
  OAMap/HashMap`; it reproduces the committed files exactly, which `tools/ci.sh` checks).
* `tools/srccheck.py`: checks the source text and attributes of the 16 iterator declarations that
  parity ignores against `inventory.json`.
* `tools/check_c.py`: checks the C that Lean generates for the API at `Nat` and `String` keys
  (`bench/Bench/CCheck.lean`, one monomorphic function per operation; `lake build Bench.CCheck`
  first). From each function it follows the direct calls and fails on a closure call
  (`lean_apply_*`), on an allocation in a lookup (outside the `Nat`-indexed probes of tables of
  more than `2 ^ 31` slots), on an array shared right before its in-place update (the bake-off's
  "bug A"), and on an update that does not reuse its unshared table cell.
* `tools/inventory.json`: the API to reproduce, with Std's exact signatures and attributes.
