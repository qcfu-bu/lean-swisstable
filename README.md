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

Status: Wave 0. The reference core `OAMap.Core.ListRef` implements the core contract and passes
`test/OAMapTest/CoreSpec.lean`; every other library module is a stub.

## Build and test

```sh
lake build                 # the library OAMap (default target): every proof
lake test                  # the test library OAMapTest (below)
tools/ci.sh                # both, plus the source-text checks
```

`lake test` builds `test/OAMapTest.lean`, whose modules log an error (failing the build) when
their check fails:

| module | check |
|---|---|
| `CoreSpec` | the selected core provides the 23 definitions and 22 lemmas of the contract (§3.4) |
| `SealCheck` | modules above the core use only the 45 contract names, import no core directly, and never `import all` |
| `Audit` | every constant of `OAMap` uses only `propext`, `Classical.choice`, `Quot.sound`; no axiom, `opaque`, `partial`, `unsafe`, `implemented_by`, `extern` |
| `ParityRun` | statement, attribute and axiom parity with `Std.HashMap`/`Std.HashSet` |
| `Cbv`, `Unverified` | stubs (Wave 3) |

**Gates until the Merge phase.** `ParityRun` is built and run by every `lake test`, but its
`failOnError := false` and `maxShow := 5` lines (marked `-- GATE`) keep missing declarations and
`sorry` from failing the build. `Audit` likewise only lists `sorry` while `failOnSorry := false`.
At the Merge, delete the two GATE lines of `test/OAMapTest/ParityRun.lean` and set
`failOnSorry := true` in `test/OAMapTest/Audit.lean`.

## Parity

```sh
lake build OAMap Parity && lake env lean test/OAMapTest/ParityRun.lean
```

runs the checker alone (about 1 s) and writes `.lake/parity.json`. For a to-do list, set
`maxShow := 0` and `showMissingStatements := true` in the configuration (see `docs/parity.md`).

## Selecting the core

`OAMap/Core/Table.lean` selects the core with one `public import` line:

```sh
tools/select-core.sh             # print the current core
tools/select-core.sh listref     # the reference core (default)
tools/select-core.sh linear      # a bake-off core, once OAMap/Core/Linear.lean exists
lake build OAMapTest.CoreSpec    # the acceptance test for the selected core
```

## Tools

* `tools/ci.sh`, `tools/select-core.sh`: above.
* `tools/audit.py`: text-level audit of `OAMap/` (every file is a `module`; no `sorry`, `admit`,
  `native_decide`, `implemented_by`, `extern`, `unsafe`, `partial`, `opaque`, `axiom`,
  `import all` outside comments and strings).
* `tools/port.py`, `chain.py`, `extract.py`, `extract2.py`, `classify.py`, `classify2.py`,
  `secdeps.py`: the porting pipeline of `docs/proofs.md` §6 and ARCHITECTURE.md §6.2. Their
  JSON inputs, extracted from Std's sources, are in `tools/data/`. For example, from `tools/data/`,
  `python3 -I ../port.py hmchain.json dhm.json raw0.json hm.json all_hm.json OUT.lean` ports all
  678 HashMap lemmas (the study's `auto_all.lean`).
* `tools/inventory.json`: the API to reproduce, with Std's exact signatures and attributes.
