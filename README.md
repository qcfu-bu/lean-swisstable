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

Status: Waves 1 and 2 merged, against the reference core `OAMap.Core.ListRef` (the layout-specific
core comes from the benchmark bake-off). Every proof is complete: no `sorry`, and every constant
of the library depends only on `propext`, `Classical.choice` and `Quot.sound`. Parity with Std
reports 1118 of 1118 Std declarations ok, 0 missing and 0 extras. The nine
`HashMap/Lemmas/*.lean` files and `HashSet/{Basic,Lemmas,DecidableEquiv}.lean` are generated from
Std's text (below), with hand proofs where no generated proof compiled (each file's docstring
lists them). The array iterators, their lemmas, `OAMapTest/Cbv.lean` and `Unverified.lean` are
written; `bench/` is still a stub.

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
| `Cbv` | `by cbv` closes the same goals as on Std |
| `Unverified` | `#guard` tests for the functions without Std lemmas |

**Gates (on since the Merge).** `ParityRun` fails on any difference from Std outside its `ignore`
list (the 16 iterator declarations, checked by `tools/srccheck.py`): errors, warnings and extras
(`failOnWarning := true`). `Audit` fails on any dependency on `sorryAx` (`failOnSorry := true`).

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
tools/select-core.sh listref     # the reference core (default)
tools/select-core.sh linear      # a bake-off core, once OAMap/Core/Linear.lean exists
lake build OAMapTest.CoreSpec    # the acceptance test for the selected core
```

## Tools

* `tools/ci.sh`, `tools/select-core.sh`: above.
* `tools/audit.py`: text-level audit of `OAMap/` (every file is a `module`; no `sorry`, `admit`,
  `native_decide`, `implemented_by`, `extern`, `unsafe`, `partial`, `opaque`, `axiom`,
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
    are recorded in `tools/data/review.json`, which `port.py lemmas` reads, so the generated files
    are reproducible. A proof fixed by hand in Wave 2 replaces the generated text in the file;
    after that, do not regenerate that file (or add the proof to `OVERRIDES` in `port.py`).
  * The original study scripts (`chain.py`, `extract.py`, `extract2.py`, `classify.py`,
    `classify2.py`, `secdeps.py`) and their JSON inputs (`tools/data/`) are kept; from
    `tools/data/`, `python3 -I ../port.py hmchain.json dhm.json raw0.json hm.json all_hm.json
    OUT.lean` still reproduces the study's `auto_all.lean` exactly.
* `tools/gen_basic.py`: generates `OAMap/HashMap/Basic.lean` and `AdditionalOperations.lean`
  from Std's text (`python3 -I tools/gen_basic.py STD_DATA_DIR tools/inventory.json
  OAMap/HashMap`; it reproduces the committed files exactly).
* `tools/srccheck.py`: checks the source text and attributes of the 16 iterator declarations that
  parity ignores against `inventory.json`.
* `tools/inventory.json`: the API to reproduce, with Std's exact signatures and attributes.
