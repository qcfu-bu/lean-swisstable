# Parity: a statement-parity checker for `OAMap` against `Std.HashMap`/`Std.HashSet`

`Parity.lean` is a Lean 4.35 meta-program (it imports only `Lean`). `Parity.run cfg` goes
through every public Std declaration under the source namespaces, translates its elaborated type
into the candidate's vocabulary, and compares the result with the candidate's declaration of
the same name. Each run prints a report and can also write JSON. `lean` exits with status 1 when
any check fails with an error, so the checker can gate CI.

## Files (all in this directory)

| file | role |
|---|---|
| `Parity.lean` | the checker |
| `ParityMock.lean` | the mock candidate library: `OAMap.HashMap` over a list model, with planted differences |
| `ParityRunMock.lean` | runs the checker on the mock, restricted to the 26 Std declarations the mock copies |
| `ParityRunMockFull.lean` | the mock against all 1134 Std declarations, at most 8 entries shown per section |
| `ParityMockExtra.lean` | self-contained second mock covering the other kinds of difference |
| `ParitySelfTest.lean` | Std against itself (identity renaming): every declaration must pass |
| `ParityStressExt.lean` | real-data stress test: `Std.HashMap` against `Std.ExtHashMap` |
| `parity-*.txt`, `parity-*.json` | recorded outputs |

## Running

Each step is a single `lean` process of 1–2 s; nothing goes through lake.

```sh
cd /private/tmp/claude-501/-Users-qcfu-Projects-wnetkat/285881d0-ec47-495c-9169-fcc228e9dc96/scratchpad/arch
export LEAN_PATH="$PWD"              # so that `import Parity` / `import ParityMock` resolve
lean -o Parity.olean Parity.lean     # compile the checker once
lean -o ParityMock.olean ParityMock.lean
lean ParityRunMock.lean              # the mock report (exit status 1: it has errors)
lean ParitySelfTest.lean             # 1134 Std declarations, 1134 ok
lean ParityMockExtra.lean            # the other difference kinds
```

On the real library, put `Parity.lean` in the package as its own `lean_lib Parity` (or in a
test directory), and keep the driver out of the library build:

```lean
-- ParityRun.lean
import Std
import OAMap
import Parity

#eval Parity.run {
  jsonOut := some "parity.json" }
```

Then run `lake build OAMap Parity && lake env lean ParityRun.lean`.

**Struct-literal pitfall.** In `Parity.run { … }`, every field that starts a new line must begin at
or right of the column of the first field. Writing `#eval Parity.run { a := 1,` and then `b := 2 }`
on a less-indented line fails with "unexpected identifier; expected '}'". Put `{` at the end of
the `#eval` line and indent all the fields equally, as in `ParityRunMock.lean`.

## Configuration (`Parity.Config`)

| field | default | meaning |
|---|---|---|
| `nsMap` | `Std.HashMap ↦ OAMap.HashMap`, `Std.HashSet ↦ OAMap.HashSet` | prefix renaming applied to every constant (longest prefix wins) |
| `constMap` | `#[]` | explicit renamings; they take precedence over `nsMap` |
| `extraDecls` | `#[]` | Std declarations outside the namespaces to check as well, with their counterparts, e.g. `(`List.groupByKey, `OAMap.List.groupByKey)` |
| `exclude` | `Std.HashMap.Raw`, `Std.HashSet.Raw`, `….Internal` | Std prefixes that are not checked (deferred APIs) |
| `ignore` | `#[]` | exact Std names that are not checked |
| `only` | `#[]` | when nonempty, check only these Std names |
| `checkTheorems` / `checkDefs` / `checkInstances` | `true` | the three sections |
| `checkStructureInternals` | `false` | also check constructors, projections, `rec`, `casesOn`, `noConfusion`, `mk.inj…` |
| `checkBinderNames` | `true` | report renamed binders (they break named arguments `(hab := h)`) |
| `checkUniverseOrder` | `true` | report universe parameters listed in another order |
| `reportExtras` | `true` | list our public declarations that have no Std counterpart |
| `checkAxioms` | `true` | report our theorems that depend on `sorryAx` (error) or on non-standard axioms (warning) |
| `skipDeprecated` | `false` | skip Std declarations tagged `@[deprecated]` |
| `showMissingStatements` | `false` | print the translated Std type of each missing declaration (a to-do list) |
| `verbose` | `false` | also list the declarations that pass |
| `maxShow` | `0` | maximal number of entries printed per section (`0` = all) |
| `failOnError` | `true` | log an error at the end, so that `lean` exits with status 1 |
| `jsonOut` | `none` | write `{entries: [{kind, std, ours, status, issues: [{severity, tag, lines}]}], extras}` |

## What is compared

**Translation.** Every constant `c` in Std's elaborated type becomes `constMap[c]`, else the
`nsMap` renaming of `c`, else stays as is (so `List`, `BEq`, `EquivBEq` and so on are left
alone). Instances are matched by name first. When the name differs, the checker looks for an
instance of ours whose type equals the translated type, and failing that for the closest
instance of the same class. Either way it adds the pair to the renaming, so statements that
mention the instance still compare (`m[a]?` mentions the `GetElem?` instance). `match`
auxiliaries (`foo.match_1`) are matched by their definition (type and value), because Lean
numbers them per declaration and shares identical ones across declarations. Universe
parameters are matched by order of first occurrence in the types, so `universe v u` against
Std's `universe u v` still pairs `{α : Type u}` with `{α : Type u}`. This works both for the
declaration's own parameters and for the universe arguments of every translated constant.
A different order is reported as a warning, since only an explicit `.{u}` would notice it.

**Equality.** The two types are equal if they are the same tree after removing metadata,
ignoring binder names (alpha-equivalence) and treating proofs inside statements as equal. Proof
irrelevance is implemented by erasing every application of a theorem, which also covers the
`_proof_i` auxiliaries that Lean abstracts out of statements. Binder infos (explicit, `{}`,
`⦃⦄`, `[]`), `optParam` default values and `autoParam` tactics count. Levels are compared up to
normalisation.

**Binder alignment.** The ∀-telescopes are aligned rather than zipped, so a single change is
reported once instead of as a cascade:

* `extra-hypothesis`: a binder of ours with no Std counterpart (always an error).
* `missing-hypothesis`: a Std binder that ours lacks. A missing explicit binder is an error; an
  implicit or instance binder is a warning, because ours is then a more general lemma.
* `binder-order`: the same binder at another position. Once relinked, the binders that follow
  are compared normally.
* `binder-info`: the same type with another binder kind.
* `binder-type`: another type, shown with a diff; `binder-default`: a changed default value.
* `binder-name`: a renamed binder (warning).
* `conclusion`: the conclusion differs.

**Diffs.** Each mismatch prints both statements and then the smallest pair of differing
subterms. The search descends while exactly one component differs, or exactly one explicit
argument; for `ite`, the condition counts but its `Decidable` instance does not. The terms are
printed with `pp.explicit`, then `pp.all`, when the plain printing hides the difference. When
the binders line up but the statements differ syntactically, the checker tries `isDefEq` at
`instances` transparency. If that succeeds, it downgrades the difference to a warning and adds
`defeq-only`, because `rw` and `simp` may still behave differently.

**Attributes**, compared as sets of facts:

* every registered simp set (`simp`, `seval`, …, plus grind's normaliser), with `↓`, `←` and
  priority, and the simp discrimination keys (they change when ours unfolds differently);
* every grind set (`grind`, `lia`, …), with its kind (`=`, `=_`, `_=_`, `←`, `→`, `.`, …), `!`,
  `ext`, `cases`, `inj` and `funCC`, and the grind patterns of entries of the same kind;
* `cbv_eval` (and `←`), `cbv_opaque`, `defeq` (whether `dsimp` can use the lemma), `refl`,
  `symm`, `ext` (with priority), `elab_as_elim`, `induction_eliminator`/`cases_eliminator`,
  `congr`, and `deprecated` (with the replacement name translated);
* instance priority and scope, reducibility (`@[reducible]`, `@[instance_reducible]`, …),
  `protected`, `noncomputable` and `class`.

A missing attribute is an error, except `deprecated` and reducibility, which are warnings.
An extra attribute is an error too, since it changes what `simp` and `grind` do. Two facts are
asymmetric: an extra `@[defeq]` is only info, and `noncomputable` is an error only when ours
has it and Std's does not.

**Definitions and instances** are checked by signature (type), kind and attributes. Their
values are not compared, except for notation declarations (`ParserDescr`), whose parser
description is compared. Inductive types (`HashMap`, `HashSet`, `Equiv`) are checked by type.
Their constructors and projections are internals and are skipped by default.

**Root causes.** When a statement mentions a Std operation whose own signature differs (for
example `ExtHashMap.insert` takes extra instance arguments), the entry gets a `root-cause` note
that names that operation.

## Output on the mock (`lean ParityRunMock.lean`, recorded in `parity-mock-output.txt`)

| planted in `ParityMock.lean` | reported |
|---|---|
| `getElem?_insert`: `a == k` instead of `k == a` | `ERROR [conclusion]`, first difference `k == a` vs `a == k` |
| `size_insert` with `[Inhabited α]` | `ERROR [extra-hypothesis] ours has an extra binder #6: [Inhabited α]` (plus `axioms: sorryAx`, since its proof is `sorry`) |
| `getElem?_insert_self` missing | `MISSING` |
| `contains_insert` without `cbv_eval` | `ERROR [attribute] Std has @[cbv_eval], ours does not` |
| `isEmpty_insert` with `[BEq α] [Hashable α]` | `ERROR [binder-info] … Std has it implicit, ours instance implicit` |
| `getElem?_congr` with `(h : …)` | `WARN [binder-name] … breaks named arguments (hab := _)` |
| `emptyWithCapacity (capacity := 16)` | `ERROR [binder-default]`, first difference `8` vs `16` |
| `getD` missing | `MISSING` |
| no `Inhabited (HashMap α β)` | `MISSING` instance, with the expected type |
| `GetElem?` instance named `instGetElemOpt` | `WARN [renamed]`; the `m[a]?` lemmas still pass |
| extra `getElem?_eq_find?` | listed under extras |

The other 16 declarations pass, including their attributes (for example `get?_eq_getElem?` has
`@[simp]`, `@[grind =]` and `@[defeq]` on both sides). The summary line reads
`26 Std declarations, 16 ok, 8 with errors (3 missing), 2 with warnings only`. While the mock
was being written, the checker also caught two slips I had not planted. A `sorry` inside the
mock's `get` reached every lemma that mentions `m[a]?`, through the `GetElem?` instance. And
`get` had a binder named `_h` where Std has `h`.

`ParityMockExtra.lean` (recorded in `parity-mockextra-output.txt`) covers the other kinds:
a missing `@[simp]`, `grind =` where Std has `grind _=_`, a dropped instance hypothesis
(warning), a dropped explicit hypothesis (error), two instance hypotheses swapped
(`binder-order`), an unfolded statement (`defeq-only` warning), an `abbrev` (reducibility
warning), and universes declared in another order (warnings only, no cascade). It also has a
statement with a `match` and a proof term inside (`keys_filter`), where Lean reused another
declaration's matcher; the statement passes.

## Validation

* `ParitySelfTest.lean`: all 1134 Std declarations pass against themselves (4 types, 35
  instances, 81 definitions, 1014 theorems), so the attribute and alignment code raises no false
  alarms on Std's real statements.
* `ParityStressExt.lean`: `HashMap ↦ ExtHashMap` gives 762 declarations, 252 missing and 504
  with genuine differences, mostly the extra `[EquivBEq α] [LawfulHashable α]`. It is the test
  that showed the need for relinking moved binders (`ExtHashMap` puts `{β}` after the instance
  binders) and for the root-cause note.
* `ParityRunMockFull.lean`: the whole of Std against the mock runs in about 1.8 s.

## Not checked, and caveats

* Proofs, docstrings and compiler attributes (`@[inline]`, `@[specialize]`, `@[expose]`,
  `implemented_by`) are not compared. Neither are the bodies of definitions, so `rfl`-level
  behaviour is covered only through the `@[defeq]` fact and the simp keys.
* Notation is compared through its `ParserDescr` declaration (precedence and tokens), not its
  `scoped` status.
* Only the source namespaces are scanned. Some Std API outside them produces the map types:
  `List.groupByKey`, `Array.groupByKey`, `Std.Iter.toHashSet`, `Std.IterM.toHashSet`,
  `Std.Iter.Total.toHashSet`, `Std.IterM.Total.toHashSet`, `Std.IterM.toHashSet_eq_fold`. Pass
  such declarations in `extraDecls` if ours provides counterparts. `ExtHashMap` is not scanned.
* Universe parameters are matched by first occurrence, which is a heuristic. Constants whose
  numbers of universe parameters differ are compared positionally, with an error.
* The `defeq-only` downgrade is skipped for statements that contain erased proofs.
* The Iterator API (`iter`, `keysIter`, …) exposes `Std.DHashMap.Internal.AssocList` types, which
  an open-addressing table cannot match. Add those names to `ignore` or `exclude`, or give them
  counterparts in `constMap`.
