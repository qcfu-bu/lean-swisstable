# SwissTable

A verified, drop-in replacement for `Std.HashMap` and `Std.HashSet` for Lean 4 (v4.35.0, core
and Std only, no Mathlib). `SwissTable.HashMap α β` and `SwissTable.HashSet α` have Std's
operations, instances and all of Std's lemmas, with identical names, statements, binders and
attributes. On the benchmark below they take about 0.55× the time of Std's maps.

```lean
import SwissTable.HashMap        -- instead of `import Std.Data.HashMap`

def m : SwissTable.HashMap String Nat := (∅ : SwissTable.HashMap String Nat).insert "a" 1

example : m["a"]? = some 1 := by simp [m]   -- Std's simp lemmas, under the same names
```

```toml
# lakefile.toml of a project that uses it
[[require]]
name = "swisstable"
path = "../lean-swisstable"
```

`DHashMap`, the `Raw` maps and the `Ext` maps are not provided.

## What "drop-in" and "verified" mean here

* **Same declarations.** A checker (`test/Parity.lean`, run by `lake test`) compares every public
  theorem, definition and instance of `Std.HashMap`/`Std.HashSet` with ours, after renaming
  `Std.HashMap ↦ SwissTable.HashMap`: 1140 of 1140 match, with no extras. Code written against Std
  compiles against SwissTable, and so do its proofs.
* **Same semantics where the lemmas fix it.** `insert` replaces the stored key and value,
  `insertIfNew` and `HashSet.insert` keep the old entry, `union` is right-biased, `ofList` keeps the
  last duplicate, and so on. No `Inhabited` requirement is added.
* **Fully proved.** No `sorry`. Every constant depends only on `propext`, `Classical.choice` and
  `Quot.sound`. There is no `native_decide`, `bv_decide`, `implemented_by`, `extern`, `unsafe`,
  `partial` or `opaque`. The `_unsafe_rec` helpers that Lean's compiler generates for well-founded
  definitions are the only exception, and the audit allows them only for such definitions. The
  compiled code is the code the proofs are about.
* **Known differences from Std.**
  * The iteration order is different (Std leaves it unspecified).
  * `Repr` prints `SwissTable.HashMap.ofList …`.
  * The `inner` field of a map has a different type, as does the state type of the iterators.
  * After an `erase`, the table may keep one reference to the erased key and value until it next
    rebuilds; values that release a resource when freed (such as file handles) can notice this.

## Structure

```
SwissTable/
  Core/Swiss/   the table: a SwissTable with its invariant and proofs   ← the only layout-specific part
  Core/Table    the one line that selects the core
  Core/ListRef  a list-backed reference core with the same interface (for testing)
  Core/Derived, Core/Bulk   queries, traversals, insertMany/union/inter/diff, on top of the core
  HashMap/      Std's API (Basic), the model bridge and tactic, and Std's lemmas (Lemmas/)
  HashSet/      Std's HashSet over HashMap α Unit, as in Std
test/           parity checker, contract test, axiom audit, seal check, #guard tests
tools/          lemma generator, audits, C check, CI script
bench/          SwissTable.HashMap against Std.HashMap
```

**The core contract.** Everything above `Core/` sees the table only through 23 definitions
(`lookup`, `insert`, `erase`, `alter`, `filter`, `foldM`, …) and 22 lemmas. The lemmas relate
each operation to a list model `toListModel : Table α β → List ((_ : α) × β)`. For example,
inserting permutes the model into `insertEntry k v` of the old model. These are the list functions
of `Std.Internal.List`, the same model Std's own proofs use.

* Lemmas about the queries and operations hold under `[EquivBEq α] [LawfulHashable α]`, where
  Std's do. Lemmas about traversals and filtering hold for any `BEq`/`Hashable`, as Std's do.
* The table bundles its invariant, and the part that needs lawful instances is stated only under
  them. So the operations themselves need no lawfulness, again as in Std.
* `SealCheck` makes sure nothing above the core uses anything else, so a different core can be
  slotted in by changing `Core/Table.lean`. The list-backed `ListRef` core passes the same contract
  test.

**Std's lemmas, reused.** Std proves its map lemmas in layers, ending in proofs of the form
`simp_to_model [insert, get?] using List.getValue?_insertEntry`: rewrite to the list model, then
apply a lemma about lists. SwissTable keeps that bottom layer. A copy of the `simp_to_model`
tactic (`HashMap/Tactic.lean`) runs over our model lemmas, with Std's own `using` terms.
`tools/port.py` generates `HashMap/Lemmas/*.lean` and `HashSet/*.lean` from Std's source text, so
the statements are Std's character for character. 56 lemmas needed a short hand proof; they are
kept in `tools/data/hand.json`. `tools/ci.sh` checks that the generated files are exactly what the
generator produces.

## The SwissTable core

The layout is Abseil's SwissTable in the portable, non-SIMD form of Rust's hashbrown.

* **Arrays.** For `cap = 2^lg` slots there are three arrays:
  * `ctrl : ByteArray` of `cap + 8` bytes, one control byte per slot;
  * `slotKeys` and `slotVals`, of `cap + 1` cells each.
* **Control bytes**, hashbrown's encoding: `0xFF` empty, `0x80` deleted (a tombstone), and
  `0b0hhhhhhh` full, where `hhhhhhh` is a 7-bit tag from the key's hash.
* **Hash split.** `q = (hash k * ⌊2^64/φ⌋) >>> (57 − lg)` keeps the top `lg + 7` bits of a
  Fibonacci product. The home slot is `q >>> 7` and the tag is `q &&& 0x7F`, so both depend on
  every bit of the hash; Lean's `hash` on a `Nat` is the identity.
* **Lookup.** Probe groups of 8 slots, in triangular steps (`+8, +16, +24, …` modulo `cap`).
  * In each group, compare the key at every slot whose control byte equals the tag, lowest first.
  * Stop at the first group that contains an empty byte.
* **Insert.** The same probe also remembers the first free slot it passes.
  * A hit replaces the key and value.
  * A new key goes into the first free slot.
  * Fast path: when the home slot is empty and nothing in its group has the tag, the key is new
    and is written there with no probe.
  * Load limit 7/8. When the table is full, it rebuilds into fresh arrays: at the same capacity
    if at most half full, otherwise at twice the capacity.
* **Erase.** Writes empty when every 8-slot window around the slot already has another empty
  slot, since then no probe can have passed through it (hashbrown's rule). Otherwise it writes a
  tombstone. Once tombstones exceed a quarter of the capacity, the next insert that needs an empty
  slot rebuilds.
* **Rebuild.** Moves every entry into fresh arrays without comparing keys.
* **Traversals** (`fold`, `forIn`, `toList`, …) scan a group at a time.
* **`filter` and `map`** work in place: they mark slots or rewrite the value array.

### Making it work in Lean, on a `ByteArray`

**One load per group.** Core Lean only has byte-level `ByteArray.uget`. Eight of them at
consecutive indices, shifted and OR'ed together, compile to one unaligned 64-bit load under
Lake's default `-O3 -DNDEBUG`:

```lean
@[inline] def ctrlWord (c : @& ByteArray) (i : USize) (h : i.toNat + 8 ≤ c.size) : UInt64 :=
  (c.uget i _).toUInt64 ||| ((c.uget (i + 1) _).toUInt64 <<< 8) ||| … |||
  ((c.uget (i + 7) _).toUInt64 <<< 56)          -- arm64: a single `ldr x0, [x8, #24]`
```

**A mirrored tail, so a group never wraps.**
* Bytes `cap .. cap+7` repeat bytes `0 .. 7`, so the 8 bytes from any slot are in the array.
* `setCtrl` writes slot `i` and its copy at index `((i − 8) &&& mask) + 8`. That index is
  `i + cap` for `i < 8` and `i` otherwise, so the second write needs no branch.

**Matching 8 bytes at once (SWAR).** With `y = group ^^^ tag · 0x0101…01`:

```lean
matchTag g rep := let y := g ^^^ rep; ~~~(((y &&& 0x7F7F…7F) + 0x7F7F…7F) ||| y) &&& 0x8080…80
matchEmpty g   := g &&& (g <<< 1) &&& 0x8080…80     -- bytes 0xFF
matchFree g    := g &&& 0x8080…80                   -- bytes 0xFF or 0x80
```

* Bit `8j+7` of each result says whether byte `j` qualifies.
* The tag match is exact: no byte's sum can carry into the next byte. hashbrown's cheaper form,
  `(y − 0x0101…01) &&& ~~~y &&& 0x8080…80`, can borrow across bytes and wrongly flag a byte just
  above a match. The exact form costs one more instruction per group and never makes a wasted key
  comparison.
* Because no carry crosses bytes, each fact has a one-byte proof that the kernel checks over all
  256 byte values (`decide +kernel`). `bv_decide` is not used, because its proofs depend on an
  extra axiom.

**The lowest flagged byte, without a loop.** `UInt64.log2` compiles to a bit-by-bit loop, so it
isn't used. Instead:

```lean
lowestLane m := (((m &&& (0 − m)) >>> 7) * 0x0001020304050607) >>> 56
```

* `m &&& (0 − m)` isolates the lowest flag, `2^(8j+7)`.
* Shifting it right by 7 gives `256^j`.
* Multiplying by `0x0001020304050607` moves the byte holding `j` to the top.
* `m &&& (m − 1)` then clears that flag, so the next match comes out lowest first.

**Allocation without `replicate` or `Inhabited`.**
* Core Lean has no `ByteArray.replicate`, so a table's control bytes are built by repeatedly
  appending an 8-byte all-empty group to itself, which is `memcpy` doubling.
* The empty map (`∅`, `emptyWithCapacity`) allocates no array at all. Its control bytes are one
  shared all-empty group with `mask = 0`, so every probe of it stops in its first group without
  reading a key, and the queries need no special case.
* The first insert allocates the table and fills the empty cells of `slotKeys`/`slotVals` with
  its own key and value. Every rebuild refreshes that placeholder pair, which is why no
  `Inhabited α` is needed.

**Machine-word indices with a proof.**
* Every operation runs on `USize` indices with `uget`/`uset` and bounds proofs, on tables of up to
  `2^31` slots, where no index computation can wrap on any platform.
* Beyond that it runs the same algorithms on `Nat` indices; one test per operation chooses.
* Updates happen in place when the table is unshared.
* The proofs are erased arguments, so the generated C is the same code as an unverified version.
  `tools/check_c.py` checks it at `Nat` and `String` keys:
  * no closure calls;
  * no allocation on a lookup;
  * no array shared just before its in-place update;
  * the table cell reused on update.

## Compared with `Std.HashMap`

| | `Std.HashMap` | `SwissTable.HashMap` |
|---|---|---|
| layout | array of buckets, each a linked list of cells | control bytes + key array + value array |
| per entry | one heap cell (key, value, next) | one key cell and one value cell in the arrays, plus 1 control byte |
| collisions | walk the bucket's list, comparing every key | 8 slots per step, keys compared only on a 7-bit tag match |
| growth | at 3/4 load, rehash every key | at 7/8 load, rebuild into a fresh table, rehash every key |
| erase | unlink the cell | empty slot or tombstone |
| freeing a map | one free per entry | three arrays |
| iteration | bucket order | slot order, a group at a time |
| `Inhabited` needed | no | no |

**Speed.** The benchmark covers:
* 16 workloads;
* 5 key types: random `Nat`, a flat 8-field structure, an 8-field structure behind an array,
  `String`, and the consecutive `Nat`s `0 .. n−1`;
* 8 sizes from 10³ to 10⁷;
* one process per cell, taking the minimum ns per operation over repetitions, on an Apple M5 Pro.

Ratios are SwissTable/Std; below 1 means faster. The middle column is the geometric mean over the
4 non-consecutive key types at all 8 sizes:

| workload | SwissTable / Std | worst cell |
|---|---|---|
| lookup hit, shuffled (`getD` / `get?`) | 0.68 / 0.50 | 1.08 / 0.74 |
| lookup hit, insertion order (`getD` / `get?`) | 0.76 / 0.48 | 1.65 / 0.72 |
| lookup miss | 0.58 | 1.20 |
| insert into `∅` / into `emptyWithCapacity n` | 0.69 / 0.84 | 0.94 / 1.11 |
| update existing keys | 0.52 | 0.85 |
| lookup-or-insert (`getThenInsertIfNew?`) | 0.57 | 0.78 |
| erase half / erase all | 0.66 / 0.72 | 1.29 / 1.63 |
| lookups after erasing half | 0.85 | 1.37 |
| insert-and-erase churn / lookups after churn | 0.75 / 0.82 | 1.25 / 1.21 |
| `fold` | 0.20 | 0.59 |
| freeing the map | 0.10 | 0.39 |
| **all 512 cells** | **0.55** | 23 cells above 1.10 |

For example, at 10⁶ random `Nat` keys (ns per operation, Std → SwissTable):

| operation | Std | SwissTable |
|---|---|---|
| shuffled `getD` | 14.8 | 9.3 |
| miss | 11.0 | 2.4 |
| insert | 44.9 | 23.5 |
| erase | 46.4 | 23.8 |
| `fold` | 9.2 | 1.6 |

Where Std is faster:
* **Consecutive `Nat` keys** (`0 .. n−1`). Std's bucket index keeps them in sequential buckets.
  SwissTable's multiplicative hash spreads them, which costs locality. Over all such cells the two
  are even (1.00), but at 10⁶ entries and more, in-order lookups and pre-sized inserts are
  4–12× slower.
* **A few small in-cache cells:** erasing from a map at load 3/4 (up to 1.63×), lookups after many
  erases with no insert in between (up to 1.37×), and in-order `getD` at about 1000 entries (up
  to 1.65×, under 1 ns more per lookup).
* **Expensive keys during growth.** Hashes are not stored, so a rebuild hashes every key again, as
  Std does. For keys whose hash is expensive, cache it in the key.

**Memory** per entry, at 10⁵ entries and more:

| map | SwissTable / Std |
|---|---|
| built with `emptyWithCapacity n` | 0.63× (e.g. 30 against 46 bytes at 10⁷) |
| grown from `∅` | 1.03× |

A map that is shared when updated is copied first, as with Std. With `String` keys such a copy
costs 3–5× Std's: copying the arrays touches every key and value object to raise its reference
count, placeholders included, and these objects are scattered in memory. With `Nat` keys a copy
is cheaper than Std's.

`lake exe swisstable-bench` runs a smaller version of this benchmark (`rand` and `String` keys,
10³–10⁶, under a minute); `swisstable-bench compare --keys … --sizes … --workloads …` selects cells.

## Building and checking

```sh
lake build                 # the library and every proof
lake test                  # parity with Std, contract, axiom audit, seal, #guard tests
lake exe swisstable-bench  # SwissTable.HashMap against Std.HashMap
tools/ci.sh                # all of the above, plus the source audit, the lemma-generator check
                           # and the generated-C check
```

The design notes, the proof architecture and the raw benchmark data are in `docs/`.
