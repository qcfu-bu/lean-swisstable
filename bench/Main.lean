module

public import Bench
public import Std.Data.HashMap
public import SwissTable.HashMap

/-!
# SwissTable versus Std: timings

`SwissTable.HashMap` against `Std.HashMap` on the workloads of the bake-off harness (`oabench2`,
`docs/bakeoff/`): `Bench/Keys.lean`, `Bench/Iface.lean`, `Bench/Loops.lean` and `Bench/Run.lean`
are its harness modules without the hardware counters. The workloads are written once against the
class `Bench.BenchMap` and `@[specialize]`d, and `bench_map` derives the instance from each map's
own operations, so the loops below are compiled at each map type with the key type's `hash` and
`==` called directly. Not gating (`docs/ARCHITECTURE.md` §9.4); rough timings.

    lake exe swisstable-bench                  # the default comparison (under a minute)
    lake exe swisstable-bench compare [--keys rand,string] [--sizes 1000,100000,1000000]
                                      [--workloads insert,getd-shuf,...] [--reps 3] [--min-ms 100]
    lake exe swisstable-bench <std|swisstable> <dense|rand|string|struct|flat> <n> <workload>
                                      [--reps R] [--min-ms T] [--iters I]

`compare` runs every cell in its own process (this executable again, with the map, key, n and
workload as arguments), Std and SwissTable alternately first, and prints the minimum ns per
operation of each, their ratio, the geometric mean of the ratios per workload and overall, and any
cell whose checksums differ between the two maps. The single-cell form prints the harness's `RESULT`
line. One operation is one map call; the workloads are listed in `Bench/Run.lean` (`genInputs`) and
in the harness's README: `insert` and `insert-cap` build maps of `n` fresh keys (from `∅` and from
`emptyWithCapacity n`), `getd`/`getopt` look up every key (in insertion order, or shuffled with
`-shuf`), `miss` looks up absent keys, `reinsert` overwrites every key, `hashcons` runs
`getThenInsertIfNew?` over new and repeated keys, `fold` sums the values, `free` drops the maps, and
the erase workloads erase every other key (`erase-alt`, then shuffled lookups of all keys in
`erase-alt-get`), every key (`erase-all`), or insert a new key and erase the oldest on a map of `n`
keys (`churn`, then lookups of the live and the last erased keys in `churn-get`). Keys: `rand`
(random `Nat`s), `dense` (`0 .. n-1`), `string` (`"key-" ++ toString i`), `struct` (an array of
eight boxed `UInt64`s) and `flat` (eight unboxed `UInt64` fields). `mem` and `mem-cap` build one map
untimed, for measuring the process's memory with `/usr/bin/time -l`.
-/

bench_map Std.HashMap
bench_map SwissTable.HashMap

namespace Bench.Compare

/-- The cells of `swisstable-bench` with no arguments. -/
def defaultKeys : List String := ["rand", "string"]
def defaultSizes : List Nat := [1000, 100000, 1000000]
def defaultWorkloads : List String :=
  ["insert", "insert-cap", "getd-shuf", "getopt-shuf", "miss", "reinsert", "hashcons", "fold",
   "erase-alt", "erase-alt-get", "churn", "churn-get", "erase-all"]

structure Opts where
  keys : List String := defaultKeys
  sizes : List Nat := defaultSizes
  workloads : List String := defaultWorkloads
  reps : Nat := 3
  minMs : Nat := 100

def csv (s : String) : List String := (s.splitOn ",").filter (· ≠ "")

def parse : List String → Opts → Except String Opts
  | [], o => .ok o
  | "--keys" :: v :: rest, o => parse rest { o with keys := csv v }
  | "--workloads" :: v :: rest, o => parse rest { o with workloads := csv v }
  | "--sizes" :: v :: rest, o =>
    match (csv v).mapM String.toNat? with
    | some ns => parse rest { o with sizes := ns }
    | none => .error s!"bad --sizes {v}"
  | "--reps" :: v :: rest, o =>
    match v.toNat? with
    | some r => parse rest { o with reps := r }
    | none => .error s!"bad --reps {v}"
  | "--min-ms" :: v :: rest, o =>
    match v.toNat? with
    | some r => parse rest { o with minMs := r }
    | none => .error s!"bad --min-ms {v}"
  | o :: _, _ => .error s!"unknown option {o}"

/-- The value of `k=` in a `RESULT` line. -/
def field (line k : String) : Option String :=
  (line.splitOn " ").findSome? fun kv =>
    if kv.startsWith (k ++ "=") then some (kv.drop (k.length + 1)).toString else none

/-- What `compare` keeps of one cell. -/
structure Result where
  /-- The minimum over repetitions of ns per operation. -/
  ns : Float
  checksum : String
  fin : String

/-- Run one cell of `map` in a child process. -/
def runCell (map key : String) (n : Nat) (wl : String) (o : Opts) : IO (Except String Result) := do
  let exe ← IO.appPath
  let out ← IO.Process.output
    { cmd := exe.toString,
      args := #[map, key, toString n, wl, "--reps", toString o.reps, "--min-ms", toString o.minMs] }
  if out.exitCode != 0 then
    return .error s!"{map} {key} {n} {wl}: exit {out.exitCode}: {out.stderr.trimAscii}"
  let some line := (out.stdout.splitOn "\n").find? (·.startsWith "RESULT ")
    | return .error s!"{map} {key} {n} {wl}: no RESULT line"
  let get (k : String) : Except String String :=
    match field line k with
    | some v => .ok v
    | none => .error s!"{map} {key} {n} {wl}: no {k}= in the RESULT line"
  return do
    let some ops := (← get "ops").toNat? | .error s!"{map} {key} {n} {wl}: bad ops"
    let some times := (csv (← get "times_ns")).mapM String.toNat?
      | .error s!"{map} {key} {n} {wl}: bad times_ns"
    let t := times.foldl min (times.headD 0)
    pure { ns := t.toFloat / (max ops 1).toFloat, checksum := ← get "checksum", fin := ← get "fin" }

/-- `x` with `d` decimals. -/
def fmt (x : Float) (d : Nat := 2) : String :=
  let r := (x * (10 ^ d).toFloat).round.toUInt64.toNat
  let f := toString (r % 10 ^ d)
  s!"{r / 10 ^ d}." ++ "".pushn '0' (d - f.length) ++ f

def padL (s : String) (w : Nat) : String := "".pushn ' ' (w - s.length) ++ s
def padR (s : String) (w : Nat) : String := s ++ "".pushn ' ' (w - s.length)

def geomean (xs : List Float) : Float :=
  if xs.isEmpty then 0 else Float.exp ((xs.map Float.log).foldl (· + ·) 0 / xs.length.toFloat)

def run (args : List String) : IO UInt32 := do
  let o ← match parse args {} with
    | .ok o => pure o
    | .error e => IO.eprintln e; return 2
  IO.println s!"SwissTable.HashMap vs Std.HashMap: min ns per op over at least {o.reps} \
    repetitions of at least {o.minMs} ms in all, one process per cell (rough timings)"
  IO.println (padR "key" 8 ++ padL "n" 9 ++ "  " ++ padR "workload" 14 ++ padL "std" 10 ++
    padL "swisstable" 10 ++ padL "swisstable/std" 11)
  let mut ratios : Array (String × Float) := #[]
  let mut mismatches : Array String := #[]
  let mut failures : Array String := #[]
  let mut cell := 0
  for key in o.keys do
    for n in o.sizes do
      for wl in o.workloads do
        let order := if cell % 2 == 0 then ["std", "swisstable"] else ["swisstable", "std"]
        cell := cell + 1
        let mut rs : List (String × Result) := []
        for map in order do
          match ← runCell map key n wl o with
          | .ok r => rs := (map, r) :: rs
          | .error e => failures := failures.push e
        match rs.lookup "std", rs.lookup "swisstable" with
        | some s, some m =>
          let q := m.ns / s.ns
          ratios := ratios.push (wl, q)
          if s.checksum != m.checksum || s.fin != m.fin then
            mismatches := mismatches.push s!"{key} {n} {wl}: std {s.checksum}/{s.fin}, \
              swisstable {m.checksum}/{m.fin}"
          IO.println (padR key 8 ++ padL (toString n) 9 ++ "  " ++ padR wl 14 ++
            padL (fmt s.ns 1) 10 ++ padL (fmt m.ns 1) 10 ++ padL (fmt q) 11)
        | _, _ => pure ()
  IO.println ""
  IO.println "geometric mean of swisstable/std"
  for wl in o.workloads do
    let qs := (ratios.filter (·.1 == wl)).toList.map (·.2)
    unless qs.isEmpty do
      IO.println (padR wl 14 ++ padL (fmt (geomean qs)) 8 ++ s!"  ({qs.length} cells)")
  IO.println (padR "all" 14 ++ padL (fmt (geomean (ratios.toList.map (·.2)))) 8 ++
    s!"  ({ratios.size} cells)")
  IO.println s!"checksum mismatches: {mismatches.size}"
  for m in mismatches do IO.println s!"  {m}"
  for f in failures do IO.eprintln s!"FAILED {f}"
  return if mismatches.isEmpty && failures.isEmpty then 0 else 1

end Bench.Compare

def usage : String :=
  "usage: swisstable-bench [compare [--keys K,..] [--sizes N,..] [--workloads W,..] [--reps R] \
   [--min-ms T]]\n       swisstable-bench <std|swisstable> <dense|rand|string|struct|flat> \
   <n> <workload> [--reps R] [--min-ms T] [--iters I]"

public def main (args : List String) : IO UInt32 :=
  match args with
  | "std" :: rest =>
    Bench.mainFor "std" (Std.HashMap Nat Nat) (Std.HashMap String Nat)
      (Std.HashMap Bench.SKey Nat) (Std.HashMap Bench.FKey Nat) rest
  | "swisstable" :: rest =>
    Bench.mainFor "swisstable" (SwissTable.HashMap Nat Nat) (SwissTable.HashMap String Nat)
      (SwissTable.HashMap Bench.SKey Nat) (SwissTable.HashMap Bench.FKey Nat) rest
  | "compare" :: rest => Bench.Compare.run rest
  | [] => Bench.Compare.run []
  | _ => do IO.eprintln usage; return 2
