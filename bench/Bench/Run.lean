module

public import Bench.Keys
public import Bench.Loops

/-!
# Cells, timing and the command line

One process run measures one cell (map, key type, n, workload):

    swisstable-bench <std|swisstable> <dense|rand|string|struct|flat> <n> <workload>
      [--reps R] [--min-ms T] [--iters I]

All keys are built before the clock starts. A repetition runs `iters` passes of the workload
between two `IO.monoNanosNow` calls. Its checksum is written to an `IO.Ref` before the second
call, so the work cannot float past the clock. A second checksum of the result (`fin`) is
computed after the clock stops, and the maps built in a repetition are dropped after it too
(except in `free`, which times exactly that drop).

No two passes of a repetition replay the same sequence where the workload allows it: shuffled
lookups, misses and erase sequences use a fresh permutation per pass, and insert, insert-cap,
free, hashcons, erase-alt and erase-all use a fresh key set per pass (pass `j` has the keys
`j*n .. j*n+n-1`). In-order lookups, reinsert and fold repeat the same pass by definition.

The output is one line `RESULT key=value ...`: the minimum and the median ns per operation, the
checksums and the time of every repetition. (This is the bake-off harness `oabench2`'s
`Harness/Run.lean` without its instruction and cycle counters.)
-/

@[expose] public section

set_option cleanup.letToHave false

namespace Bench

/-! ## Timing -/

structure Timing where
  /-- ns of each repetition. -/
  times : Array Nat := #[]
  /-- The sum of `times`. -/
  total : Nat := 0
  /-- The checksum of the last repetition, taken before the clock stopped. -/
  cs : Nat := 0
  /-- The checksum of the result of the last repetition, taken after the clock stopped. -/
  fin : Nat := 0

/-- How many repetitions to run: at least `reps`, and more until the timed total reaches `minNs`,
at most `maxReps`. -/
structure Budget where
  reps : Nat
  minNs : Nat
  maxReps : Nat

def Budget.done (b : Budget) (t : Timing) : Bool :=
  t.times.size ≥ b.maxReps || (t.times.size ≥ b.reps && t.total ≥ b.minNs)

def Timing.push (t : Timing) (dt cs fin : Nat) : Timing :=
  { times := t.times.push dt, total := t.total + dt, cs, fin }

/-- Each repetition times `work ()`, which builds its result from scratch. -/
@[specialize] def timeFresh {τ : Type} (sink : IO.Ref Nat) (b : Budget) (fuel : Nat)
    (work : Unit → τ × Nat) (fin : τ → Nat) (t : Timing) : IO Timing :=
  match fuel with
  | 0 => pure t
  | k + 1 => do
    if b.done t then return t
    let t0 ← IO.monoNanosNow
    let (out, cs) := work ()
    sink.set cs
    let t1 ← IO.monoNanosNow
    let f := fin out
    timeFresh sink b k work fin (t.push (t1 - t0) cs f)

/-- Each repetition times `work` on the state the last one left, threaded linearly. -/
@[specialize] def timeThread {σ : Type} (sink : IO.Ref Nat) (b : Budget) (fuel : Nat)
    (work : σ → σ × Nat) (fin : σ → Nat) (s : σ) (t : Timing) : IO Timing :=
  match fuel with
  | 0 => pure t
  | k + 1 => do
    if b.done t then return t
    let t0 ← IO.monoNanosNow
    let (s, cs) := work s
    sink.set cs
    let t1 ← IO.monoNanosNow
    let f := fin s
    timeThread sink b k work fin s (t.push (t1 - t0) cs f)

/-- Each repetition builds its input with `build ()` before the clock starts (its checksum goes to
the sink first, so the build cannot float into the timed region) and times `work` consuming it;
`fin` and the drop of the result come after the clock stops. -/
@[specialize] def timeBuilt {σ τ : Type} (sink : IO.Ref Nat) (b : Budget) (fuel : Nat)
    (build : Unit → σ × Nat) (work : σ → τ × Nat) (fin : τ → Nat) (t : Timing) : IO Timing :=
  match fuel with
  | 0 => pure t
  | k + 1 => do
    if b.done t then return t
    let (s, c) := build ()
    sink.set c
    let t0 ← IO.monoNanosNow
    let (out, cs) := work s
    sink.set cs
    let t1 ← IO.monoNanosNow
    let f := fin out
    timeBuilt sink b k build work fin (t.push (t1 - t0) cs f)

/-- Each repetition builds with `build ()` before the clock starts and times dropping the result:
the result is moved into a reference before the clock starts, and the timed `set` swaps it out,
so its last reference goes inside the timed region. -/
@[specialize] def timeFree {σ : Type} (sink : IO.Ref Nat) (b : Budget) (fuel : Nat)
    (build : Unit → Array σ × Nat) (t : Timing) : IO Timing :=
  match fuel with
  | 0 => pure t
  | k + 1 => do
    if b.done t then return t
    let (x, cs) := build ()
    sink.set cs
    let r ← IO.mkRef x
    let t0 ← IO.monoNanosNow
    r.set #[]
    let t1 ← IO.monoNanosNow
    timeFree sink b k build (t.push (t1 - t0) cs cs)

/-! ## Cells -/

inductive Workload
  | insert | insertCap | getD | getOpt | getDShuf | getOptShuf | miss | reinsert | hashcons
  | fold | free | eraseAlt | eraseAltGet | churn | churnGet | eraseAll | mem | memCap | base
  deriving BEq

def Workload.table : List (String × Workload) :=
  [("insert", .insert), ("insert-cap", .insertCap), ("getd", .getD), ("getopt", .getOpt),
   ("getd-shuf", .getDShuf), ("getopt-shuf", .getOptShuf), ("miss", .miss),
   ("reinsert", .reinsert), ("hashcons", .hashcons), ("fold", .fold), ("free", .free),
   ("erase-alt", .eraseAlt), ("erase-alt-get", .eraseAltGet), ("churn", .churn),
   ("churn-get", .churnGet), ("erase-all", .eraseAll), ("mem", .mem), ("mem-cap", .memCap),
   ("base", .base)]

def Workload.ofString? (s : String) : Option Workload := (Workload.table.lookup s)

/-- Map operations per pass. -/
def Workload.opsPerPass (w : Workload) (n : Nat) : Nat :=
  match w with
  | .hashcons | .churn | .churnGet => 2 * n
  | .eraseAlt => (n + 1) / 2
  | _ => n

structure Cell where
  map : String
  key : String
  wname : String
  work : Workload
  n : Nat
  reps : Nat
  minMs : Nat
  iters : Nat

/-- The keys of a cell. `ins` are inserted (key `i` with value `i`); every other array holds fresh
copies (`mk` is called again), so a heap key is never found by pointer equality. -/
structure Inputs (α : Type) where
  ins : Array α := #[]
  qry : Array α := #[]
  shuf : Array α := #[]
  absent : Array α := #[]
  stream : Array α := #[]
  /-- The keys to erase, in order. -/
  ers : Array α := #[]

/-- The inputs of a cell. Shuffled lookups and misses get one permutation per pass, mapped into
one pool of query copies (so a heap key costs one pointer per query); the building workloads get
`n * iters` keys, `n` per pass.

* `erase-alt`: pass `j` builds the keys `j*n ..` and erases the even ones in random order.
* `erase-alt-get`: the keys `0 .. n-1` with the even ones erased; shuffled `getD` (fallback 1) of
  all `n` keys, a fresh permutation per pass.
* `churn`: the keys `0 .. n-1`, then `iters * n` rounds of insert key `n + t`, erase key `t`.
* `churn-get`: the map after `churn`; shuffled `getD` (fallback 1) of its `n` live keys and the `n`
  keys erased last, a fresh permutation of the `2n` per pass.
* `erase-all`: pass `j` builds the keys `j*n ..` and erases all of them in random order. -/
def genInputs {α : Type} [Inhabited α] (c : Cell) (mk : Nat → α) : Inputs α :=
  let n := c.n
  let k := c.iters
  match c.work with
  | .hashcons => { stream := hashconsStreamK n k mk }
  | .insert | .insertCap | .free => { ins := gen (n * k) 0 mk }
  | .getD | .getOpt | .reinsert => { ins := gen n 0 mk, qry := gen n 0 mk }
  | .getDShuf | .getOptShuf =>
    let q := gen n 0 mk
    { ins := gen n 0 mk, shuf := pick q (manyPerms n k) 0 (.emptyWithCapacity (n * k)) }
  | .miss =>
    let a := gen n n mk
    { ins := gen n 0 mk, absent := pick a (manyPerms n k) 0 (.emptyWithCapacity (n * k)) }
  | .eraseAlt => { ins := gen (n * k) 0 mk, ers := eraseSeqK n k 2 mk }
  | .eraseAll => { ins := gen (n * k) 0 mk, ers := eraseSeqK n k 1 mk }
  | .eraseAltGet =>
    let q := gen n 0 mk
    { ins := gen n 0 mk, ers := eraseSeqK n 1 2 mk,
      shuf := pick q (manyPerms n k) 0 (.emptyWithCapacity (n * k)) }
  | .churn => { ins := gen (n * (k + 1)) 0 mk, ers := gen (n * k) 0 mk }
  | .churnGet =>
    let ers := gen (n * k) 0 mk
    -- the pool: copies of the keys erased last (`ers` holds them, no longer in the map) and
    -- fresh copies of the live keys
    let pool := (ers.extract (n * (k - 1)) (n * k)) ++ gen n (n * k) mk
    { ins := gen (n * (k + 1)) 0 mk, ers,
      shuf := pick pool (manyPerms (2 * n) k) 0 (.emptyWithCapacity (2 * n * k)) }
  | _ => { ins := gen n 0 mk }

def median (xs : Array Nat) : Nat :=
  let s := xs.qsort (· < ·)
  s[s.size / 2]!

def ratio (a b : Nat) : Float := Float.ofNat a / Float.ofNat b

/-- The index of the fastest repetition. -/
def argmin (xs : Array Nat) : Nat := Id.run do
  let mut best := 0
  for i in [0:xs.size] do
    if xs[i]! < xs[best]! then best := i
  return best

def report (c : Cell) (t : Timing) (extra : String) : IO Unit := do
  let ops := c.iters * c.work.opsPerPass c.n
  let i := argmin t.times
  let sum (xs : Array Nat) := xs.foldl (· + ·) 0
  let line :=
    s!"RESULT map={c.map} key={c.key} n={c.n} workload={c.wname} reps={t.times.size} iters={c.iters} " ++
    s!"ops={ops} min_ns_op={ratio t.times[i]! ops} median_ns_op={ratio (median t.times) ops} " ++
    s!"total_ns={sum t.times} checksum={t.cs} fin={t.fin} " ++
    s!"times_ns={",".intercalate (t.times.toList.map toString)}{extra}"
  IO.println line

/-- Run one cell at map type `M`. -/
@[specialize] def runCell (M : Type) {α : Type} [BenchMap M α Nat] (sink : IO.Ref Nat) (c : Cell)
    (inp : Inputs α) : IO Unit := do
  let b : Budget := { reps := c.reps, minNs := c.minMs * 1000000, maxReps := 100000 }
  let iters := c.iters
  let n := c.n
  match c.work with
  | .insert | .insertCap =>
    let cap := c.work == .insertCap
    let t ← timeFresh sink b b.maxReps
      (fun _ => let ms : Array M := buildManyK inp.ins n cap 0 iters #[]; (ms, totalSize ms))
      totalVals {}
    report c t ""
  | .getD =>
    let m : M := insertFrom inp.ins 0 (BenchMap.empty ()) 0
    let t ← timeThread sink b b.maxReps
      (fun m => let x := repeatN iters (fun acc => sumGetD m inp.qry 0 0 acc) 0; (m, x))
      BenchMap.size m {}
    report c t ""
  | .getOpt =>
    let m : M := insertFrom inp.ins 0 (BenchMap.empty ()) 0
    let t ← timeThread sink b b.maxReps
      (fun m => let x := repeatN iters (fun acc => sumGetOpt m inp.qry 0 acc) 0; (m, x))
      BenchMap.size m {}
    report c t ""
  | .getDShuf =>
    let m : M := insertFrom inp.ins 0 (BenchMap.empty ()) 0
    let t ← timeThread sink b b.maxReps
      (fun m => let x := sumGetD m inp.shuf 0 0 0; (m, x))
      BenchMap.size m {}
    report c t ""
  | .getOptShuf =>
    let m : M := insertFrom inp.ins 0 (BenchMap.empty ()) 0
    let t ← timeThread sink b b.maxReps
      (fun m => let x := sumGetOpt m inp.shuf 0 0; (m, x))
      BenchMap.size m {}
    report c t ""
  | .miss =>
    let m : M := insertFrom inp.ins 0 (BenchMap.empty ()) 0
    let t ← timeThread sink b b.maxReps
      (fun m => let x := sumGetD m inp.absent 1 0 0; (m, x))
      BenchMap.size m {}
    report c t ""
  | .reinsert =>
    let m : M := insertFrom inp.ins 0 (BenchMap.empty ()) 0
    let t ← timeThread sink b b.maxReps
      (fun m => let m := reinsertPasses inp.qry m 0 iters; (m, BenchMap.size m))
      sumVals m {}
    report c t ""
  | .hashcons =>
    let t ← timeFresh sink b b.maxReps
      (fun _ =>
        let (ms, cs) := hashconsManyK (M := M) inp.stream (2 * n) 0 iters #[] 0
        (ms, cs + totalSize ms))
      totalVals {}
    report c t ""
  | .fold =>
    let m : M := insertFrom inp.ins 0 (BenchMap.empty ()) 0
    let t ← timeThread sink b b.maxReps
      (fun m => let x := repeatN iters (fun acc => acc + sumVals m) 0; (m, x))
      BenchMap.size m {}
    report c t ""
  | .free =>
    let t ← timeFree sink b b.maxReps
      (fun _ => let ms : Array M := buildManyK inp.ins n false 0 iters #[]; (ms, totalSize ms))
      {}
    report c t ""
  | .eraseAlt | .eraseAll =>
    let len := c.work.opsPerPass n
    let t ← timeBuilt sink b b.maxReps
      (fun _ => let ms : List M := buildList inp.ins n iters []; (ms, listSize ms))
      (fun ms => eraseMaps inp.ers len ms 0 [] 0)
      listVals {}
    report c t ""
  | .eraseAltGet =>
    let m : M := insertFrom inp.ins 0 (BenchMap.empty ()) 0
    let m := eraseRange inp.ers m 0 inp.ers.size
    let t ← timeThread sink b b.maxReps
      (fun m => let x := sumGetD m inp.shuf 1 0 0; (m, x))
      BenchMap.size m {}
    report c t ""
  | .churn =>
    let t ← timeBuilt sink b b.maxReps
      (fun _ => let m : M := insertRange inp.ins (BenchMap.empty ()) 0 n; (m, BenchMap.size m))
      (fun m => let m := churnRange inp.ins inp.ers n m 0 (n * iters); (m, BenchMap.size m))
      sumVals {}
    report c t ""
  | .churnGet =>
    let m : M := insertRange inp.ins (BenchMap.empty ()) 0 n
    let m := churnRange inp.ins inp.ers n m 0 (n * iters)
    let t ← timeThread sink b b.maxReps
      (fun m => let x := sumGetD m inp.shuf 1 0 0; (m, x))
      BenchMap.size m {}
    report c t ""
  | .mem | .memCap =>
    let m0 : M := if c.work == .memCap then BenchMap.emptyWithCapacity n else BenchMap.empty ()
    let m : M := insertFrom inp.ins 0 m0 0
    sink.set (BenchMap.size m)
    IO.println s!"RESULT map={c.map} key={c.key} n={n} workload={c.wname} \
      size={BenchMap.size m} checksum={sumVals m}"
  | .base =>
    sink.set inp.ins.size
    IO.println s!"RESULT map={c.map} key={c.key} n={n} workload={c.wname} \
      size={inp.ins.size} checksum={inp.ins.size}"

/-- Run one cell at map type `M` and key type `α`. -/
@[specialize] def runKey (M : Type) {α : Type} [BenchMap M α Nat] [Inhabited α]
    (sink : IO.Ref Nat) (c : Cell) (mk : Nat → α) : IO Unit :=
  runCell M sink c (genInputs c mk)

def usage (map : String) : String :=
  s!"usage: swisstable-bench {map} <dense|rand|string|struct|flat> <n> <workload> [--reps R] \
   [--min-ms T] [--iters I]\nworkloads: {" ".intercalate (Workload.table.map (·.1))}"

structure Opts where
  reps : Nat := 5
  minMs : Nat := 300
  iters : Option Nat := none

def parseOpts : List String → Opts → Except String Opts
  | [], o => .ok o
  | "--reps" :: v :: rest, o =>
    match v.toNat? with
    | some r => parseOpts rest { o with reps := r }
    | none => .error s!"bad --reps {v}"
  | "--min-ms" :: v :: rest, o =>
    match v.toNat? with
    | some r => parseOpts rest { o with minMs := r }
    | none => .error s!"bad --min-ms {v}"
  | "--iters" :: v :: rest, o =>
    match v.toNat? with
    | some i => parseOpts rest { o with iters := some i }
    | none => .error s!"bad --iters {v}"
  | o :: _, _ => .error s!"unknown option {o}"

/-- One cell of the map `map`, given its map types at the four key types (`dense` and `rand` are
both `Nat`): `M Nat Nat`, `M String Nat`, `M SKey Nat`, `M FKey Nat`. -/
@[specialize] def mainFor (map : String) (MN MS MK MF : Type) [BenchMap MN Nat Nat]
    [BenchMap MS String Nat] [BenchMap MK SKey Nat] [BenchMap MF FKey Nat] (args : List String) :
    IO UInt32 := do
  match args with
  | key :: nStr :: wname :: rest =>
    let some n := nStr.toNat? | IO.eprintln (usage map); return 2
    let some work := Workload.ofString? wname | IO.eprintln (usage map); return 2
    let o ← match parseOpts rest {} with
      | .ok o => pure o
      | .error e => IO.eprintln e; IO.eprintln (usage map); return 2
    let iters := match work with
      | .mem | .memCap | .base => 1
      | _ => o.iters.getD (max 1 (1000000 / max 1 n))
    let c : Cell := { map, key, wname, work, n, reps := max 1 o.reps, minMs := o.minMs, iters }
    let sink ← IO.mkRef 0
    match key with
    | "dense" => runKey MN sink c (fun i => i)
    | "rand" =>
      let raws := randStream (2 * n * iters)
      runKey MN sink c (fun i => raws[i]!)
      -- Keep the raw stream alive to the end: freed after key generation, its memory would be
      -- reused by the map, hiding part of the map from the `mem` cells (`base` holds it too).
      sink.modify (· + raws.size)
    | "string" => runKey MS sink c (fun i => "key-" ++ toString i)
    | "struct" => runKey MK sink c SKey.make
    | "flat" => runKey MF sink c FKey.make
    | _ => IO.eprintln (usage map); return 2
    let s ← sink.get
    if s == 0xFFFFFFFFFFFFFFFFFF then IO.println "unreachable"
    return 0
  | _ => IO.eprintln (usage map); return 2

end Bench
