module

public import Bench.Iface

/-!
# Workload loops

Written once against `BenchMap M α Nat` and `@[specialize]`d, so that each executable compiles
them at its own map type. Maps are threaded linearly (unshared) throughout; a set of maps that a
pass consumes one by one is a `List`, whose cells are freed as the pass takes the maps out, so
each map is unshared when the pass reaches it.
-/

@[expose] public section

set_option cleanup.letToHave false

namespace Bench

section Loops

variable {M α : Type} [BenchMap M α Nat]

/-- Insert `ks[i] ↦ i + off` for every `i` from `i` on. -/
@[specialize] def insertFrom (ks : Array α) (off : Nat) (m : M) (i : Nat) : M :=
  if h : i < ks.size then insertFrom ks off (BenchMap.insert m ks[i] (i + off)) (i + 1) else m
termination_by ks.size - i

/-- Insert `ks[i] ↦ i` for `i` in `[i, stop)`. -/
@[specialize] def insertRange (ks : Array α) (m : M) (i stop : Nat) : M :=
  if h : i < stop then
    if h' : i < ks.size then insertRange ks (BenchMap.insert m ks[i] i) (i + 1) stop else m
  else m
termination_by stop - i

/-- Erase `qs[i]` for `i` in `[i, stop)`. -/
@[specialize] def eraseRange (qs : Array α) (m : M) (i stop : Nat) : M :=
  if h : i < stop then
    if h' : i < qs.size then eraseRange qs (BenchMap.erase m qs[i]) (i + 1) stop else m
  else m
termination_by stop - i

/-- The sum of `getD q fallback` over the queries from `i` on. -/
@[specialize] def sumGetD (m : M) (qs : Array α) (fallback : Nat) (i acc : Nat) : Nat :=
  if h : i < qs.size then sumGetD m qs fallback (i + 1) (acc + BenchMap.getD m qs[i] fallback)
  else acc
termination_by qs.size - i

/-- The sum of `v + 1` over the queries from `i` on that `get?` finds with value `v`. -/
@[specialize] def sumGetOpt (m : M) (qs : Array α) (i acc : Nat) : Nat :=
  if h : i < qs.size then
    match BenchMap.get? m qs[i] with
    | some v => sumGetOpt m qs (i + 1) (acc + v + 1)
    | none => sumGetOpt m qs (i + 1) acc
  else acc
termination_by qs.size - i

/-- Hash-consing: `getThenInsertIfNew? k (size)` over the stream positions `[i, stop)`; the sum of
the ids found. -/
@[specialize] def hashconsRange (ks : Array α) (m : M) (i stop acc : Nat) : M × Nat :=
  if h : i < stop then
    if h' : i < ks.size then
      let id := BenchMap.size m
      match BenchMap.getThenInsertIfNew? m ks[i] id with
      | (some v, m) => hashconsRange ks m (i + 1) stop (acc + v)
      | (none, m) => hashconsRange ks m (i + 1) stop acc
    else (m, acc)
  else (m, acc)
termination_by stop - i

/-- Churn rounds `t` in `[t, stop)`: insert the new key `ins[n + t] ↦ n + t`, then erase the
oldest key `outs[t]` (a copy of `ins[t]`). A map holding the keys `t .. t + n - 1` holds
`stop .. stop + n - 1` after. -/
@[specialize] def churnRange (ins outs : Array α) (n : Nat) (m : M) (t stop : Nat) : M :=
  if h : t < stop then
    if h1 : n + t < ins.size then
      if h2 : t < outs.size then
        churnRange ins outs n (BenchMap.erase (BenchMap.insert m ins[n + t] (n + t)) outs[t])
          (t + 1) stop
      else m
    else m
  else m
termination_by stop - t

/-- The fresh map of pass `j`: the keys `ks[j*n, (j+1)*n)`, from the empty map or one pre-sized
for `n`. -/
@[inline] def buildPass (ks : Array α) (n : Nat) (cap : Bool) (j : Nat) : M :=
  let m0 : M := if cap then BenchMap.emptyWithCapacity n else BenchMap.empty ()
  insertRange ks m0 (j * n) (j * n + n)

/-- `iters` fresh maps, map `j` (counting from `j`) built by `buildPass`. -/
@[specialize] def buildManyK (ks : Array α) (n : Nat) (cap : Bool) (j iters : Nat)
    (acc : Array M) : Array M :=
  match iters with
  | 0 => acc
  | k + 1 => buildManyK ks n cap (j + 1) k (acc.push (buildPass ks n cap j))

/-- The maps of passes `0 .. j - 1` (built by `buildPass` from the empty map), pass `0` first,
in front of `acc`. -/
@[specialize] def buildList (ks : Array α) (n j : Nat) (acc : List M) : List M :=
  match j with
  | 0 => acc
  | j + 1 => buildList ks n j (buildPass ks n false j :: acc)

/-- Pass `j` (counting from `j`) takes the next map and erases `qs[j*len, (j+1)*len)` from it;
the maps after, and the sum of their sizes. -/
@[specialize] def eraseMaps (qs : Array α) (len : Nat) (ms : List M) (j : Nat) (acc : List M)
    (cs : Nat) : List M × Nat :=
  match ms with
  | [] => (acc, cs)
  | m :: ms =>
    let m := eraseRange qs m (j * len) (j * len + len)
    eraseMaps qs len ms (j + 1) (m :: acc) (cs + BenchMap.size m)

/-- `iters` passes re-inserting every key of `ks`, pass `r` with the values `i + r`. -/
@[specialize] def reinsertPasses (ks : Array α) (m : M) (r iters : Nat) : M :=
  match iters with
  | 0 => m
  | k + 1 => reinsertPasses ks (insertFrom ks (r + 1) m 0) (r + 1) k

/-- `iters` fresh hash-consing passes, pass `j` (counting from `j`) over the stream positions
`[j*len, (j+1)*len)`. -/
@[specialize] def hashconsManyK (ks : Array α) (len j iters : Nat) (acc : Array M) (cs : Nat) :
    Array M × Nat :=
  match iters with
  | 0 => (acc, cs)
  | k + 1 =>
    let (m, c) := hashconsRange ks (BenchMap.empty ()) (j * len) (j * len + len) 0
    hashconsManyK ks len (j + 1) k (acc.push m) (cs + c)

/-- `f` applied `iters` times. -/
@[specialize] def repeatN (iters : Nat) (f : Nat → Nat) (acc : Nat) : Nat :=
  match iters with
  | 0 => acc
  | k + 1 => repeatN k f (f acc)

/-- The sum of the values, by `fold`. -/
@[inline] def sumVals (m : M) : Nat := BenchMap.fold (fun acc _ v => acc + v) 0 m

def totalSize (ms : Array M) : Nat := ms.foldl (fun a m => a + BenchMap.size m) 0

def totalVals (ms : Array M) : Nat := ms.foldl (fun a m => a + sumVals m) 0

def listSize (ms : List M) : Nat := ms.foldl (fun a m => a + BenchMap.size m) 0

def listVals (ms : List M) : Nat := ms.foldl (fun a m => a + sumVals m) 0

end Loops

end Bench
