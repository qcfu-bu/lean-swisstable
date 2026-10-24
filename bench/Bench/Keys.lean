module

/-!
# Keys and random streams

Everything here runs before a clock starts; none of it depends on the map. (From the bake-off
harness `oabench2`, without its instruction and cycle counters, which need a C helper.)
-/

@[expose] public section

set_option cleanup.letToHave false

namespace Bench

/-! ## Pseudo-random numbers -/

def xorshift (x : UInt64) : UInt64 :=
  let x := x ^^^ (x <<< 13)
  let x := x ^^^ (x >>> 7)
  x ^^^ (x <<< 17)

/-- The splitmix64 finaliser. -/
def mix64 (z : UInt64) : UInt64 :=
  let z := (z ^^^ (z >>> 30)) * 0xbf58476d1ce4e5b9
  let z := (z ^^^ (z >>> 27)) * 0x94d049bb133111eb
  z ^^^ (z >>> 31)

/-- The first `count` values of the xorshift stream from a fixed seed, cut to their top 62 bits. -/
def randStream (count : Nat) : Array Nat := Id.run do
  let mut x : UInt64 := 0x2545F4914F6CDD1D
  let mut out := Array.emptyWithCapacity count
  for _ in [0:count] do
    x := xorshift x
    out := out.push (x >>> 2).toNat
  return out

/-- A uniformly shuffled `0, …, n - 1` (Fisher–Yates from `seed`). -/
def permutation (n : Nat) (seed : UInt64 := 0x9E3779B97F4A7C15) : Array Nat := Id.run do
  let mut a := Array.range n
  let mut x := seed
  for i in [0:n] do
    let j := n - 1 - i
    if j > 0 then
      x := xorshift x
      a := a.swapIfInBounds j (x % (j + 1).toUInt64).toNat
  return a

/-- The seed of permutation `j` of a cell (`salt` keeps the erase sequences of a cell apart from
its lookup permutations). -/
def permSeed (j : Nat) (salt : UInt64 := 0) : UInt64 :=
  0x9E3779B97F4A7C15 + 2 * j.toUInt64 + 2 + salt

/-- `k` permutations of `0, …, n - 1`, each from its own seed, concatenated. (Pushed element by
element: the compiled `Array.append` recurses once per element through `lean_apply` and
overflows the stack at about 7 million elements.) -/
def manyPerms (n k : Nat) : Array Nat := Id.run do
  let mut out := Array.emptyWithCapacity (n * k)
  for j in [0:k] do
    let p := permutation n (permSeed j)
    for i in [0:p.size] do
      out := out.push p[i]!
  return out

/-! ## The structured keys -/

/-- A key standing in for Wnetkat2's `Node`: eight 64-bit fields in an `Array UInt64` (each field
boxed), hashed and compared field by field on every use. -/
structure SKey where
  f : Array UInt64
  deriving Inhabited

def SKey.beqFrom (a b : Array UInt64) (i : Nat) : Bool :=
  if h : i < a.size then
    if h' : i < b.size then a[i] == b[i] && SKey.beqFrom a b (i + 1) else false
  else true
termination_by a.size - i

instance : BEq SKey where
  beq a b := a.f.size == b.f.size && SKey.beqFrom a.f b.f 0

instance : Hashable SKey where
  hash k := k.f.foldl (fun h x => mixHash h (hash x)) 11

/-- The `i`-th structured key: field 0 is `i`, the others are mixed from it. -/
def SKey.make (i : Nat) : SKey :=
  let u := i.toUInt64
  ⟨#[u, mix64 (8 * u + 1), mix64 (8 * u + 2), mix64 (8 * u + 3), mix64 (8 * u + 4),
    mix64 (8 * u + 5), mix64 (8 * u + 6), mix64 (8 * u + 7)]⟩

/-- The same eight fields as one flat object (the fields are stored unboxed), with the derived
hash and equality. -/
structure FKey where
  a : UInt64
  b : UInt64
  c : UInt64
  d : UInt64
  e : UInt64
  f : UInt64
  g : UInt64
  h : UInt64
  deriving BEq, Hashable, Inhabited

def FKey.make (i : Nat) : FKey :=
  let u := i.toUInt64
  ⟨u, mix64 (8 * u + 1), mix64 (8 * u + 2), mix64 (8 * u + 3), mix64 (8 * u + 4),
    mix64 (8 * u + 5), mix64 (8 * u + 6), mix64 (8 * u + 7)⟩

/-! ## Key arrays -/

/-- `mk off, …, mk (off + count - 1)`. -/
def gen {α : Type} (count off : Nat) (mk : Nat → α) : Array α := Id.run do
  let mut out := Array.emptyWithCapacity count
  for i in [0:count] do
    out := out.push (mk (off + i))
  return out

/-- `out` followed by `pool[idx[j]]!` for `j` from `j` on: `idx.map (pool[·]!)`, written as tail
recursion. At a generic `α` neither `Array.map` nor a `for` loop gets specialised here, and their
unspecialised `Id` loops recurse once per element through `lean_apply`, which overflows the stack
at about 7 million elements. -/
def pick {α : Type} [Inhabited α] (pool : Array α) (idx : Array Nat) (j : Nat) (out : Array α) :
    Array α :=
  if h : j < idx.size then pick pool idx (j + 1) (out.push pool[idx[j]]!) else out
termination_by idx.size - j

/-- `k` hash-consing streams of `2n` keys, fresh copies throughout. In stream `j`, position `2i` is
key `j*n + i` (new) and position `2i + 1` is key `j*n + r` for a uniformly random `r ≤ i` (a
repeat). -/
def hashconsStreamK {α : Type} (n k : Nat) (mk : Nat → α) : Array α := Id.run do
  let mut out := Array.emptyWithCapacity (2 * n * k)
  let mut x : UInt64 := 0xD1B54A32D192ED03
  for j in [0:k] do
    for i in [0:n] do
      out := out.push (mk (j * n + i))
      x := xorshift x
      out := out.push (mk (j * n + (x % (i + 1).toUInt64).toNat))
  return out

/-- `k` erase sequences, fresh copies: sequence `j` is the keys `j*n + stride*p` for `p` in a
permutation of `0, …, ⌈n / stride⌉ - 1` (stride 1: every key of pass `j` in random order;
stride 2: every other key, in random order). -/
def eraseSeqK {α : Type} (n k stride : Nat) (mk : Nat → α) : Array α := Id.run do
  let len := (n + stride - 1) / stride
  let mut out := Array.emptyWithCapacity (len * k)
  for j in [0:k] do
    let p := permutation len (permSeed j 0x5555)
    for i in [0:p.size] do
      out := out.push (mk (j * n + stride * p[i]!))
  return out

end Bench
