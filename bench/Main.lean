import OAMap

/-!
# OAMap versus Std: timings

Insert, lookup, erase, alter/modify, traversals, `ofList`, `union`/`inter` and HashSet operations
on `Nat` and `String` keys, small and large maps (`docs/ARCHITECTURE.md` §9.4). Not gating.

Stub (Wave 0). Owner: BENCH, Wave 3. Build with `lake build oamap-bench`.
-/

def main : IO Unit :=
  IO.println "oamap-bench: no benchmarks yet (Wave 3)"
