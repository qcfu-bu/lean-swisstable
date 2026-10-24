#!/bin/sh
# Full check of the package (docs/ARCHITECTURE.md §9.3). Usage: tools/ci.sh
#
#   1. lake build OAMap   every proof, against the core selected by OAMap/Core/Table.lean
#   2. lake test          OAMapTest: CoreSpec, SealCheck, Audit, ParityRun, Cbv, Unverified,
#                         Semantics, SwissGroupUse, and CoreSpecListRef and AuditListRef (the
#                         reference core)
#   3. srccheck.py        source text of the 16 iterator declarations parity ignores
#   4. audit.py           text-level spec-integrity audit of OAMap/ (no sorry, axiom, unsafe, ...)
#   5. regenerate         port.py and gen_basic.py reproduce the generated files exactly (hand
#                         proofs live in tools/data/hand.json, never in the generated files)
#   6. CoreSpecListRef    below its header, the reference core's contract test is CoreSpec's text
#   7. oamap-bench        the benchmark compiles (it is not run: timings do not gate)
#   8. check_c.py         the generated C of the API at Nat and String keys calls no closure,
#                         allocates nothing in a lookup and updates its arrays in place
#
# Every step is strict: ParityRun fails on any difference from Std outside its ignore list, and
# Audit on any dependency on sorryAx.
set -eu
cd "$(dirname "$0")/.."
echo "ci: core = $(tools/select-core.sh)"
lake build OAMap
lake test
python3 -I tools/srccheck.py tools/inventory.json OAMap
python3 -I tools/audit.py OAMap OAMap.lean
python3 -I tools/port.py lemmas --check
std="$(lean --print-prefix)/src/lean/Std/Data"
tmp="$(mktemp -d)"
trap 'rm -rf "$tmp"' EXIT
python3 -I tools/gen_basic.py "$std" tools/inventory.json "$tmp"
for f in Basic AdditionalOperations; do
  diff -u "OAMap/HashMap/$f.lean" "$tmp/$f.lean" ||
    { echo "ci: OAMap/HashMap/$f.lean differs from tools/gen_basic.py's output"; exit 1; }
done
echo "ci: generated files reproduced"
body() { sed -n '/^open OAMap.Core Std.Internal.List$/,$p' "$1"; }
body test/OAMapTest/CoreSpec.lean > "$tmp/CoreSpec.body"
body test/OAMapTest/CoreSpecListRef.lean > "$tmp/CoreSpecListRef.body"
[ -s "$tmp/CoreSpec.body" ] && diff -u "$tmp/CoreSpec.body" "$tmp/CoreSpecListRef.body" ||
  { echo "ci: test/OAMapTest/CoreSpecListRef.lean is not CoreSpec.lean's contract text"; exit 1; }
echo "ci: CoreSpecListRef checks CoreSpec's contract text"
lake build oamap-bench Bench.CCheck
python3 -I tools/check_c.py
echo "ci: ok"
