#!/bin/sh
# Full check of the package (docs/ARCHITECTURE.md §9.3). Usage: tools/ci.sh
#
#   1. lake build OAMap   every proof, against the core selected by OAMap/Core/Table.lean
#   2. lake test          OAMapTest: CoreSpec, SealCheck, Audit, ParityRun, Cbv, Unverified,
#                         Semantics
#   3. srccheck.py        source text of the 16 iterator declarations parity ignores
#   4. audit.py           text-level spec-integrity audit of OAMap/ (no sorry, axiom, unsafe, ...)
#   5. regenerate         port.py and gen_basic.py reproduce the generated files exactly (hand
#                         proofs live in tools/data/hand.json, never in the generated files)
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
echo "ci: ok"
