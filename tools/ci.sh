#!/bin/sh
# Full check of the package (docs/ARCHITECTURE.md §9.3). Usage: tools/ci.sh
#
#   1. lake build OAMap   every proof, against the core selected by OAMap/Core/Table.lean
#   2. lake test          OAMapTest: CoreSpec, SealCheck, Audit, ParityRun, Cbv, Unverified
#   3. srccheck.py        source text of the 16 iterator declarations parity ignores
#   4. audit.py           text-level spec-integrity audit of OAMap/ (no sorry, axiom, unsafe, ...)
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
echo "ci: ok"
