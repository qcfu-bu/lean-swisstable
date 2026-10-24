#!/bin/sh
# Full check of the package (docs/ARCHITECTURE.md §9.3). Usage: tools/ci.sh
#
#   1. lake build OAMap   every proof, against the core selected by OAMap/Core/Table.lean
#   2. lake test          OAMapTest: CoreSpec, SealCheck, Audit, ParityRun, Cbv, Unverified
#   3. srccheck.py        source text of the 16 iterator declarations parity ignores (once written)
#   4. audit.py           text-level spec-integrity audit of OAMap/ (no sorry, axiom, unsafe, ...)
#
# Until the Merge phase, ParityRun and Audit report missing declarations and `sorry` without
# failing (their GATE lines); step 4 is always strict.
set -eu
cd "$(dirname "$0")/.."
echo "ci: core = $(tools/select-core.sh)"
lake build OAMap
lake test
if [ -f tools/srccheck.py ]; then
  python3 -I tools/srccheck.py tools/inventory.json OAMap
else
  echo "ci: tools/srccheck.py does not exist yet (Wave 1, PORT); skipped"
fi
python3 -I tools/audit.py OAMap OAMap.lean
echo "ci: ok"
