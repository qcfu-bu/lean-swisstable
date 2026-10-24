#!/bin/sh
# Select the table core that OAMap is built on (docs/ARCHITECTURE.md §2.2, §3.6, §9.3).
#
#   tools/select-core.sh                   print the current selection
#   tools/select-core.sh listref           the list-backed reference core OAMap.Core.ListRef
#   tools/select-core.sh linear|swiss|dense    a bake-off core OAMap.Core.Linear/Swiss/Dense
#   tools/select-core.sh OAMap.Core.<X>    any other core module
#
# It rewrites the one `public import OAMap.Core.<X>` line of OAMap/Core/Table.lean. A core is
# eligible when `lake build OAMapTest.CoreSpec` succeeds after selecting it; `lake test` then
# also checks the seal (test/OAMapTest/SealCheck.lean).
set -eu
cd "$(dirname "$0")/.."
sel=OAMap/Core/Table.lean
if [ $# -eq 0 ]; then
  sed -n 's/^public import \(OAMap\.Core\..*\)$/\1/p' "$sel"
  exit 0
fi
case "$1" in
  listref) mod=OAMap.Core.ListRef ;;
  linear)  mod=OAMap.Core.Linear ;;
  swiss)   mod=OAMap.Core.Swiss ;;
  dense)   mod=OAMap.Core.Dense ;;
  OAMap.Core.*) mod=$1 ;;
  *) echo "usage: $0 [listref|linear|swiss|dense|OAMap.Core.<X>]" >&2; exit 2 ;;
esac
case "$mod" in
  OAMap.Core.Table|OAMap.Core.Derived|OAMap.Core.Bulk)
    echo "$mod is a layout-free module, not a core" >&2; exit 2 ;;
esac
file="$(echo "$mod" | tr . /).lean"
if [ ! -f "$file" ]; then
  echo "no core module $mod (expected the file $file)" >&2; exit 1
fi
n=$(grep -c '^public import OAMap\.Core\.' "$sel" || true)
if [ "$n" != 1 ]; then
  echo "$sel must contain exactly one 'public import OAMap.Core.<X>' line (found $n)" >&2; exit 1
fi
tmp="$sel.tmp"
awk -v mod="$mod" '/^public import OAMap\.Core\./ { print "public import " mod; next } { print }' \
  "$sel" > "$tmp"
mv "$tmp" "$sel"
echo "OAMap.Core.Table now selects $mod; check it with: lake build OAMapTest.CoreSpec && lake test"
