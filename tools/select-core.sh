#!/bin/sh
# Select the table core that SwissTable is built on (docs/ARCHITECTURE.md §2.2, §3.6, §9.3).
#
#   tools/select-core.sh                   print the current selection
#   tools/select-core.sh swiss             the Swiss core SwissTable.Core.Swiss (the selection)
#   tools/select-core.sh listref           the list-backed reference core SwissTable.Core.ListRef
#   tools/select-core.sh linear|dense      other bake-off cores, SwissTable.Core.Linear/Dense (not
#                                          in the repository)
#   tools/select-core.sh SwissTable.Core.<X>
#                                          any other core module
#
# It rewrites the one `public import SwissTable.Core.<X>` line of SwissTable/Core/Table.lean. A core
# is eligible when `lake build SwissTableTest.CoreSpec` succeeds after selecting it; `lake test`
# then also checks the seal (test/SwissTableTest/SealCheck.lean).
set -eu
cd "$(dirname "$0")/.."
sel=SwissTable/Core/Table.lean
if [ $# -eq 0 ]; then
  sed -n 's/^public import \(SwissTable\.Core\..*\)$/\1/p' "$sel"
  exit 0
fi
case "$1" in
  listref) mod=SwissTable.Core.ListRef ;;
  linear)  mod=SwissTable.Core.Linear ;;
  swiss)   mod=SwissTable.Core.Swiss ;;
  dense)   mod=SwissTable.Core.Dense ;;
  SwissTable.Core.*) mod=$1 ;;
  *) echo "usage: $0 [listref|linear|swiss|dense|SwissTable.Core.<X>]" >&2; exit 2 ;;
esac
case "$mod" in
  SwissTable.Core.Table|SwissTable.Core.Derived|SwissTable.Core.Bulk)
    echo "$mod is a layout-free module, not a core" >&2; exit 2 ;;
esac
file="$(echo "$mod" | tr . /).lean"
if [ ! -f "$file" ]; then
  echo "no core module $mod (expected the file $file)" >&2; exit 1
fi
n=$(grep -c '^public import SwissTable\.Core\.' "$sel" || true)
if [ "$n" != 1 ]; then
  echo "$sel must contain exactly one 'public import SwissTable.Core.<X>' line (found $n)" >&2
  exit 1
fi
tmp="$sel.tmp"
awk -v mod="$mod" \
  '/^public import SwissTable\.Core\./ { print "public import " mod; next } { print }' \
  "$sel" > "$tmp"
mv "$tmp" "$sel"
echo "SwissTable.Core.Table now selects $mod; check it with:" \
  "lake build SwissTableTest.CoreSpec && lake test"
