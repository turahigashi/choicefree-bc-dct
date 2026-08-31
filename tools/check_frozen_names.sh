#!/usr/bin/env bash
# Every identifier the paper cites by name must still exist in the tree.
#   ./tools/check_frozen_names.sh
set -u
cd "$(dirname "$0")/.."
missing=0
while IFS= read -r n; do
  case "$n" in ''|'#'*) continue;; esac
  short="${n##*.}"
  if ! grep -rqw -- "$short" --include='*.lean' Mathdemo *.lean 2>/dev/null; then
    echo "MISSING: $n"; missing=$((missing+1))
  fi
done < tools/frozen_names.txt
total=$(grep -vc '^#\|^$' tools/frozen_names.txt)
echo "frozen_names: $total"
echo "missing: $missing"
if [ "$missing" -gt 0 ]; then echo "FROZEN NAME CHECK FAILED"; exit 1; fi
echo "FROZEN NAME CHECK PASSED"
