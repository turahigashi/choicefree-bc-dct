#!/usr/bin/env bash
# Every name the paper cites must still exist, and must exist as the kind of
# thing the paper cites it as.  tools/frozen_names.txt records that kind:
#
#   decl     elaborated by Lean (`#check @<name>`), the strongest check here
#   module   the module's source file must exist
#   ns       a `namespace <name>` declaration must appear in the sources
#   dir      the source directory must exist
#   corn     a CoRN file: named in audits/corn, or cited in the paper by an
#            href carrying the pinned CoRN commit
#   version  must match lean-toolchain
#
# Usage: ./tools/check_frozen_names.sh
set -uo pipefail
cd "$(dirname "$0")/.."
LIST=tools/frozen_names.txt
GEN=.lake/frozen_names_check.lean
fail=0

decl_n=$(awk '$1=="decl"' "$LIST" | wc -l)
python3 tools/generate_frozen_names_check.py --names "$LIST" --output "$GEN" >/dev/null
if lake env lean -R . "$GEN" > .lake/frozen_names_check.out 2>&1; then
  echo "decl: $decl_n checked by Lean elaboration"
else
  echo "DECL CHECK FAILED; see .lake/frozen_names_check.out"
  grep -E ": error" .lake/frozen_names_check.out | head -20
  fail=1
fi

mod_n=0
while read -r _ n; do
  mod_n=$((mod_n+1))
  f="${n//.//}.lean"
  [ -f "$f" ] || { echo "MISSING module: $n ($f)"; fail=1; }
done < <(awk '$1=="module"' "$LIST")
echo "module: $mod_n source files present"

ns_n=0
while read -r _ n; do
  ns_n=$((ns_n+1))
  grep -rqE "^namespace +$n\b" --include='*.lean' Mathdemo ./*.lean 2>/dev/null \
    || { echo "MISSING namespace: $n"; fail=1; }
done < <(awk '$1=="ns"' "$LIST")
echo "ns: $ns_n namespaces declared"

dir_n=0
while read -r _ n; do
  dir_n=$((dir_n+1))
  [ -d "$n" ] || { echo "MISSING directory: $n"; fail=1; }
done < <(awk '$1=="dir"' "$LIST")
echo "dir: $dir_n source directories present"

CORN_PIN=$(grep -o 'corn/blob/[0-9a-f]\{40\}' paper/paper.tex 2>/dev/null | head -1 | cut -d/ -f3)
corn_n=0
while read -r _ n; do
  corn_n=$((corn_n+1))
  if grep -rqF -- "$n" audits/corn 2>/dev/null; then continue; fi
  if [ -n "$CORN_PIN" ] && grep -qF -- "$CORN_PIN/reals/stdlib/$n" paper/paper.tex 2>/dev/null; then continue; fi
  echo "MISSING CoRN file: $n (not in audits/corn and not pinned in the paper)"; fail=1
done < <(awk '$1=="corn"' "$LIST")
echo "corn: $corn_n CoRN files accounted for (pin ${CORN_PIN:0:12})"

ver_n=0
while read -r _ n; do
  ver_n=$((ver_n+1))
  grep -qF -- "$n" lean-toolchain || { echo "MISSING version: $n"; fail=1; }
done < <(awk '$1=="version"' "$LIST")
echo "version: $ver_n matched against lean-toolchain"

echo "frozen_names: $((decl_n+mod_n+ns_n+dir_n+corn_n+ver_n))"
if [ "$fail" -ne 0 ]; then echo "FROZEN NAME CHECK FAILED"; exit 1; fi
echo "FROZEN NAME CHECK PASSED"
