#!/usr/bin/env bash
set -euo pipefail
mkdir -p logs
RUN_LOG=logs/build_audit.rerun.txt
STATIC_LOG=logs/static_audit.rerun.txt
rm -f "$RUN_LOG" "$STATIC_LOG"
{
  echo "== toolchain =="
  lean --version
  lake --version
  echo "artifact_version=0.7.2"
  echo "== lake build Mathdemo.CheckSec3PortAxioms =="
  lake build Mathdemo.CheckSec3PortAxioms
  echo "== lake build public DCT implementation support modules =="
  lake build Mathdemo.BishopSec3PresentedEnhancementsC
  lake build Mathdemo.BishopChengTheorem415Prop
  echo "== lake env lean -R . ChoiceFreeMeasureDCTPublic.lean -o .lake/build/lib/lean/ChoiceFreeMeasureDCTPublic.olean =="
  mkdir -p .lake/build/lib/lean
  lake env lean -R . ChoiceFreeMeasureDCTPublic.lean \
    -o .lake/build/lib/lean/ChoiceFreeMeasureDCTPublic.olean \
    -i .lake/build/lib/lean/ChoiceFreeMeasureDCTPublic.ilean
  echo "== lake build public DCT example modules =="
  lake build Mathdemo.ChoiceFreeDCTConcreteExamples
  echo "== lake env lean Mathdemo/CheckDCTV2Axioms.lean =="
  lake env lean Mathdemo/CheckDCTV2Axioms.lean
  echo "== lake env lean Mathdemo/CheckBishopChengTheorem415PropAxioms.lean =="
  lake env lean Mathdemo/CheckBishopChengTheorem415PropAxioms.lean
  echo "== lake env lean SupplementChoiceFreeMeasureDCT.lean =="
  lake env lean SupplementChoiceFreeMeasureDCT.lean
  echo "== lake env lean ChoiceFreeMeasureDCTPublic.lean =="
  lake env lean ChoiceFreeMeasureDCTPublic.lean
  echo "== lake build Mathdemo =="
  lake build Mathdemo 2>&1 | tee logs/mathdemo_build.rerun.txt
  echo "== reading-layer axiom report =="
  python3 tools/generate_reading_layer_axioms.py --output .lake/reading_layer_axioms_check.lean
  lake env lean .lake/reading_layer_axioms_check.lean > logs/reading_layer_axioms.rerun.txt
  python3 tools/check_reading_layer_axioms.py logs/reading_layer_axioms.rerun.txt
  echo "== public-surface invariant =="
  lake env lean -R . tools/public_surface_check.lean > logs/public_surface.rerun.txt 2>&1
  diff -u logs/public_surface.txt logs/public_surface.rerun.txt
  echo "PUBLIC SURFACE INVARIANT PRESERVED"
  echo "== frozen-name check =="
  ./tools/check_frozen_names.sh
  echo "== nested CoRN checksums =="
  ( cd audits/corn && sha256sum -c SHA256SUMS )
  echo "== vacuous statements (complete check) =="
  lake env lean --run tools/vacuous_statement_check.lean 2>&1 | tee logs/vacuous_statements.rerun.txt
  grep -q "VACUOUS STATEMENT CHECK PASSED" logs/vacuous_statements.rerun.txt

  echo "== release consistency =="
  if [ -f paper/paper.tex ]; then
    python3 tools/check_release_consistency.py paper/paper.tex
  elif [ -f ../paper/paper.tex ]; then
    python3 tools/check_release_consistency.py ../paper/paper.tex
  else
    python3 tools/check_release_consistency.py
  fi

  echo "== displayed definitions =="
  if [ -f paper/paper.tex ]; then
    python3 tools/check_displayed_definitions.py paper/paper.tex
  elif [ -f ../paper/paper.tex ]; then
    python3 tools/check_displayed_definitions.py ../paper/paper.tex
  else
    echo "DISPLAYED DEFINITION CHECK SKIPPED: no paper source in this deposit"
  fi

  # ★The static source-closure audit runs before the paper checks, not after.
  # It reads only the Lean tree and writes the static-audit reference log; the paper
  # checks read the *promoted* logs and so necessarily fail on the run that precedes
  # a promotion (a version bump makes the paper say 0.6.1 while the shipped log still
  # says 0.6.0).  With the order reversed, that expected failure aborted the run
  # before the static log was written, leaving the promotion incomplete.  Nothing in
  # the static audit depends on the paper, so it belongs earlier.
  echo "== python3 tools/static_no_choice_audit.py =="
  python3 tools/static_no_choice_audit.py | tee "$STATIC_LOG"
} 2>&1 | tee "$RUN_LOG"
for bad in Classical. sorryAx native_decide Quot.out; do
  if grep -Fq "$bad" "$RUN_LOG"; then
    echo "forbidden audit output token found: $bad" >&2
    exit 1
  fi
done
echo "BUILD_AUDIT_EXIT=0" | tee -a "$RUN_LOG"

# ★Runs after the success line, and outside the block that writes the run log.
# It compares the stages this script announces against the reference log in `logs/`,
# and the reference log is promoted from this run afterwards --- so if it ran inside
# the block it would abort before `BUILD_AUDIT_EXIT=0` was ever written, and the
# promoted log could never satisfy the very condition the check requires.  Its own
# verdict is appended to the run log so a reader can see that it ran.
python3 tools/check_log_generation.py 2>&1 | tee -a "$RUN_LOG"

# ★Runs here for the same reason check_log_generation.py does: it reads the *promoted*
# reference log `logs/build_audit.txt`, not this run's `.rerun.txt`.  Inside the block
# it aborted the run before `BUILD_AUDIT_EXIT=0` was written, so the log promoted from
# that run lacked the success line the next run then demanded --- and a release that
# bumps the version can never satisfy it, because the paper names the new version
# while the shipped log still names the old one.  Placing it after the success line
# lets the promotion happen and still fails the script when the paper disagrees.
echo "== paper/log consistency ==" | tee -a "$RUN_LOG"
# The software deposit excludes the paper source (.gitattributes), and a review
# bundle may place it beside the artifact.  Look in both places.  When the paper
# is genuinely absent this is reported as an explicit SKIP, never as a pass:
# the checker itself stays fail-closed whenever it is given a path.
if [ -f paper/paper.tex ]; then
  python3 tools/check_paper_against_logs.py paper/paper.tex 2>&1 | tee -a "$RUN_LOG"
elif [ -f ../paper/paper.tex ]; then
  python3 tools/check_paper_against_logs.py ../paper/paper.tex 2>&1 | tee -a "$RUN_LOG"
else
  echo "PAPER/LOG CONSISTENCY CHECK SKIPPED: no paper source in this deposit" | tee -a "$RUN_LOG"
fi
