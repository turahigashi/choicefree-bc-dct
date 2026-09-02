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
  echo "artifact_version=0.6.0"
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
  lake build Mathdemo 2>&1 | tee logs/mathdemo_build.txt
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
  echo "== paper/log consistency =="
  python3 tools/check_paper_against_logs.py
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
