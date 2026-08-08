#!/usr/bin/env bash
set -euo pipefail

CORN_COMMIT="ada7c0b497ff15dd67cf7932c6f20e143a2aee2f"
IMAGE="rocq/rocq-prover@sha256:787ea5569c9bf40e03a2255224365cb2fb0ae4a446fc60565dd61b1656d1699d"
SCRIPT_DIR="$(cd "$(dirname "${BASH_SOURCE[0]}")" && pwd)"

if [[ $# -ge 1 ]]; then
  WORK_DIR="$1"
  mkdir -p "$WORK_DIR"
else
  WORK_DIR="$(mktemp -d "${TMPDIR:-/tmp}/choicefree-bc-dct-corn-audit.XXXXXX")"
fi

LOG_FILE="${2:-$WORK_DIR/corn-print-assumptions.rerun.log}"

cd "$WORK_DIR"

git clone https://github.com/rocq-community/corn.git corn
cd corn
git checkout "$CORN_COMMIT"
cp "$SCRIPT_DIR/CoRNAxiomAudit.v" ./CoRNAxiomAudit.v

docker run --rm \
  -v "$PWD:/home/rocq/corn" \
  -w /home/rocq/corn \
  "$IMAGE" \
  sh -lc 'opam install -y --deps-only . && ./configure.sh && make -j2 reals/stdlib/CMTMeasurableFunctions.vo && coqc -R . CoRN CoRNAxiomAudit.v' \
  2>&1 | tee "$LOG_FILE"

echo "WORK_DIR=$WORK_DIR"
echo "LOG_FILE=$LOG_FILE"
echo "The work directory is retained for inspection."
