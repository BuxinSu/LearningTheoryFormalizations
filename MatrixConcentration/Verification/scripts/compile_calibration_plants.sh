#!/usr/bin/env bash
set -euo pipefail

SCRIPT_DIR="$(cd "$(dirname "${BASH_SOURCE[0]}")" && pwd)"
VERIFY_DIR="$(cd "${SCRIPT_DIR}/.." && pwd)"
ROOT="$(cd "${VERIFY_DIR}/../.." && pwd)"
LOG_DIR="${VERIFY_DIR}/logs"

cd "${ROOT}"
python3 "${SCRIPT_DIR}/make_calibration_plants.py"

LEAN_ARGS=(
  -DmaxSynthPendingDepth=3
  -DrelaxedAutoImplicit=false
)

"${HOME}/.elan/bin/lake" env lean "${LEAN_ARGS[@]}" .audit_work/SorryPlant.lean \
  > "${LOG_DIR}/calibration_sorry_compile.log" 2>&1
"${HOME}/.elan/bin/lake" env lean "${LEAN_ARGS[@]}" .audit_work/BadWitness.lean \
  > "${LOG_DIR}/calibration_bad_witness_compile.log" 2>&1
"${HOME}/.elan/bin/lake" env lean "${LEAN_ARGS[@]}" .audit_work/AxiomCalibration.lean \
  > "${LOG_DIR}/axiom_calibration_compile.log" 2>&1
echo "CALIBRATION PLANTS COMPILED"
