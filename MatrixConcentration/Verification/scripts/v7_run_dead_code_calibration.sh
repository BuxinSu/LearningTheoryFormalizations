#!/usr/bin/env bash
set -uo pipefail

ROOT="$(cd "$(dirname "${BASH_SOURCE[0]}")/../../.." && pwd)"
cd "$ROOT"

LAKE="${HOME}/.elan/bin/lake"
LOG_DIR="MatrixConcentration/Verification/logs"
PLANT=".audit_work/DeadCodePlant.lean"
PLANT_OLEAN=".audit_work/DeadCodePlant.olean"
HARNESS="MatrixConcentration/Verification/scripts/v7_dead_code_calibration.lean"

if [[ ! -f "$PLANT" ]]; then
  echo "missing calibration plant: $PLANT" >&2
  exit 2
fi

"$LAKE" env lean -o "$PLANT_OLEAN" \
  -DmaxSynthPendingDepth=3 -DrelaxedAutoImplicit=false "$PLANT" \
  > "$LOG_DIR/v7_dead_code_plant_compile.log" 2>&1
plant_status=$?

"$LAKE" env bash -c \
  'export LEAN_PATH="$PWD/.audit_work:$LEAN_PATH"; lean -DmaxSynthPendingDepth=3 -DrelaxedAutoImplicit=false "$1"' \
  _ "$HARNESS" > "$LOG_DIR/v7_dead_code_calibration.log" 2>&1
calibration_status=$?

printf 'PLANT_EXIT_STATUS %s\nCALIBRATION_EXIT_STATUS %s\n' \
  "$plant_status" "$calibration_status" \
  > "$LOG_DIR/v7_dead_code_calibration_status.log"

if [[ "$plant_status" -ne 0 || "$calibration_status" -ne 0 ]]; then
  exit 1
fi
