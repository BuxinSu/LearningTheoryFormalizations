#!/usr/bin/env bash
set -uo pipefail

ROOT="$(cd "$(dirname "${BASH_SOURCE[0]}")/../../.." && pwd)"
cd "$ROOT"

LAKE="${HOME}/.elan/bin/lake"
LOG_DIR="MatrixConcentration/Verification/logs"
WITNESS="MatrixConcentration/Verification/scripts/witnesses/V7Witnesses.lean"
BAD=".audit_work/BadWitness.lean"

"$LAKE" env lean \
  -DmaxSynthPendingDepth=3 -DrelaxedAutoImplicit=false "$WITNESS" \
  > "$LOG_DIR/v7_witnesses_compile.log" 2>&1
witness_status=$?

"$LAKE" env lean \
  -DmaxSynthPendingDepth=3 -DrelaxedAutoImplicit=false "$BAD" \
  > "$LOG_DIR/v7_bad_witness_compile.log" 2>&1
bad_status=$?

printf 'WITNESS_EXIT_STATUS %s\nBAD_WITNESS_LEAN_EXIT_STATUS %s\n' \
  "$witness_status" "$bad_status" \
  > "$LOG_DIR/v7_witness_exit_status.log"

if [[ "$witness_status" -ne 0 ]]; then
  exit "$witness_status"
fi
