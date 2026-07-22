#!/usr/bin/env bash
# Fail-closed, re-runnable machine entrypoint for the V10 census.
#
# A standalone invocation acquires the shared verification writer lock.
# run_all.sh sets VERIFICATION_OUTER_LOCK_HELD=1 while it owns that lock.

set -euo pipefail

SCRIPT_DIR="$(cd "$(dirname "${BASH_SOURCE[0]}")" && pwd)"
VERIFY="$(cd "$SCRIPT_DIR/.." && pwd)"
ROOT="$(cd "$VERIFY/../.." && pwd)"
LOGS="$VERIFY/logs"
LAKE="$HOME/.elan/bin/lake"
LEAN_ARGS=(-DmaxSynthPendingDepth=3 -DrelaxedAutoImplicit=false)
STATUS_FILE="$LOGS/v10_run_status.log"
LOCK_FILE="$ROOT/.audit_work/verification.run.lock"
FINALIZATION_GUARD="$ROOT/.audit_work/verification.finalization.guard"
COORDINATION="$SCRIPT_DIR/verification_coordination.sh"
VERIFICATION_INPUT_DIGEST="UNAVAILABLE"
SOURCE_DIGEST="UNAVAILABLE"

for directory in "$LOGS" "$ROOT/.audit_work"; do
  if [[ -L "$directory" || ( -e "$directory" && ! -d "$directory" ) ]]; then
    echo "verification path is not a real directory: $directory" >&2
    exit 1
  fi
done
mkdir -p "$LOGS" "$ROOT/.audit_work"
cd "$ROOT"

source "$COORDINATION"
verification_authorize_finalization
RUN_ID="$(verification_new_run_id)"
export VERIFICATION_RUN_ID="$RUN_ID"
PARENT_RUN_ID="${VERIFICATION_PARENT_RUN_ID:-standalone}"
verification_acquire_writer_lock \
  "v10_run" "$LOGS/final_lifecycle_check.txt" "$RUN_ID"

STARTED_AT_UTC="$(date -u '+%Y-%m-%dT%H:%M:%SZ')"
STARTED_AT_EPOCH="$(date -u '+%s')"
CURRENT_STAGE="initialization"

finish() {
  local code=$?
  local validation_code=0
  local release_code=0
  local finished_at_utc
  local finished_at_epoch
  local run_state
  local status_tmp="$STATUS_FILE.tmp.$$"
  local run_log_sha256="UNAVAILABLE"

  trap - EXIT INT TERM
  set +e
  verification_validate_active_lock
  validation_code=$?
  if [[ "$code" -eq 0 && "$validation_code" -ne 0 ]]; then
    code="$validation_code"
  fi
  finished_at_utc="$(date -u '+%Y-%m-%dT%H:%M:%SZ')"
  finished_at_epoch="$(date -u '+%s')"
  if [[ "$code" -eq 0 ]]; then
    run_state="PASS"
  else
    run_state="FAIL"
  fi
  if [[ -f "$LOGS/v10_run.log" && ! -L "$LOGS/v10_run.log" ]]; then
    run_log_sha256="$(shasum -a 256 "$LOGS/v10_run.log" | awk '{print $1}')"
  fi
  write_status() {
    {
      echo "command: ./MatrixConcentration/Verification/scripts/v10_run.sh"
      echo "run_id: $RUN_ID"
      echo "parent_run_id: $PARENT_RUN_ID"
      echo "run_state: $run_state"
      echo "verification_input_digest: $VERIFICATION_INPUT_DIGEST"
      echo "source_digest: $SOURCE_DIGEST"
      echo "started_at_utc: $STARTED_AT_UTC"
      echo "finished_at_utc: $finished_at_utc"
      echo "elapsed_seconds: $((finished_at_epoch - STARTED_AT_EPOCH))"
      echo "run_log_sha256: $run_log_sha256"
      echo "exit_code: $code"
      echo "last_stage: $CURRENT_STAGE"
    } >"$status_tmp"
    mv "$status_tmp" "$STATUS_FILE"
  }
  write_status
  verification_release_writer_lock
  release_code=$?
  if [[ "$code" -eq 0 && "$release_code" -ne 0 ]]; then
    code="$release_code"
    run_state="FAIL"
    finished_at_utc="$(date -u '+%Y-%m-%dT%H:%M:%SZ')"
    finished_at_epoch="$(date -u '+%s')"
    write_status
  fi
  exit "$code"
}
trap finish EXIT
trap 'exit 130' INT
trap 'exit 143' TERM

exec >"$LOGS/v10_run.log" 2>&1
{
  echo "command: ./MatrixConcentration/Verification/scripts/v10_run.sh"
  echo "run_id: $RUN_ID"
  echo "parent_run_id: $PARENT_RUN_ID"
  echo "run_state: RUNNING"
  echo "started_at_utc: $STARTED_AT_UTC"
  echo "runner_pid: $$"
  echo "lean_flags: ${LEAN_ARGS[*]}"
} >"$STATUS_FILE.tmp.$$"
mv "$STATUS_FILE.tmp.$$" "$STATUS_FILE"

stage() {
  local label="$1"
  shift
  CURRENT_STAGE="$label"
  echo "===== START $label $(date -u '+%Y-%m-%dT%H:%M:%SZ') ====="
  "$@"
  echo "===== PASS  $label $(date -u '+%Y-%m-%dT%H:%M:%SZ') ====="
}

lean_to_log() {
  local input="$1"
  local output="$2"
  local status
  set +e
  /usr/bin/time -p "$LAKE" env lean "${LEAN_ARGS[@]}" "$input" \
    >"$output" 2>&1
  status=$?
  set -e
  printf 'LEAN_EXIT_STATUS %s\n' "$status" >>"$output"
  return "$status"
}

echo "V10 CONDITIONAL-INTERFACE CENSUS"
echo "root=$ROOT"
echo "run_id=$RUN_ID"
echo "parent_run_id=$PARENT_RUN_ID"
echo "started_at_utc=$STARTED_AT_UTC"
verification_load_input_digest "$SCRIPT_DIR"
INITIAL_INPUT_DIGEST="$VERIFICATION_INPUT_DIGEST"

stage "initial source manifest gate" \
  python3 "$SCRIPT_DIR/source_manifest.py" check
python3 "$SCRIPT_DIR/source_manifest.py" check \
  >"$LOGS/v10_manifest_check.log" 2>&1
SOURCE_DIGEST="$(
  awk '/^TOP_LEVEL_SHA256 / { print $2 }' "$LOGS/v10_manifest_check.log"
)"
if [[ ! "$SOURCE_DIGEST" =~ ^[0-9a-f]{64}$ ]]; then
  echo "V10 source manifest did not emit one digest" >&2
  exit 1
fi

stage "calibration plant generation" \
  python3 "$SCRIPT_DIR/make_calibration_plants.py"

stage "conditional calibration compilation" lean_to_log \
  ".audit_work/ConditionalPlant.lean" \
  "$LOGS/v10_conditional_calibration_compile.log"

# `lake env lean` does not inherit lakefile leanOptions.  These two explicit
# flags reproduce the library-adjacent caveats required by the audit protocol;
# the lakefile linter set is intentionally unavailable in single-file mode.
stage "environment census collection" lean_to_log \
  "$SCRIPT_DIR/v10_environment.lean" \
  "$LOGS/v10_environment_compile.log"

stage "concrete witness compilation" lean_to_log \
  "$SCRIPT_DIR/witnesses/V10Witnesses.lean" \
  "$LOGS/v10_witnesses_compile.log"

stage "census reconciliation and adjudication" \
  python3 "$SCRIPT_DIR/v10_census.py"

stage "final source manifest stability" \
  python3 "$SCRIPT_DIR/source_manifest.py" check
python3 "$SCRIPT_DIR/source_manifest.py" check \
  >"$LOGS/v10_final_manifest_check.log" 2>&1
verification_load_input_digest "$SCRIPT_DIR"
if [[ "$VERIFICATION_INPUT_DIGEST" != "$INITIAL_INPUT_DIGEST" ]]; then
  echo "verification input digest changed during V10" >&2
  exit 1
fi

CURRENT_STAGE="complete"
echo "V10 ALL MACHINE STAGES PASSED"
