#!/usr/bin/env bash
set -euo pipefail

ROOT="$(cd "$(dirname "${BASH_SOURCE[0]}")/../../.." && pwd)"
cd "$ROOT"

LAKE="${HOME}/.elan/bin/lake"
SCRIPTS="MatrixConcentration/Verification/scripts"
LOGS="MatrixConcentration/Verification/logs"
LEAN_FLAGS=(-DmaxSynthPendingDepth=3 -DrelaxedAutoImplicit=false)
LOCK_FILE="$ROOT/.audit_work/verification.run.lock"
FINALIZATION_GUARD="$ROOT/.audit_work/verification.finalization.guard"
STATUS_FILE="$LOGS/v7_run_status.log"
COORDINATION="$SCRIPTS/verification_coordination.sh"
STARTED_AT_UTC="$(date -u '+%Y-%m-%dT%H:%M:%SZ')"
STARTED_AT_EPOCH="$(date -u '+%s')"
VERIFICATION_INPUT_DIGEST="UNAVAILABLE"
SOURCE_DIGEST="UNAVAILABLE"
load_bearing="UNAVAILABLE"
covered="UNAVAILABLE"
dead_code="UNAVAILABLE"

for directory in "$LOGS" "$ROOT/.audit_work"; do
  if [[ -L "$directory" || ( -e "$directory" && ! -d "$directory" ) ]]; then
    echo "verification path is not a real directory: $directory" >&2
    exit 1
  fi
done
mkdir -p "$LOGS" "$ROOT/.audit_work"

source "$COORDINATION"
verification_authorize_finalization
RUN_ID="$(verification_new_run_id)"
export VERIFICATION_RUN_ID="$RUN_ID"

# V6, V7, and the machine orchestrator rewrite overlapping evidence.  Refuse
# a concurrent writer before any delivered log is opened.
verification_acquire_writer_lock \
  "v7" "$LOGS/final_lifecycle_check.txt" "$RUN_ID"

finish() {
  local code=$?
  local validation_code=0
  local release_code=0
  local status_tmp="$STATUS_FILE.tmp.$$"
  local finished_at_utc
  local finished_at_epoch
  local run_log_sha256="UNAVAILABLE"
  trap - EXIT INT TERM
  verification_validate_active_lock || validation_code=$?
  if [[ "$code" -eq 0 && "$validation_code" -ne 0 ]]; then
    code="$validation_code"
  fi
  finished_at_utc="$(date -u '+%Y-%m-%dT%H:%M:%SZ')"
  finished_at_epoch="$(date -u '+%s')"
  if [[ -f "$LOGS/v7_run.log" && ! -L "$LOGS/v7_run.log" ]]; then
    run_log_sha256="$(shasum -a 256 "$LOGS/v7_run.log" | awk '{print $1}')"
  fi
  write_status() {
    {
      echo "command: ./MatrixConcentration/Verification/scripts/v7_run.sh"
      echo "run_id: $RUN_ID"
      if [[ "$code" -eq 0 ]]; then
        echo "run_state: PASS"
      else
        echo "run_state: FAIL"
      fi
      echo "verification_input_digest: $VERIFICATION_INPUT_DIGEST"
      echo "source_digest: $SOURCE_DIGEST"
      echo "started_at_utc: $STARTED_AT_UTC"
      echo "finished_at_utc: $finished_at_utc"
      echo "elapsed_seconds: $((finished_at_epoch - STARTED_AT_EPOCH))"
      echo "run_log_sha256: $run_log_sha256"
      echo "load_bearing_definitions: $load_bearing"
      echo "sanity_covered: $covered"
      echo "dead_code_candidates: $dead_code"
      echo "exit_code: $code"
    } >"$status_tmp"
    mv "$status_tmp" "$STATUS_FILE"
  }
  write_status
  verification_release_writer_lock || release_code=$?
  if [[ "$code" -eq 0 && "$release_code" -ne 0 ]]; then
    code="$release_code"
    finished_at_utc="$(date -u '+%Y-%m-%dT%H:%M:%SZ')"
    finished_at_epoch="$(date -u '+%s')"
    write_status
  fi
  exit "$code"
}
trap finish EXIT
trap 'exit 130' INT
trap 'exit 143' TERM

exec >"$LOGS/v7_run.log" 2>&1
printf '%s\n' \
  "command: ./MatrixConcentration/Verification/scripts/v7_run.sh" \
  "run_id: $RUN_ID" \
  "run_state: RUNNING" \
  "started_at_utc: $STARTED_AT_UTC" \
  >"$STATUS_FILE.tmp.$$"
mv "$STATUS_FILE.tmp.$$" "$STATUS_FILE"

echo "V7 DEFINITION SANITY AUDIT"
echo "run_id=$RUN_ID"
verification_load_input_digest "$SCRIPTS"
INITIAL_INPUT_DIGEST="$VERIFICATION_INPUT_DIGEST"

python3 "$SCRIPTS/source_manifest.py" check \
  > "$LOGS/v7_manifest_check.log" 2>&1
SOURCE_DIGEST="$(
  awk '/^TOP_LEVEL_SHA256 / { print $2 }' "$LOGS/v7_manifest_check.log"
)"
if [[ ! "$SOURCE_DIGEST" =~ ^[0-9a-f]{64}$ ]]; then
  echo "V7 source manifest did not emit one digest" >&2
  exit 1
fi
python3 "$SCRIPTS/make_calibration_plants.py" \
  > "$LOGS/v7_calibration_plant_generation.log" 2>&1

# Recreate the correspondence endpoint input used by the load-bearing rule.
python3 "$SCRIPTS/v6_extract_correspondence.py" \
  > "$LOGS/v7_correspondence_extract_prerequisite.log" 2>&1
"$LAKE" env lean "${LEAN_FLAGS[@]}" "$SCRIPTS/v6_endpoint_telescopes.lean" \
  > "$LOGS/v7_endpoint_telescopes_prerequisite_compile.log" 2>&1

# Enumerate source declarations, dump elaborated dependencies, and compute the
# exact load-bearing and source-level zero-referrer sets.
python3 "$SCRIPTS/v7_extract_source_declarations.py" \
  > "$LOGS/v7_source_inventory_run.log" 2>&1
"$LAKE" env lean "${LEAN_FLAGS[@]}" "$SCRIPTS/v7_environment_dependencies.lean" \
  > "$LOGS/v7_environment_dependencies_compile.log" 2>&1
python3 "$SCRIPTS/v7_analyze_dependencies.py" \
  > "$LOGS/v7_dependency_analysis_run.log" 2>&1

# Compile non-degeneracy witnesses, exercise both mandatory calibrations, and
# fail closed while assembling the evidence register.
bash "$SCRIPTS/v7_run_witnesses.sh" \
  > "$LOGS/v7_witness_runner.log" 2>&1
bash "$SCRIPTS/v7_run_dead_code_calibration.sh" \
  > "$LOGS/v7_dead_code_runner.log" 2>&1
python3 "$SCRIPTS/v7_check_sanity.py" \
  > "$LOGS/v7_sanity_checker_run.log" 2>&1

# Reject evidence assembled across a source change during this long runner.
python3 "$SCRIPTS/source_manifest.py" check \
  > "$LOGS/v7_final_manifest_check.log" 2>&1
verification_load_input_digest "$SCRIPTS"
if [[ "$VERIFICATION_INPUT_DIGEST" != "$INITIAL_INPUT_DIGEST" ]]; then
  echo "verification input digest changed during V7" >&2
  exit 1
fi

load_bearing="$(awk '$1 == "LOAD_BEARING_DEFINITIONS" {print $2}' \
  "$LOGS/v7_sanity_summary.log")"
covered="$(awk '$1 == "COVERED" {print $2}' \
  "$LOGS/v7_sanity_summary.log")"
dead_code="$(awk '$1 == "DEAD_CODE_AFTER_TERMINAL_EXCLUSION" {print $2}' \
  "$LOGS/v7_dependency_summary.log")"
dead_code_public="$(awk '$1 == "DEAD_CODE_PUBLIC" {print $2}' \
  "$LOGS/v7_dependency_summary.log")"
dead_code_private="$(awk '$1 == "DEAD_CODE_PRIVATE" {print $2}' \
  "$LOGS/v7_dependency_summary.log")"
if [[ "$load_bearing" != "51" || "$covered" != "51" ||
      ! "$dead_code" =~ ^[0-9]+$ ||
      ! "$dead_code_public" =~ ^[0-9]+$ ||
      ! "$dead_code_private" =~ ^[0-9]+$ ||
      "$dead_code" -ne $((dead_code_public + dead_code_private)) ]]; then
  echo "V7 terminal metric extraction failed: load_bearing=$load_bearing covered=$covered dead_code=$dead_code" >&2
  exit 1
fi

echo "V7 ALL STAGES PASSED"
