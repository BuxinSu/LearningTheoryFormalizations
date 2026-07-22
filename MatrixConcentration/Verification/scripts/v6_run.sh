#!/usr/bin/env bash
# Self-contained staged rerun for V6 (machine tiers plus curated-ledger checks).

set -euo pipefail

SCRIPT_DIR="$(cd "$(dirname "${BASH_SOURCE[0]}")" && pwd)"
VERIFY="$(cd "$SCRIPT_DIR/.." && pwd)"
ROOT="$(cd "$VERIFY/../.." && pwd)"
LOGS="$VERIFY/logs"
LAKE="$HOME/.elan/bin/lake"
LEAN_ARGS=(-DmaxSynthPendingDepth=3 -DrelaxedAutoImplicit=false)
STATUS_FILE="$LOGS/v6_run_status.log"
LOCK_FILE="$ROOT/.audit_work/verification.run.lock"
FINALIZATION_GUARD="$ROOT/.audit_work/verification.finalization.guard"
COORDINATION="$SCRIPT_DIR/verification_coordination.sh"
STARTED_AT_UTC="$(date -u '+%Y-%m-%dT%H:%M:%SZ')"
STARTED_AT_EPOCH="$(date -u '+%s')"
SOURCE_DIGEST="UNAVAILABLE"
VERIFICATION_INPUT_DIGEST="UNAVAILABLE"

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

# V6, V7, and the machine orchestrator rewrite overlapping evidence.  An
# atomic, shared file lock prevents any pair of them from running together.
verification_acquire_writer_lock \
  "v6" "$LOGS/final_lifecycle_check.txt" "$RUN_ID"

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
  if [[ -f "$LOGS/v6_run.log" && ! -L "$LOGS/v6_run.log" ]]; then
    run_log_sha256="$(shasum -a 256 "$LOGS/v6_run.log" | awk '{print $1}')"
  fi
  write_status() {
    {
      echo "command: ./MatrixConcentration/Verification/scripts/v6_run.sh"
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

exec >"$LOGS/v6_run.log" 2>&1
printf '%s\n' \
  "command: ./MatrixConcentration/Verification/scripts/v6_run.sh" \
  "run_id: $RUN_ID" \
  "run_state: RUNNING" \
  "started_at_utc: $STARTED_AT_UTC" \
  >"$STATUS_FILE.tmp.$$"
mv "$STATUS_FILE.tmp.$$" "$STATUS_FILE"

stage() {
  local label="$1"
  shift
  echo
  echo "===== START $label ====="
  "$@"
  echo "===== PASS  $label ====="
}

lean_to_log() {
  local input="$1"
  local output="$2"
  "$LAKE" env lean "${LEAN_ARGS[@]}" "$input" >"$output" 2>&1
}

lean_with_status() {
  local input="$1"
  local output="$2"
  local status_file="$3"
  local status=0
  {
    echo "command: ~/.elan/bin/lake env lean ${LEAN_ARGS[*]} $input"
    echo "run_state: RUNNING"
    echo "started_at_utc: $(date -u '+%Y-%m-%dT%H:%M:%SZ')"
  } >"$status_file.tmp.$$"
  mv "$status_file.tmp.$$" "$status_file"
  "$LAKE" env lean "${LEAN_ARGS[@]}" "$input" >"$output" 2>&1 || status=$?
  {
    echo "command: ~/.elan/bin/lake env lean ${LEAN_ARGS[*]} $input"
    if (( status == 0 )); then
      echo "run_state: PASS"
    else
      echo "run_state: FAIL"
    fi
    echo "exit_code: $status"
    echo "finished_at_utc: $(date -u '+%Y-%m-%dT%H:%M:%SZ')"
    echo "stdout_stderr_bytes: $(wc -c <"$output" | tr -d ' ')"
  } >"$status_file.tmp.$$"
  mv "$status_file.tmp.$$" "$status_file"
  return "$status"
}

echo "V6 VACUITY AND TRIVIALITY AUDIT"
echo "root=$ROOT"
echo "run_id=$RUN_ID"
verification_load_input_digest "$SCRIPT_DIR"
INITIAL_INPUT_DIGEST="$VERIFICATION_INPUT_DIGEST"

# Hard gate: V6 evidence cannot be refreshed against a different source tree.
stage "source manifest gate" \
  python3 "$SCRIPT_DIR/source_manifest.py" check
python3 "$SCRIPT_DIR/source_manifest.py" check \
  >"$LOGS/v6_manifest_check.log" 2>&1
SOURCE_DIGEST="$(
  awk '/^TOP_LEVEL_SHA256 / { print $2 }' "$LOGS/v6_manifest_check.log"
)"
if [[ ! "$SOURCE_DIGEST" =~ ^[0-9a-f]{64}$ ]]; then
  echo "V6 source manifest did not emit one digest" >&2
  exit 1
fi

stage "calibration generation" \
  python3 "$SCRIPT_DIR/make_calibration_plants.py"

stage "correspondence extraction" \
  python3 "$SCRIPT_DIR/v6_extract_correspondence.py"
stage "compiled endpoint telescopes" lean_to_log \
  "$SCRIPT_DIR/v6_endpoint_telescopes.lean" \
  "$LOGS/v6_endpoint_telescopes_compile.log"

stage "Tier-A calibrated statement scan" \
  python3 "$SCRIPT_DIR/v6_scan_vacuity.py"
stage "Tier-A hit adjudication" \
  python3 "$SCRIPT_DIR/v6_adjudicate_tier_a.py"

stage "auto-bound positive-control compilation" lean_with_status \
  ".audit_work/V6AutoImplicitPlant.lean" \
  "$LOGS/v6_autoimplicit_calibration_compile.log" \
  "$LOGS/v6_autoimplicit_calibration_compile_status.log"
stage "auto-bound source/environment audit" \
  python3 "$SCRIPT_DIR/v6_audit_autoimplicit.py"

# The following stages never synthesize review judgments. They fail unless all
# eight immutable human-curated chapter ledgers are complete and source-valid.
stage "curated Tier-B merge" \
  python3 "$SCRIPT_DIR/v6_merge_curated_tier_b.py"
stage "curated Tier-B independent validation" \
  python3 "$SCRIPT_DIR/v6_validate_curated_tier_b.py"

stage "uniform all-OK Tier-C sample" \
  python3 "$SCRIPT_DIR/v6_sample_ok.py"
stage "library endpoint dependency collection" lean_to_log \
  "$SCRIPT_DIR/v6_endpoint_citations.lean" \
  "$LOGS/v6_endpoint_citations_compile.log"

stage "witness and bad-witness compilation" \
  python3 "$SCRIPT_DIR/v6_compile_witnesses.py"
stage "witness acceptance" \
  python3 "$SCRIPT_DIR/v6_check_witnesses.py"
stage "dynamic Tier-C environment evidence" \
  python3 "$SCRIPT_DIR/v6_compile_tier_c_evidence.py"
stage "dynamic Tier-C fail-closed validation" \
  python3 "$SCRIPT_DIR/v6_validate_tier_c.py"

stage "maxSummandSq containment" lean_to_log \
  "$SCRIPT_DIR/v6_maxsummand_users.lean" \
  "$LOGS/v6_maxsummand_users_compile.log"

stage "V6 report assembly" \
  python3 "$SCRIPT_DIR/v6_assemble_report.py"

echo
echo "===== FINAL SOURCE MANIFEST STABILITY ====="
python3 "$SCRIPT_DIR/source_manifest.py" check
verification_load_input_digest "$SCRIPT_DIR"
if [[ "$VERIFICATION_INPUT_DIGEST" != "$INITIAL_INPUT_DIGEST" ]]; then
  echo "verification input digest changed during V6" >&2
  exit 1
fi

echo
echo "V6 ALL STAGES PASSED"
