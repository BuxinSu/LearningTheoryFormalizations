#!/usr/bin/env bash
# Staged orchestrator for the machine-checkable verification tiers.
#
# A plain run / `--resume` appends to an interrupted run and reuses completed
# numbered stages. `--fresh` clears every numbered stage marker and the
# digest-bound canonical-replay completion marker. Historical deletion markers
# are chronology only; current V1 runners never delete `.lake/build`.
# Final certification must use `--fresh`.

set -euo pipefail

SCRIPT_DIR="$(cd "$(dirname "${BASH_SOURCE[0]}")" && pwd)"
VERIFY="$(cd "$SCRIPT_DIR/.." && pwd)"
ROOT="$(cd "$VERIFY/../.." && pwd)"
LOGS="$VERIFY/logs"
LAKE="$HOME/.elan/bin/lake"
LEAN_ARGS=(-DmaxSynthPendingDepth=3 -DrelaxedAutoImplicit=false)
STAGE_DIR="$ROOT/.audit_work/run_all_stages"
V1_DONE_MARKER="$ROOT/.audit_work/v1_clean_build.done"
LOCK_FILE="$ROOT/.audit_work/verification.run.lock"
FINALIZATION_GUARD="$ROOT/.audit_work/verification.finalization.guard"
STATUS_FILE="$LOGS/run_all_status.log"
COORDINATION="$SCRIPT_DIR/verification_coordination.sh"

for directory in "$ROOT/.audit_work" "$LOGS" "$STAGE_DIR"; do
  if [[ -L "$directory" || ( -e "$directory" && ! -d "$directory" ) ]]; then
    echo "verification path is not a real directory: $directory" >&2
    exit 1
  fi
done
mkdir -p "$LOGS" "$STAGE_DIR"
cd "$ROOT"

source "$COORDINATION"
verification_authorize_finalization

mode="${1:---resume}"
STARTED_AT_UTC="$(date -u '+%Y-%m-%dT%H:%M:%SZ')"
STARTED_AT_EPOCH="$(date -u '+%s')"
RUN_ID="$(verification_new_run_id)"
export VERIFICATION_RUN_ID="$RUN_ID"
export VERIFICATION_PARENT_RUN_ID="$RUN_ID"
VERIFICATION_INPUT_DIGEST="UNAVAILABLE"
SOURCE_DIGEST="UNAVAILABLE"
if [[ "$#" -gt 1 ]]; then
  echo "usage: $0 [--fresh|--resume]" >&2
  exit 2
fi

# A fresh run clears shared stage markers and rewrites the authoritative log.
# Acquire a single-writer lock before either operation.  A supervising
# finalizer may already own the same lock; in that case it sets
# VERIFICATION_OUTER_LOCK_HELD=1 and this runner verifies, but does not remove,
# the outer lock.  This is the same nesting discipline used by V1 and V10.
verification_acquire_writer_lock \
  "run_all" "$LOGS/final_lifecycle_check.txt" "$RUN_ID"
cleanup_lock() {
  local code=$?
  local validation_code=0
  local release_code=0
  local run_state
  local status_tmp="$STATUS_FILE.tmp.$$"
  local finished_at_utc
  local finished_at_epoch
  local run_log_sha256="UNAVAILABLE"
  local source_digest="$SOURCE_DIGEST"
  trap - EXIT INT TERM
  verification_validate_active_lock || validation_code=$?
  if [[ "$code" -eq 0 && "$validation_code" -ne 0 ]]; then
    code="$validation_code"
  fi
  finished_at_utc="$(date -u '+%Y-%m-%dT%H:%M:%SZ')"
  finished_at_epoch="$(date -u '+%s')"
  if [[ -f "$LOGS/run_all.log" && ! -L "$LOGS/run_all.log" ]]; then
    run_log_sha256="$(shasum -a 256 "$LOGS/run_all.log" | awk '{print $1}')"
  fi
  if [[ ! "$source_digest" =~ ^[0-9a-f]{64}$ &&
        -f "$LOGS/source_manifest.txt" ]]; then
    source_digest="$(
      awk '/^TOP_LEVEL_SHA256 / { print $2 }' "$LOGS/source_manifest.txt"
    )"
  fi
  if [[ "$code" -eq 0 ]]; then
    run_state="PASS"
  else
    run_state="FAIL"
  fi
  write_status() {
    {
    echo "command: ./MatrixConcentration/Verification/scripts/run_all.sh $mode"
    echo "run_id: $RUN_ID"
    echo "run_state: $run_state"
    echo "verification_input_digest: $VERIFICATION_INPUT_DIGEST"
    echo "source_digest: $source_digest"
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
    run_state="FAIL"
    finished_at_utc="$(date -u '+%Y-%m-%dT%H:%M:%SZ')"
    finished_at_epoch="$(date -u '+%s')"
    write_status
  fi
  exit "$code"
}
trap cleanup_lock EXIT
trap 'exit 130' INT
trap 'exit 143' TERM
printf '%s\n' \
  "command: ./MatrixConcentration/Verification/scripts/run_all.sh $mode" \
  "run_id: $RUN_ID" \
  "run_state: RUNNING" \
  "started_at_utc: $STARTED_AT_UTC" \
  >"$STATUS_FILE.tmp.$$"
mv "$STATUS_FILE.tmp.$$" "$STATUS_FILE"

case "$mode" in
  --fresh)
    # Verification-stage markers are disposable controls. Clearing the
    # separate V1 completion marker forces the canonical replay to run again.
    # The isolated recovery evidence is validated or generated in its own
    # previously absent build directory; neither current V1 runner deletes
    # `.lake/build`.
    rm -f "$STAGE_DIR"/*.done "$V1_DONE_MARKER"
    exec >"$LOGS/run_all.log" 2>&1
    ;;
  --resume)
    exec >>"$LOGS/run_all.log" 2>&1
    ;;
  *)
    echo "usage: $0 [--fresh|--resume]" >&2
    exit 2
    ;;
esac

stage() {
  local id="$1"
  local label="$2"
  shift 2
  local marker="$STAGE_DIR/$id.done"
  local marker_tmp="${marker}.tmp.$$"
  if [[ -e "$marker" || -L "$marker" ]]; then
    if [[ -L "$marker" || ! -f "$marker" || ! -s "$marker" ]] ||
      [[ "$(wc -l <"$marker" | tr -d ' ')" != "3" ]] ||
      ! grep -Fxq "stage=$id" "$marker" ||
      ! grep -Fxq "label=$label" "$marker" ||
      ! grep -Eq '^completed=[0-9]{4}-[0-9]{2}-[0-9]{2}T[0-9]{2}:[0-9]{2}:[0-9]{2}Z$' "$marker"; then
      echo "invalid completed-stage marker: $marker" >&2
      return 1
    fi
    echo "===== SKIP  $label (completed marker: $marker) ====="
    return 0
  fi
  echo
  echo "===== START $label $(date '+%Y-%m-%d %H:%M:%S %Z') ====="
  local command_status=0
  "$@" || command_status=$?
  if [[ "$command_status" -ne 0 ]]; then
    echo "===== FAIL  $label exit=$command_status $(date '+%Y-%m-%d %H:%M:%S %Z') ====="
    return "$command_status"
  fi
  {
    echo "stage=$id"
    echo "label=$label"
    echo "completed=$(date -u '+%Y-%m-%dT%H:%M:%SZ')"
  } >"$marker_tmp"
  mv "$marker_tmp" "$marker"
  echo "===== PASS  $label $(date '+%Y-%m-%d %H:%M:%S %Z') ====="
}

lean_to_log() {
  local input="$1"
  local output="$2"
  /usr/bin/time -p "$LAKE" env lean "${LEAN_ARGS[@]}" "$input" \
    >"$output" 2>&1
}

echo "MATRIXCONCENTRATION MECHANICAL VERIFICATION"
echo "root=$ROOT"
echo "mode=$mode"
echo "run_id=$RUN_ID"
echo "started=$(date '+%Y-%m-%d %H:%M:%S %Z')"

# Hard gate: no downstream evidence is valid after source or claims drift.
verification_load_input_digest "$SCRIPT_DIR"
INITIAL_INPUT_DIGEST="$VERIFICATION_INPUT_DIGEST"
SOURCE_OUTPUT="$(python3 "$SCRIPT_DIR/source_manifest.py" check)"
printf '%s\n' "$SOURCE_OUTPUT"
SOURCE_DIGEST="$(
  printf '%s\n' "$SOURCE_OUTPUT" |
    awk '/^TOP_LEVEL_SHA256 / { print $2 }'
)"
if [[ ! "$SOURCE_DIGEST" =~ ^[0-9a-f]{64}$ ]]; then
  echo "source manifest did not emit one digest" >&2
  exit 1
fi

# V1: generate and compile its `sorry` positive control before parsing the
# build log, so a fresh run never relies on a pre-existing calibration log.
stage "01_environment" "environment capture" bash "$SCRIPT_DIR/capture_environment.sh"
run_v1_build_evidence() {
  env VERIFICATION_OUTER_LOCK_HELD=1 \
    bash "$SCRIPT_DIR/v1_recovery_clean_build.sh" || return $?
  env VERIFICATION_OUTER_LOCK_HELD=1 \
    bash "$SCRIPT_DIR/v1_clean_build.sh" || return $?
}
stage "02_v1_build" "V1 clean-state recovery and canonical replay" \
  run_v1_build_evidence
stage "03_plants_generate" "calibration plant generation" \
  python3 "$SCRIPT_DIR/make_calibration_plants.py"
stage "04_plants_compile" "calibration plant compilation" \
  bash "$SCRIPT_DIR/compile_calibration_plants.sh"
stage "05_v1_log_audit" "V1 build-log audit" python3 "$SCRIPT_DIR/audit_build_logs.py"
stage "06_v2_import_graph" "V2 import graph" python3 "$SCRIPT_DIR/import_graph.py"

# V3–V5 scanners reuse the positive controls compiled above.
stage "07_v3_calibration" "V3 textual calibration" \
  python3 "$SCRIPT_DIR/scan_placeholders.py" calibration
stage "08_v3_production" "V3 production scan" \
  python3 "$SCRIPT_DIR/scan_placeholders.py" production

stage "09_v4_collection" "V4 environment collection" lean_to_log \
  "$SCRIPT_DIR/axiom_audit.lean" "$LOGS/axiom_audit_compile.log"
stage "10_v4_analysis" "V4 axiom analysis" python3 "$SCRIPT_DIR/analyze_axioms.py"
stage "11_v3_v4_reconcile" "V3/V4 reconciliation" \
  python3 "$SCRIPT_DIR/reconcile_sorry_axioms.py"

stage "12_v5_calibration" "V5 calibration" \
  python3 "$SCRIPT_DIR/scan_escape_hatches.py" calibration
stage "13_v5_production" "V5 production scan" \
  python3 "$SCRIPT_DIR/scan_escape_hatches.py" production

# V8: Lean may return nonzero when #lint reports findings. The analyzer validates
# the package-scope header and exact parsed hit count, including a clean zero.
run_v8_lint() {
  set +e
  /usr/bin/time -p "$LAKE" env lean "${LEAN_ARGS[@]}" \
    "$SCRIPT_DIR/lint_package.lean" >"$LOGS/v8_lint_full.log" 2>&1
  local lint_status=$?
  set -e
  echo "V8 lint exit status=$lint_status"
  python3 "$SCRIPT_DIR/analyze_linters.py"
}
stage "14_v8_lint" "V8 package lint and analysis" run_v8_lint

# V9 machine portions. The endpoint harness is also V6 evidence, but here it
# supplies fresh compiled name-resolution and collectAxioms data.
stage "15_v9_extract" "V9 correspondence extraction" \
  python3 "$SCRIPT_DIR/v6_extract_correspondence.py"
stage "16_v9_endpoints" "V9 endpoint collection" lean_to_log \
  "$SCRIPT_DIR/v6_endpoint_telescopes.lean" \
  "$LOGS/v6_endpoint_telescopes_compile.log"
stage "17_v9_claims" "V9 claims check" \
  python3 "$SCRIPT_DIR/verify_readme_claims.py" --production
stage "18_v9_calibration" "V9 fake-name calibration" \
  bash "$SCRIPT_DIR/calibrate_readme_checker.sh"
stage "19_v9_commands" "V9 printed-command check" \
  bash "$SCRIPT_DIR/test_readme_commands.sh"
stage "20_v9_records" "V9 record chronology" \
  python3 "$SCRIPT_DIR/check_translation_records.py"

run_v10_census() {
  env VERIFICATION_OUTER_LOCK_HELD=1 \
    bash "$SCRIPT_DIR/v10_run.sh"
}
stage "21_v10" "V10 conditional-interface census" run_v10_census
cp -f -- "$LOGS/v10_run.log" "$LOGS/v10_run.aggregate.log.tmp.$$"
mv -f -- "$LOGS/v10_run.aggregate.log.tmp.$$" \
  "$LOGS/v10_run.aggregate.log"
cp -f -- "$LOGS/v10_run_status.log" \
  "$LOGS/v10_run_status.aggregate.log.tmp.$$"
mv -f -- "$LOGS/v10_run_status.aggregate.log.tmp.$$" \
  "$LOGS/v10_run_status.aggregate.log"

# Refresh V2 once after all scratch-producing stages so its excluded-scratch
# enumeration describes the delivered audit state, not only the early stage.
echo
echo "===== START final V2 scratch refresh $(date '+%Y-%m-%d %H:%M:%S %Z') ====="
python3 "$SCRIPT_DIR/import_graph.py"
echo "===== PASS  final V2 scratch refresh $(date '+%Y-%m-%d %H:%M:%S %Z') ====="

# README/report consistency is last and always reruns because Verification
# reports/README are intentionally outside the immutable source manifest.
echo
echo "===== START README/report consistency $(date '+%Y-%m-%d %H:%M:%S %Z') ====="
python3 "$SCRIPT_DIR/check_consistency.py"
echo "===== PASS  README/report consistency $(date '+%Y-%m-%d %H:%M:%S %Z') ====="

echo
echo "===== FINAL SOURCE MANIFEST STABILITY $(date '+%Y-%m-%d %H:%M:%S %Z') ====="
python3 "$SCRIPT_DIR/source_manifest.py" check
verification_load_input_digest "$SCRIPT_DIR"
if [[ "$VERIFICATION_INPUT_DIGEST" != "$INITIAL_INPUT_DIGEST" ]]; then
  echo "verification input digest changed during aggregate run" >&2
  exit 1
fi

echo
echo "ALL MACHINE STAGES PASSED"
echo "finished=$(date '+%Y-%m-%d %H:%M:%S %Z')"
echo "Review-tier V6 Tier B, V7 judgments, and V10 semantic adjudication are documented but not regenerated here."
