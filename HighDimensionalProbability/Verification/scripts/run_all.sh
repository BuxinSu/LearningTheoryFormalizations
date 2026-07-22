#!/usr/bin/env bash
#
# Static, manifest-first orchestrator for the machine portions of V1--V5,
# V8, V9, V10, and the final report/README consistency check.
#
# Expensive Lean/Lake evidence is never regenerated here.  A completed heavy
# run is treated as an immutable input, validated, hashed into its stage
# record, and reused on later invocations.  Missing evidence stops at that
# stage so a later invocation resumes there.  This script never invokes the
# one-time clean-build deletion helper.

set -euo pipefail
IFS=$'\n\t'
umask 022

readonly SCRIPT_PATH="$(cd -- "$(dirname -- "${BASH_SOURCE[0]}")" && pwd -P)/$(basename -- "${BASH_SOURCE[0]}")"
readonly SCRIPT_DIR="$(dirname -- "$SCRIPT_PATH")"
readonly VERIFY_DIR="$(cd -- "$SCRIPT_DIR/.." && pwd -P)"
readonly HDP_DIR="$(cd -- "$VERIFY_DIR/.." && pwd -P)"
readonly PROJECT_ROOT="$(cd -- "$HDP_DIR/.." && pwd -P)"
readonly LOG_DIR="$VERIFY_DIR/logs"
readonly REVIEW_DIR="$VERIFY_DIR/review"
readonly STATIC_CHECKER="$SCRIPT_DIR/run_all_static_checks.py"
readonly SOURCE_MANIFEST="${RUN_ALL_SOURCE_MANIFEST:-$LOG_DIR/source_manifest.txt}"
readonly PYTHON="${PYTHON:-python3}"
readonly STATE_SCHEMA="recert-static-machine-v10"
readonly EXPECTED_FILE_WALK_COUNT="222"

readonly AUTO_IMPLICIT_LOG="${RUN_ALL_AUTO_IMPLICIT_LOG:-$LOG_DIR/recert_v5_auto_implicit_probe.log}"
readonly V5_INSTANCE_LOG="${RUN_ALL_V5_INSTANCE_LOG:-$LOG_DIR/recert_v5_instance_audit_build.log}"
readonly V5_SCRATCH_JSON="${RUN_ALL_V5_SCRATCH_JSON:-$LOG_DIR/recert_v5_scratch.json}"
readonly V5_SCRATCH_TSV="${RUN_ALL_V5_SCRATCH_TSV:-$LOG_DIR/recert_v5_scratch.tsv}"
readonly V5_SCRATCH_SUMMARY="${RUN_ALL_V5_SCRATCH_SUMMARY:-$LOG_DIR/recert_v5_scratch_summary.txt}"
readonly V5_SCRATCH_INVENTORY="${RUN_ALL_V5_SCRATCH_INVENTORY:-$LOG_DIR/recert_v5_scratch_inventory.tsv}"
readonly V8_LOG="${RUN_ALL_V8_LOG:-$LOG_DIR/recert_v8_package_lint.log}"
readonly V8_JSON="${RUN_ALL_V8_JSON:-$LOG_DIR/recert_v8_package_lint.json}"
readonly V9_AXIOM_LOG="${RUN_ALL_V9_AXIOM_LOG:-$LOG_DIR/recert_v9_readme_axioms_build.log}"
readonly V9_AXIOM_TSV="${RUN_ALL_V9_AXIOM_TSV:-$LOG_DIR/recert_v9_readme_axioms.tsv}"
readonly V9_AXIOM_SUMMARY="${RUN_ALL_V9_AXIOM_SUMMARY:-$LOG_DIR/recert_v9_readme_axioms_summary.txt}"
readonly V10_PLANTED_LOG="${RUN_ALL_V10_PLANTED_LOG:-$LOG_DIR/v10_planted_build.log}"
readonly V10_HARNESS_LOG="${RUN_ALL_V10_HARNESS_LOG:-$LOG_DIR/v10_harness_build.log}"
readonly V10_APPENDIX_WITNESS_LOG="${RUN_ALL_V10_APPENDIX_WITNESS_LOG:-$LOG_DIR/v10_pass07_appendix_axioms_build.log}"
readonly V10_SUMMARY="${RUN_ALL_V10_SUMMARY:-$LOG_DIR/v10_summary.txt}"
readonly V10_CHECK="${RUN_ALL_V10_CHECK:-$LOG_DIR/v10_check.log}"

export PYTHONDONTWRITEBYTECODE=1

SOURCE_DIGEST=""
SCRATCH_DIGEST=""
INVENTORY_DIGEST=""
ORCHESTRATOR_SHA=""
CHECKER_SHA=""
TOOLCHAIN_SHA=""
CONFIG_DIGEST=""
PLAN_DIGEST=""
STATE_DIR=""
SELF_TEST_MODE=0
STOP_AFTER=""
ACTIVE_STAGE_LOCK=""

readonly STAGES=(
  "01_v1_build_integrity"
  "02_v2_import_graph"
  "03_v3_placeholder_census"
  "04_v4_axiom_audit"
  "05_v5_escape_hatches"
  "08_v8_package_lint"
  "09_v9_published_claims"
  "10_v10_conditional_interfaces"
  "11_consistency"
)

die() {
  printf 'RUN_ALL_FATAL: %s\n' "$*" >&2
  exit 1
}

release_stage_lock() {
  if [[ -n "$ACTIVE_STAGE_LOCK" && -d "$ACTIVE_STAGE_LOCK" ]]; then
    # Google Drive can materialize its zero-byte Finder metadata file inside
    # even a very short-lived directory.  It is not lock state, and the audit
    # file-walk rules already require this exact Icon<CR> junk name to be
    # ignored.  Remove only that safe shape; any other entry still makes lock
    # release fail loudly.
    local icon_junk="$ACTIVE_STAGE_LOCK/Icon"$'\r'
    if [[ -e "$icon_junk" || -L "$icon_junk" ]]; then
      if [[ ! -f "$icon_junk" || -L "$icon_junk" || -s "$icon_junk" ]]; then
        printf 'RUN_ALL_FATAL: unsafe Icon<CR> entry in stage lock %s\n' \
          "$ACTIVE_STAGE_LOCK" >&2
        ACTIVE_STAGE_LOCK=""
        return 1
      fi
      /bin/rm -f -- "$icon_junk" || {
        printf 'RUN_ALL_FATAL: could not discard Icon<CR> lock junk %s\n' \
          "$ACTIVE_STAGE_LOCK" >&2
        ACTIVE_STAGE_LOCK=""
        return 1
      }
    fi
    if ! /bin/rmdir -- "$ACTIVE_STAGE_LOCK"; then
      printf 'RUN_ALL_FATAL: could not release stage lock %s\n' \
        "$ACTIVE_STAGE_LOCK" >&2
      ACTIVE_STAGE_LOCK=""
      return 1
    fi
  fi
  ACTIVE_STAGE_LOCK=""
}

print_command() {
  printf '+'
  printf ' %q' "$@"
  printf '\n'
}

run_command() {
  print_command "$@"
  "$@"
}

run_to_file() {
  local output="$1"
  shift
  print_command "$@"
  "$@" >"$output"
}

resolve_path() {
  local candidate="$1"
  if [[ "$candidate" = /* ]]; then
    printf '%s\n' "$candidate"
  else
    printf '%s\n' "$PROJECT_ROOT/$candidate"
  fi
}

canonical_path() {
  local resolved directory
  resolved="$(resolve_path "$1")"
  directory="$(cd -- "$(dirname -- "$resolved")" && pwd -P)" ||
    die "cannot canonicalize parent directory for $resolved"
  printf '%s/%s\n' "$directory" "$(basename -- "$resolved")"
}

require_file() {
  local path="$1"
  [[ -f "$path" && ! -L "$path" && -s "$path" ]] ||
    die "required immutable evidence is missing, empty, or a symlink: $path"
}

require_text() {
  local path="$1"
  local text="$2"
  require_file "$path"
  grep -Fq -- "$text" "$path" ||
    die "required evidence text not found in $path: $text"
}

require_final_line() {
  local path="$1"
  local text="$2"
  require_file "$path"
  [[ "$(tail -n 1 -- "$path")" == "$text" ]] ||
    die "required final evidence line not found in $path: $text"
}

require_no_completion_placeholder() {
  local path="$1"
  require_file "$path"
  if grep -Eiq \
    '(^|[^[:alnum:]_])(PENDING|TBD)([^[:alnum:]_]|$)|[[:alnum:]_]*TO_FILL[[:alnum:]_]*' \
    "$path"; then
    die "final deliverable still contains a completion placeholder: $path"
  fi
}

require_final_report() {
  local report="$1"
  local verdict_count verdict
  require_file "$report"
  verdict_count="$(
    grep -Ec '^\*\*Verdict: [A-Z][A-Z-]*\*\*[[:space:]]*$' "$report" ||
      true
  )"
  [[ "$verdict_count" == "1" ]] ||
    die "final report must contain exactly one canonical verdict: $report"
  verdict="$(
    sed -nE \
      's/^\*\*Verdict: ([A-Z][A-Z-]*)\*\*[[:space:]]*$/\1/p' \
      "$report"
  )"
  case "$verdict" in
    PASS|PASS-WITH-NOTES|ISSUES-FOUND) ;;
    INCOMPLETE)
      die "final report still has an incomplete verdict: $report"
      ;;
    *) die "final report has unsupported verdict $verdict: $report" ;;
  esac
  require_no_completion_placeholder "$report"
}

record_evidence() {
  local attempt_dir="$1"
  shift
  local path evidence_paths initial_manifest
  evidence_paths="$attempt_dir/evidence.paths"
  initial_manifest="$attempt_dir/evidence.initial.sha256"
  for path in "$@"; do
    path="$(resolve_path "$path")"
    require_file "$path"
    if grep -Fxq -- "$path" "$evidence_paths"; then
      die "stage attempted to record the same evidence twice: $path"
    fi
    printf '%s\n' "$path" >>"$evidence_paths"
    shasum -a 256 "$path" >>"$initial_manifest"
  done
}

manifest_check() {
  run_command "$PYTHON" -B "$SCRIPT_DIR/source_manifest.py" \
    --check "$SOURCE_MANIFEST"
}

assert_manifest_quiet() {
  if [[ "$SELF_TEST_MODE" == "1" ]]; then
    return 0
  fi
  local output
  if ! output="$("$PYTHON" -B "$SCRIPT_DIR/source_manifest.py" \
      --check "$SOURCE_MANIFEST" 2>&1)"; then
    printf '%s\n' "$output" >&2
    die "source manifest drifted; no stage evidence was accepted"
  fi
}

current_scratch_digest() {
  if [[ "$SELF_TEST_MODE" == "1" ]]; then
    [[ -d "$SELFTEST_SCRATCH_DIR" ]] ||
      die "self-test scratch directory is missing"
    find "$SELFTEST_SCRATCH_DIR" -type f -name '*.lean' -print |
      LC_ALL=C sort |
      while IFS= read -r scratch; do
        printf '%s\n' "$scratch"
        shasum -a 256 "$scratch"
      done |
      shasum -a 256 | awk '{print $1}'
    return 0
  fi
  "$PYTHON" -B "$STATIC_CHECKER" scratch-fingerprint
}

current_inventory_digest() {
  if [[ "$SELF_TEST_MODE" == "1" ]]; then
    [[ -d "$SELFTEST_INVENTORY_DIR" ]] ||
      die "self-test inventory directory is missing"
    find "$SELFTEST_INVENTORY_DIR" -maxdepth 1 -type f -print |
      LC_ALL=C sort |
      while IFS= read -r evidence; do
        printf '%s\n' "$evidence"
        shasum -a 256 "$evidence"
      done |
      shasum -a 256 | awk '{print $1}'
    return 0
  fi
  "$PYTHON" -B "$STATIC_CHECKER" inventory-fingerprint
}

assert_scratch_quiet() {
  local current
  current="$(current_scratch_digest)"
  [[ "$current" =~ ^[0-9a-f]{64}$ ]] ||
    die "scratch fingerprint checker returned an invalid digest"
  [[ "$current" == "$SCRATCH_DIGEST" ]] ||
    die "scratch Lean universe drifted; no stage evidence was accepted"
}

assert_inventory_quiet() {
  local current
  current="$(current_inventory_digest)"
  [[ "$current" =~ ^[0-9a-f]{64}$ ]] ||
    die "inventory fingerprint checker returned an invalid digest"
  [[ "$current" == "$INVENTORY_DIGEST" ]] ||
    die "Verification inventory evidence drifted; no stage evidence was accepted"
}

compute_toolchain_sha() {
  {
    find "$SCRIPT_DIR" -maxdepth 1 -type f \
      \( -name '*.py' -o -name '*.sh' \) -print
    printf '%s\n' "$PROJECT_ROOT/scripts/audit_docstrings.py"
  } |
    LC_ALL=C sort |
    while IFS= read -r tool; do
      require_file "$tool"
      shasum -a 256 "$tool"
    done |
    shasum -a 256 | awk '{print $1}'
}

python_identity() {
  "$PYTHON" -B -c \
    'import hashlib, pathlib, platform, sys; p = pathlib.Path(sys.executable).resolve(strict=True); print(f"{p}\t{platform.python_version()}\t{hashlib.sha256(p.read_bytes()).hexdigest()}")'
}

compute_config_digest() {
  {
    printf 'python_request=%s\n' "$PYTHON"
    printf 'python_identity=%s\n' "$(python_identity)"
    printf 'source_manifest=%s\n' "$(canonical_path "$SOURCE_MANIFEST")"
    printf 'auto_implicit_log=%s\n' "$(canonical_path "$AUTO_IMPLICIT_LOG")"
    printf 'v5_instance_log=%s\n' "$(canonical_path "$V5_INSTANCE_LOG")"
    printf 'v5_scratch_json=%s\n' "$(canonical_path "$V5_SCRATCH_JSON")"
    printf 'v5_scratch_tsv=%s\n' "$(canonical_path "$V5_SCRATCH_TSV")"
    printf 'v5_scratch_summary=%s\n' \
      "$(canonical_path "$V5_SCRATCH_SUMMARY")"
    printf 'v5_scratch_inventory=%s\n' \
      "$(canonical_path "$V5_SCRATCH_INVENTORY")"
    printf 'v8_log=%s\n' "$(canonical_path "$V8_LOG")"
    printf 'v8_json=%s\n' "$(canonical_path "$V8_JSON")"
    printf 'v9_axiom_log=%s\n' "$(canonical_path "$V9_AXIOM_LOG")"
    printf 'v9_axiom_tsv=%s\n' "$(canonical_path "$V9_AXIOM_TSV")"
    printf 'v9_axiom_summary=%s\n' \
      "$(canonical_path "$V9_AXIOM_SUMMARY")"
    printf 'v10_planted_log=%s\n' "$(canonical_path "$V10_PLANTED_LOG")"
    printf 'v10_harness_log=%s\n' "$(canonical_path "$V10_HARNESS_LOG")"
    printf 'v10_appendix_witness_log=%s\n' \
      "$(canonical_path "$V10_APPENDIX_WITNESS_LOG")"
    printf 'v10_summary=%s\n' "$(canonical_path "$V10_SUMMARY")"
    printf 'v10_check=%s\n' "$(canonical_path "$V10_CHECK")"
  } | shasum -a 256 | awk '{print $1}'
}

assert_toolchain_quiet() {
  [[ "$(shasum -a 256 "$SCRIPT_PATH" | awk '{print $1}')" == \
      "$ORCHESTRATOR_SHA" ]] ||
    die "orchestrator changed during validation"
  [[ "$(shasum -a 256 "$STATIC_CHECKER" | awk '{print $1}')" == \
      "$CHECKER_SHA" ]] ||
    die "static checker changed during validation"
  [[ "$(compute_toolchain_sha)" == "$TOOLCHAIN_SHA" ]] ||
    die "audit toolchain changed during validation"
  [[ "$(compute_config_digest)" == "$CONFIG_DIGEST" ]] ||
    die "runtime evidence/Python configuration changed during validation"
}

assert_inputs_quiet() {
  assert_manifest_quiet
  assert_scratch_quiet
  assert_inventory_quiet
  assert_toolchain_quiet
}

initialize_after_manifest() {
  require_file "$SOURCE_MANIFEST"
  SOURCE_DIGEST="$(
    awk '/^# digest_of_digests: / {print $3; exit}' "$SOURCE_MANIFEST"
  )"
  [[ "$SOURCE_DIGEST" =~ ^[0-9a-f]{64}$ ]] ||
    die "source manifest has no valid digest_of_digests"
  SCRATCH_DIGEST="$(current_scratch_digest)"
  [[ "$SCRATCH_DIGEST" =~ ^[0-9a-f]{64}$ ]] ||
    die "scratch fingerprint checker returned an invalid digest"
  INVENTORY_DIGEST="$(current_inventory_digest)"
  [[ "$INVENTORY_DIGEST" =~ ^[0-9a-f]{64}$ ]] ||
    die "inventory fingerprint checker returned an invalid digest"
  ORCHESTRATOR_SHA="$(shasum -a 256 "$SCRIPT_PATH" | awk '{print $1}')"
  CHECKER_SHA="$(shasum -a 256 "$STATIC_CHECKER" | awk '{print $1}')"
  TOOLCHAIN_SHA="$(compute_toolchain_sha)"
  CONFIG_DIGEST="$(compute_config_digest)"
  PLAN_DIGEST="$(
    printf '%s\n%s\n%s\n%s\n%s\n%s\n%s\n' \
      "$STATE_SCHEMA" "$SCRATCH_DIGEST" "$INVENTORY_DIGEST" "$ORCHESTRATOR_SHA" \
      "$CHECKER_SHA" "$TOOLCHAIN_SHA" "$CONFIG_DIGEST" |
      shasum -a 256 | awk '{print $1}'
  )"
  STATE_DIR="$LOG_DIR/run_all_state/$SOURCE_DIGEST/$STATE_SCHEMA-$PLAN_DIGEST"
  mkdir -p -- "$STATE_DIR"
}

marker_value() {
  local marker="$1"
  local key="$2"
  awk -F= -v wanted="$key" '$1 == wanted {sub(/^[^=]*=/, ""); print; exit}' \
    "$marker"
}

validate_stage_marker() {
  local stage="$1"
  local marker="$STATE_DIR/$stage.done"
  require_file "$marker"

  [[ "$(marker_value "$marker" stage)" == "$stage" ]] ||
    die "$marker has the wrong stage"
  [[ "$(marker_value "$marker" source_digest)" == "$SOURCE_DIGEST" ]] ||
    die "$marker belongs to another source snapshot"
  [[ "$(marker_value "$marker" scratch_digest)" == "$SCRATCH_DIGEST" ]] ||
    die "$marker belongs to another scratch snapshot"
  [[ "$(marker_value "$marker" inventory_digest)" == "$INVENTORY_DIGEST" ]] ||
    die "$marker belongs to another V9 inventory snapshot"
  [[ "$(marker_value "$marker" state_schema)" == "$STATE_SCHEMA" ]] ||
    die "$marker belongs to another state schema"
  [[ "$(marker_value "$marker" orchestrator_sha256)" == "$ORCHESTRATOR_SHA" ]] ||
    die "$marker was produced by a different orchestrator"
  [[ "$(marker_value "$marker" checker_sha256)" == "$CHECKER_SHA" ]] ||
    die "$marker was produced by a different static checker"
  [[ "$(marker_value "$marker" toolchain_sha256)" == "$TOOLCHAIN_SHA" ]] ||
    die "$marker was produced by a different audit toolchain"
  [[ "$(marker_value "$marker" config_digest)" == "$CONFIG_DIGEST" ]] ||
    die "$marker was produced with different evidence/Python configuration"

  local stage_log evidence_manifest evidence_sha
  stage_log="$(marker_value "$marker" stage_log)"
  evidence_manifest="$(marker_value "$marker" evidence_manifest)"
  evidence_sha="$(marker_value "$marker" evidence_manifest_sha256)"
  require_text "$stage_log" "stage_exit: 0"
  require_file "$evidence_manifest"
  [[ "$(shasum -a 256 "$evidence_manifest" | awk '{print $1}')" == \
      "$evidence_sha" ]] ||
    die "$stage evidence manifest was modified: $evidence_manifest"
  shasum -a 256 -c "$evidence_manifest" >/dev/null ||
    die "$stage immutable evidence drifted: $stage"
}

write_evidence_manifest() {
  local attempt_dir="$1"
  local stage_log="$2"
  local destination="$attempt_dir/evidence.sha256"
  local initial_manifest="$attempt_dir/evidence.initial.sha256"
  require_file "$initial_manifest"
  : >"$destination"
  local path
  while IFS= read -r path; do
    [[ -n "$path" ]] || continue
    require_file "$path"
    shasum -a 256 "$path" >>"$destination"
  done <"$attempt_dir/evidence.paths"
  if ! cmp -s "$initial_manifest" "$destination"; then
    printf 'evidence_snapshot: DRIFT_DURING_VALIDATION\n' >>"$stage_log"
    die "stage evidence changed while it was being validated: $attempt_dir"
  fi
  printf 'evidence_snapshot: STABLE\n' >>"$stage_log"
  shasum -a 256 "$initial_manifest" >>"$destination"
  shasum -a 256 "$stage_log" >>"$destination"
  require_file "$destination"
}

run_stage() {
  local stage="$1"
  local function_name="$2"
  local marker="$STATE_DIR/$stage.done"

  assert_inputs_quiet
  if [[ -e "$marker" ]]; then
    validate_stage_marker "$stage"
    assert_inputs_quiet
    printf 'SKIP %s: immutable completion marker verified\n' "$stage"
    return 0
  fi

  local stage_lock="$STATE_DIR/$stage.lock"
  mkdir -- "$stage_lock" 2>/dev/null ||
    die "stage is already running or has a stale lock: $stage_lock"
  ACTIVE_STAGE_LOCK="$stage_lock"
  trap release_stage_lock EXIT INT TERM HUP

  assert_inputs_quiet
  if [[ -e "$marker" ]]; then
    validate_stage_marker "$stage"
    assert_inputs_quiet
    release_stage_lock
    trap - EXIT INT TERM HUP
    printf 'SKIP %s: completion marker appeared before lock acquisition\n' \
      "$stage"
    return 0
  fi

  local attempt_dir stage_log evidence_manifest evidence_sha rc
  attempt_dir="$(mktemp -d "$STATE_DIR/$stage.attempt.XXXXXX")"
  stage_log="$attempt_dir/stage.log"
  : >"$attempt_dir/evidence.paths"
  {
    printf 'stage: %s\n' "$stage"
    printf 'state_schema: %s\n' "$STATE_SCHEMA"
    printf 'source_digest: %s\n' "$SOURCE_DIGEST"
    printf 'scratch_digest: %s\n' "$SCRATCH_DIGEST"
    printf 'inventory_digest: %s\n' "$INVENTORY_DIGEST"
    printf 'orchestrator_sha256: %s\n' "$ORCHESTRATOR_SHA"
    printf 'checker_sha256: %s\n' "$CHECKER_SHA"
    printf 'toolchain_sha256: %s\n' "$TOOLCHAIN_SHA"
    printf 'config_digest: %s\n' "$CONFIG_DIGEST"
    printf 'attempt_dir: %s\n' "$attempt_dir"
    printf 'started_utc: %s\n\n' "$(date -u '+%Y-%m-%dT%H:%M:%SZ')"
  } >"$stage_log"
  : >"$attempt_dir/evidence.initial.sha256"

  set +e
  (
    set -e
    cd -- "$PROJECT_ROOT"
    "$function_name" "$attempt_dir"
  ) >>"$stage_log" 2>&1
  rc=$?
  set -e
  {
    printf '\nfinished_utc: %s\n' "$(date -u '+%Y-%m-%dT%H:%M:%SZ')"
    printf 'stage_exit: %s\n' "$rc"
  } >>"$stage_log"

  if [[ "$rc" != "0" ]]; then
    printf 'FAIL %s: preserved attempt log %s\n' "$stage" "$stage_log" >&2
    tail -n 40 "$stage_log" >&2
    release_stage_lock
    trap - EXIT INT TERM HUP
    return "$rc"
  fi

  assert_inputs_quiet
  write_evidence_manifest "$attempt_dir" "$stage_log"
  evidence_manifest="$attempt_dir/evidence.sha256"
  evidence_sha="$(shasum -a 256 "$evidence_manifest" | awk '{print $1}')"
  (
    set -o noclobber
    {
      printf 'stage=%s\n' "$stage"
      printf 'source_digest=%s\n' "$SOURCE_DIGEST"
      printf 'scratch_digest=%s\n' "$SCRATCH_DIGEST"
      printf 'inventory_digest=%s\n' "$INVENTORY_DIGEST"
      printf 'state_schema=%s\n' "$STATE_SCHEMA"
      printf 'orchestrator_sha256=%s\n' "$ORCHESTRATOR_SHA"
      printf 'checker_sha256=%s\n' "$CHECKER_SHA"
      printf 'toolchain_sha256=%s\n' "$TOOLCHAIN_SHA"
      printf 'config_digest=%s\n' "$CONFIG_DIGEST"
      printf 'stage_log=%s\n' "$stage_log"
      printf 'evidence_manifest=%s\n' "$evidence_manifest"
      printf 'evidence_manifest_sha256=%s\n' "$evidence_sha"
      printf 'completed_utc=%s\n' "$(date -u '+%Y-%m-%dT%H:%M:%SZ')"
    } >"$marker"
  ) || die "completion marker appeared concurrently: $marker"
  validate_stage_marker "$stage"
  assert_inputs_quiet
  release_stage_lock
  trap - EXIT INT TERM HUP
  printf 'PASS %s: marker=%s log=%s\n' "$stage" "$marker" "$stage_log"
}

stage_v1() {
  local attempt_dir="$1"
  local evidence=(
    "$SOURCE_MANIFEST"
    "$LOG_DIR/environment.txt"
    "$LOG_DIR/source_manifest_recertification_check.txt"
    "$LOG_DIR/final_clean_copy_manifest_reorganization.log"
    "$LOG_DIR/final_clean_copy_builddir_absence_reorganization.log"
    "$LOG_DIR/round10_docstring_delta.log"
    "$LOG_DIR/exercise_reorganization_delta.log"
    "$LOG_DIR/build_full_reorganization_clean.log"
    "$LOG_DIR/build_appendix_reorganization_clean.log"
    "$LOG_DIR/warning_inventory_recertification.log"
    "$LOG_DIR/v1_build_recertification_summary.log"
    "$VERIFY_DIR/01_build_integrity.md"
    "$HDP_DIR/APPENDIX_SUMMARY.md"
  )
  record_evidence "$attempt_dir" "${evidence[@]}"
  require_text "$LOG_DIR/source_manifest_recertification_check.txt" \
    "SOURCE MANIFEST OK"
  require_final_line "$LOG_DIR/final_clean_copy_manifest_reorganization.log" \
    "exit_code: 0"
  require_final_line "$LOG_DIR/final_clean_copy_builddir_absence_reorganization.log" \
    "exit_code: 0"
  require_text "$LOG_DIR/final_clean_copy_manifest_reorganization.log" \
    "$SOURCE_DIGEST"
  require_final_line "$LOG_DIR/round10_docstring_delta.log" "exit_code: 0"
  require_text "$LOG_DIR/exercise_reorganization_delta.log" \
    "EXERCISE_REORGANIZATION_DELTA: PASS"
  require_final_line "$LOG_DIR/exercise_reorganization_delta.log" "exit_code: 0"
  require_final_line "$LOG_DIR/build_full_reorganization_clean.log" "exit_code: 0"
  require_final_line "$LOG_DIR/build_appendix_reorganization_clean.log" "exit_code: 0"
  require_text "$LOG_DIR/v1_build_recertification_summary.log" \
    "v1_clean_build_gate: PASS"
  run_to_file "$attempt_dir/v1_validation.txt" \
    "$PYTHON" -B "$SCRIPT_DIR/v1_build_integrity.py"
  run_to_file "$attempt_dir/warning_inventory.txt" \
    "$PYTHON" -B "$SCRIPT_DIR/warning_inventory.py" \
    "$LOG_DIR/build_full_reorganization_clean.log" \
    "$LOG_DIR/build_appendix_reorganization_clean.log"
  cmp -s \
    "$attempt_dir/v1_validation.txt" \
    "$LOG_DIR/v1_build_recertification_summary.log" ||
    die "fresh V1 build summary differs from recertification evidence"
  cmp -s \
    "$attempt_dir/warning_inventory.txt" \
    "$LOG_DIR/warning_inventory_recertification.log" ||
    die "fresh V1 warning inventory differs from recertification evidence"
  record_evidence "$attempt_dir" \
    "$attempt_dir/v1_validation.txt" \
    "$attempt_dir/warning_inventory.txt"
  require_final_report "$VERIFY_DIR/01_build_integrity.md"
}

stage_v2() {
  local attempt_dir="$1"
  record_evidence "$attempt_dir" \
    "$LOG_DIR/recert_file_universe.txt" \
    "$LOG_DIR/recert_import_graph.txt" \
    "$LOG_DIR/recert_import_graph.json" \
    "$LOG_DIR/import_graph_recertification_calibration.log" \
    "$LOG_DIR/v2_orphan_recertification_summary.log" \
    "$VERIFY_DIR/02_import_graph.md"
  run_to_file "$attempt_dir/file_universe.txt" \
    "$PYTHON" -B "$SCRIPT_DIR/file_universe.py" --paths
  run_to_file "$attempt_dir/import_graph.txt" \
    "$PYTHON" -B "$SCRIPT_DIR/import_graph.py" \
    --expect-count "$EXPECTED_FILE_WALK_COUNT"
  run_to_file "$attempt_dir/import_graph.json" \
    "$PYTHON" -B "$SCRIPT_DIR/import_graph.py" --json \
    --expect-count "$EXPECTED_FILE_WALK_COUNT"
  run_to_file "$attempt_dir/orphan_summary.txt" \
    "$PYTHON" -B "$SCRIPT_DIR/v2_orphan_summary.py"
  run_to_file "$attempt_dir/import_graph_calibration.txt" \
    "$PYTHON" -B "$SCRIPT_DIR/test_import_graph.py"
  cmp -s "$attempt_dir/file_universe.txt" "$LOG_DIR/recert_file_universe.txt" ||
    die "fresh file universe differs from recertification evidence"
  cmp -s "$attempt_dir/import_graph.txt" "$LOG_DIR/recert_import_graph.txt" ||
    die "fresh V2 text graph differs from recertification evidence"
  cmp -s "$attempt_dir/import_graph.json" "$LOG_DIR/recert_import_graph.json" ||
    die "fresh V2 JSON graph differs from recertification evidence"
  cmp -s \
    "$attempt_dir/orphan_summary.txt" \
    "$LOG_DIR/v2_orphan_recertification_summary.log" ||
    die "fresh V2 orphan summary differs from recertification evidence"
  cmp -s \
    "$attempt_dir/import_graph_calibration.txt" \
    "$LOG_DIR/import_graph_recertification_calibration.log" ||
    die "fresh V2 calibration differs from recertification evidence"
  record_evidence "$attempt_dir" \
    "$attempt_dir/file_universe.txt" \
    "$attempt_dir/import_graph.txt" \
    "$attempt_dir/import_graph.json" \
    "$attempt_dir/orphan_summary.txt" \
    "$attempt_dir/import_graph_calibration.txt"
  require_final_report "$VERIFY_DIR/02_import_graph.md"
}

stage_v3() {
  local attempt_dir="$1"
  local project_forward sibling_forward live_forward
  project_forward="$PROJECT_ROOT/TranslationReport/forward_sorry_ledger.md"
  sibling_forward="$PROJECT_ROOT/../High_Dimensional_Probability/TranslationReport/forward_sorry_ledger.md"
  if [[ -f "$project_forward" && ! -f "$sibling_forward" ]]; then
    live_forward="$project_forward"
  elif [[ ! -f "$project_forward" && -f "$sibling_forward" ]]; then
    live_forward="$sibling_forward"
  else
    die "expected exactly one live forward-sorry ledger"
  fi
  record_evidence "$attempt_dir" \
    "$PROJECT_ROOT/.audit_work/verification/RecertV3V5ScannerPositive.lean" \
    "$PROJECT_ROOT/.audit_work/verification/RecertV3V5ScannerNoncode.lean" \
    "$LOG_DIR/recert_source_scanner_calibration.log" \
    "$LOG_DIR/recert_v3_calibration.json" \
    "$LOG_DIR/recert_v3_calibration_command.log" \
    "$LOG_DIR/recert_v3_library.json" \
    "$LOG_DIR/recert_v3_library.tsv" \
    "$LOG_DIR/recert_v3_library_json_command.log" \
    "$LOG_DIR/recert_v3_library_tsv_command.log" \
    "$LOG_DIR/recert_v3_direct_sorry_declarations.tsv" \
    "$LOG_DIR/recert_v3_direct_sorry_summary.txt" \
    "$LOG_DIR/recert_v3_direct_map_command.log" \
    "$LOG_DIR/recert_v3_forward_sorry_ledger_snapshot.md" \
    "$LOG_DIR/recert_v3_ledger_reconciliation.txt" \
    "$LOG_DIR/recert_v3_ledger_reconciliation_command.log" \
    "$LOG_DIR/recert_v3_ledger_reconciliation_selftest.log" \
    "$LOG_DIR/recert_v3_direct_sorry_declarations_kernel_join.tsv" \
    "$LOG_DIR/recert_v3_sorry_declarations.tsv" \
    "$LOG_DIR/recert_v3_v4_sorry_reconciliation.tsv" \
    "$LOG_DIR/recert_v3_v4_sorry_reconciliation.txt" \
    "$LOG_DIR/recert_v3_v4_reconciliation_command.log" \
    "$LOG_DIR/recert_v3_v4_reconciliation_selftest.log" \
    "$LOG_DIR/recert_axiom_audit.tsv" \
    "$LOG_DIR/recert_axiom_direct_dependencies.tsv" \
    "$VERIFY_DIR/inventory/exercise_leaf_declarations.tsv" \
    "$VERIFY_DIR/03_sorry_audit.md" \
    "$VERIFY_DIR/REVIEW_NOTES.md" \
    "$VERIFY_DIR/CORRECTION_LEDGER.md" \
    "$VERIFY_DIR/FINAL_CORRECTION_REPORT.md" \
    "$HDP_DIR/APPENDIX_SUMMARY.md" \
    "$live_forward"
  local completed_log
  for completed_log in \
      recert_source_scanner_calibration.log \
      recert_v3_calibration_command.log \
      recert_v3_library_json_command.log \
      recert_v3_library_tsv_command.log \
      recert_v3_direct_map_command.log \
      recert_v3_ledger_reconciliation_command.log \
      recert_v3_ledger_reconciliation_selftest.log \
      recert_v3_v4_reconciliation_command.log \
      recert_v3_v4_reconciliation_selftest.log; do
    require_final_line "$LOG_DIR/$completed_log" "exit_code: 0"
  done
  run_command "$PYTHON" -B "$SCRIPT_DIR/test_source_scanners.py"
  run_command "$PYTHON" -B "$SCRIPT_DIR/scan_v3_placeholders.py" \
    --scope library --format json --output "$attempt_dir/v3_library.json" \
    --fail-on-lex-diagnostic
  run_command "$PYTHON" -B "$SCRIPT_DIR/scan_v3_placeholders.py" \
    --scope library --format tsv --output "$attempt_dir/v3_library.tsv" \
    --fail-on-lex-diagnostic
  cmp -s "$attempt_dir/v3_library.json" "$LOG_DIR/recert_v3_library.json" ||
    die "fresh V3 JSON differs from recertification evidence"
  cmp -s "$attempt_dir/v3_library.tsv" "$LOG_DIR/recert_v3_library.tsv" ||
    die "fresh V3 TSV differs from recertification evidence"
  run_command "$PYTHON" -B "$SCRIPT_DIR/v3_direct_map.py" \
    --v3-json "$attempt_dir/v3_library.json" \
    --v3-tsv "$attempt_dir/v3_library.tsv" \
    --exercise-inventory "$VERIFY_DIR/inventory/exercise_leaf_declarations.tsv" \
    --direct-output "$attempt_dir/v3_direct.tsv" \
    --summary-output "$attempt_dir/v3_direct_summary.txt"
  cmp -s \
    "$attempt_dir/v3_direct.tsv" \
    "$LOG_DIR/recert_v3_direct_sorry_declarations.tsv" ||
    die "fresh V3 declaration map differs from recertification evidence"
  cmp -s \
    "$attempt_dir/v3_direct_summary.txt" \
    "$LOG_DIR/recert_v3_direct_sorry_summary.txt" ||
    die "fresh V3 declaration summary differs from recertification evidence"
  run_command "$PYTHON" -B "$SCRIPT_DIR/v3_ledger_reconciliation.py" \
    --self-test
  run_command "$PYTHON" -B "$SCRIPT_DIR/v3_ledger_reconciliation.py" \
    --v3-json "$attempt_dir/v3_library.json" \
    --output "$attempt_dir/v3_ledger_reconciliation.txt"
  grep -Fxq -- \
    "verdict: PASS" \
    "$attempt_dir/v3_ledger_reconciliation.txt" ||
    die "fresh V3 ledger reconciliation lacks exact PASS verdict"
  cmp -s \
    "$attempt_dir/v3_ledger_reconciliation.txt" \
    "$LOG_DIR/recert_v3_ledger_reconciliation.txt" ||
    die "fresh V3 ledger join differs from recertification evidence"
  run_command "$PYTHON" -B "$SCRIPT_DIR/v3_v4_reconcile.py" --self-test
  run_command "$PYTHON" -B "$SCRIPT_DIR/v3_v4_reconcile.py" \
    --v3-json "$attempt_dir/v3_library.json" \
    --v4-audit "$LOG_DIR/recert_axiom_audit.tsv" \
    --v4-dependencies "$LOG_DIR/recert_axiom_direct_dependencies.tsv" \
    --exercise-inventory "$VERIFY_DIR/inventory/exercise_leaf_declarations.tsv" \
    --direct-output "$attempt_dir/v3_kernel_direct.tsv" \
    --allowlist-output "$attempt_dir/v3_allowlist.tsv" \
    --reconciliation-output "$attempt_dir/v3_v4_reconciliation.tsv" \
    --summary-output "$attempt_dir/v3_v4_reconciliation.txt"
  cmp -s \
    "$attempt_dir/v3_kernel_direct.tsv" \
    "$LOG_DIR/recert_v3_direct_sorry_declarations_kernel_join.tsv" ||
    die "fresh V3/V4 direct set differs from recertification evidence"
  cmp -s \
    "$attempt_dir/v3_allowlist.tsv" \
    "$LOG_DIR/recert_v3_sorry_declarations.tsv" ||
    die "fresh V3/V4 allowlist differs from recertification evidence"
  cmp -s \
    "$attempt_dir/v3_v4_reconciliation.tsv" \
    "$LOG_DIR/recert_v3_v4_sorry_reconciliation.tsv" ||
    die "fresh V3/V4 rows differ from recertification evidence"
  cmp -s \
    "$attempt_dir/v3_v4_reconciliation.txt" \
    "$LOG_DIR/recert_v3_v4_sorry_reconciliation.txt" ||
    die "fresh V3/V4 summary differs from recertification evidence"
  record_evidence "$attempt_dir" \
    "$attempt_dir/v3_library.json" \
    "$attempt_dir/v3_library.tsv" \
    "$attempt_dir/v3_direct.tsv" \
    "$attempt_dir/v3_direct_summary.txt" \
    "$attempt_dir/v3_ledger_reconciliation.txt" \
    "$attempt_dir/v3_kernel_direct.tsv" \
    "$attempt_dir/v3_allowlist.tsv" \
    "$attempt_dir/v3_v4_reconciliation.tsv" \
    "$attempt_dir/v3_v4_reconciliation.txt"
  require_final_report "$VERIFY_DIR/03_sorry_audit.md"
}

stage_v4() {
  local attempt_dir="$1"
  record_evidence "$attempt_dir" \
    "$PROJECT_ROOT/.audit_work/verification/AxiomAuditShard0.lean" \
    "$PROJECT_ROOT/.audit_work/verification/AxiomAuditShard1.lean" \
    "$VERIFY_DIR/inventory/exercise_leaf_declarations.tsv" \
    "$LOG_DIR/recert_v4_shard0.log" \
    "$LOG_DIR/recert_v4_shard1.log" \
    "$LOG_DIR/recert_v4_merge_summary.json" \
    "$LOG_DIR/recert_axiom_audit_build.log" \
    "$LOG_DIR/recert_axiom_calibration.tsv" \
    "$LOG_DIR/recert_axiom_modules.txt" \
    "$LOG_DIR/recert_axiom_audit.tsv" \
    "$LOG_DIR/recert_axiom_declaration_types.tsv" \
    "$LOG_DIR/recert_axiom_declaration_binders.tsv" \
    "$LOG_DIR/recert_axiom_direct_dependencies.tsv" \
    "$LOG_DIR/recert_axiom_summary.txt" \
    "$LOG_DIR/recert_axiom_module_coverage.txt" \
    "$LOG_DIR/recert_axiom_exceedances.tsv" \
    "$LOG_DIR/recert_axiom_and_opaque_declarations.tsv" \
    "$LOG_DIR/round10_docstring_delta.log" \
    "$LOG_DIR/exercise_reorganization_delta.log" \
    "$LOG_DIR/recert_v3_sorry_declarations.tsv" \
    "$VERIFY_DIR/04_axiom_audit.md"
  run_command "$PYTHON" -B "$SCRIPT_DIR/axiom_audit.py" self-test
  run_command "$PYTHON" -B "$SCRIPT_DIR/axiom_audit.py" analyze \
    --v3-sorry-declarations "$LOG_DIR/recert_v3_sorry_declarations.tsv"
  require_final_line "$LOG_DIR/recert_axiom_audit_build.log" "exit_code: 0"
  require_text "$LOG_DIR/recert_axiom_summary.txt" "verdict: PASS"
  require_text "$LOG_DIR/recert_axiom_summary.txt" "module_coverage: PASS"
  require_text "$LOG_DIR/recert_axiom_summary.txt" "calibration: PASS"
  require_text "$LOG_DIR/recert_axiom_summary.txt" "v3_reconciliation: PASS"
  require_text "$LOG_DIR/recert_axiom_summary.txt" \
    "nonstandard_non_sorry_axiom_declarations: 0"
  require_text "$LOG_DIR/recert_axiom_summary.txt" \
    "unexpected_user_facing_opaque_declarations: 0"
  require_text "$LOG_DIR/round10_docstring_delta.log" \
    "ROUND10_DOCSTRING_DELTA: PASS"
  require_final_line "$LOG_DIR/round10_docstring_delta.log" "exit_code: 0"
  require_text "$LOG_DIR/exercise_reorganization_delta.log" \
    "EXERCISE_REORGANIZATION_DELTA: PASS"
  require_final_line "$LOG_DIR/exercise_reorganization_delta.log" "exit_code: 0"
  require_final_report "$VERIFY_DIR/04_axiom_audit.md"
}

stage_v5() {
  local attempt_dir="$1"
  record_evidence "$attempt_dir" \
    "$PROJECT_ROOT/.audit_work/verification/RecertV3V5ScannerPositive.lean" \
    "$PROJECT_ROOT/.audit_work/verification/RecertV3V5ScannerNoncode.lean" \
    "$PROJECT_ROOT/.audit_work/verification/RecertV5InstanceAudit.lean" \
    "$PROJECT_ROOT/.audit_work/verification/RecertV5AutoImplicitProbe.lean" \
    "$LOG_DIR/recert_source_scanner_calibration.log" \
    "$LOG_DIR/recert_v5_calibration.json" \
    "$LOG_DIR/recert_v5_calibration_command.log" \
    "$LOG_DIR/recert_v5_library.json" \
    "$LOG_DIR/recert_v5_library.tsv" \
    "$LOG_DIR/recert_v5_library_json_command.log" \
    "$LOG_DIR/recert_v5_library_tsv_command.log" \
    "$LOG_DIR/recert_v5_trust_surface_summary.txt" \
    "$LOG_DIR/recert_v5_trust_surface_command.log" \
    "$LOG_DIR/recert_v5_options.tsv" \
    "$LOG_DIR/recert_v5_global_instances.tsv" \
    "$LOG_DIR/recert_v5_all_instances.tsv" \
    "$LOG_DIR/recert_v5_reviewable_hits.tsv" \
    "$LOG_DIR/recert_v5_notation_shadow_search.log" \
    "$LOG_DIR/recert_v5_lakefile_autoimplicit_config.log" \
    "$LOG_DIR/recert_v5_scratch_birth_audit.log" \
    "$V5_SCRATCH_JSON" \
    "$V5_SCRATCH_TSV" \
    "$V5_SCRATCH_SUMMARY" \
    "$V5_SCRATCH_INVENTORY" \
    "$LOG_DIR/recert_v5_scratch_json_command.log" \
    "$LOG_DIR/recert_v5_scratch_tsv_command.log" \
    "$LOG_DIR/recert_v5_scratch_analysis_command.log" \
    "$V5_INSTANCE_LOG" \
    "$AUTO_IMPLICIT_LOG" \
    "$LOG_DIR/recert_axiom_and_opaque_declarations.tsv" \
    "$VERIFY_DIR/05_escape_hatches.md"
  local completed_log
  for completed_log in \
      recert_source_scanner_calibration.log \
      recert_v5_calibration_command.log \
      recert_v5_library_json_command.log \
      recert_v5_library_tsv_command.log \
      recert_v5_trust_surface_command.log \
      recert_v5_notation_shadow_search.log \
      recert_v5_lakefile_autoimplicit_config.log \
      recert_v5_scratch_birth_audit.log \
      recert_v5_scratch_json_command.log \
      recert_v5_scratch_tsv_command.log \
      recert_v5_scratch_analysis_command.log; do
    require_final_line "$LOG_DIR/$completed_log" "exit_code: 0"
  done
  run_command "$PYTHON" -B "$SCRIPT_DIR/test_source_scanners.py"
  run_command "$PYTHON" -B "$SCRIPT_DIR/scan_v5_escape_hatches.py" \
    --scope library --format json --output "$attempt_dir/v5_library.json" \
    --fail-on-lex-diagnostic
  run_command "$PYTHON" -B "$SCRIPT_DIR/scan_v5_escape_hatches.py" \
    --scope library --format tsv --output "$attempt_dir/v5_library.tsv" \
    --fail-on-lex-diagnostic
  run_command "$PYTHON" -B "$SCRIPT_DIR/scan_v5_escape_hatches.py" \
    --scope scratch --format json --output "$attempt_dir/v5_scratch.json" \
    --fail-on-lex-diagnostic
  run_command "$PYTHON" -B "$SCRIPT_DIR/scan_v5_escape_hatches.py" \
    --scope scratch --format tsv --output "$attempt_dir/v5_scratch.tsv" \
    --fail-on-lex-diagnostic
  run_command "$PYTHON" -B "$SCRIPT_DIR/v5_trust_surface.py" \
    --library-json "$attempt_dir/v5_library.json" \
    --library-tsv "$attempt_dir/v5_library.tsv" \
    --summary-output "$attempt_dir/v5_trust_summary.txt" \
    --options-output "$attempt_dir/v5_options.tsv" \
    --instances-output "$attempt_dir/v5_instances.tsv" \
    --all-instances-output "$attempt_dir/v5_all_instances.tsv" \
    --reviewable-output "$attempt_dir/v5_reviewable.tsv"
  run_command "$PYTHON" -B "$SCRIPT_DIR/v5_scratch_inventory.py" \
    --json "$attempt_dir/v5_scratch.json" \
    --tsv "$attempt_dir/v5_scratch.tsv" \
    --summary "$attempt_dir/v5_scratch_summary.txt" \
    --inventory "$attempt_dir/v5_scratch_inventory.tsv"
  cmp -s "$attempt_dir/v5_library.json" "$LOG_DIR/recert_v5_library.json" ||
    die "fresh V5 library JSON differs from recertification evidence"
  cmp -s "$attempt_dir/v5_library.tsv" "$LOG_DIR/recert_v5_library.tsv" ||
    die "fresh V5 library TSV differs from recertification evidence"
  cmp -s "$attempt_dir/v5_scratch.json" "$V5_SCRATCH_JSON" ||
    die "fresh V5 scratch JSON differs from final recertification evidence"
  cmp -s "$attempt_dir/v5_scratch.tsv" "$V5_SCRATCH_TSV" ||
    die "fresh V5 scratch TSV differs from final recertification evidence"
  cmp -s \
    "$attempt_dir/v5_trust_summary.txt" \
    "$LOG_DIR/recert_v5_trust_surface_summary.txt" ||
    die "fresh V5 trust summary differs from recertification evidence"
  cmp -s "$attempt_dir/v5_options.tsv" "$LOG_DIR/recert_v5_options.tsv" ||
    die "fresh V5 option inventory differs from recertification evidence"
  cmp -s \
    "$attempt_dir/v5_instances.tsv" \
    "$LOG_DIR/recert_v5_global_instances.tsv" ||
    die "fresh V5 global-instance inventory differs from recertification evidence"
  cmp -s \
    "$attempt_dir/v5_all_instances.tsv" \
    "$LOG_DIR/recert_v5_all_instances.tsv" ||
    die "fresh V5 all-instance inventory differs from recertification evidence"
  cmp -s \
    "$attempt_dir/v5_reviewable.tsv" \
    "$LOG_DIR/recert_v5_reviewable_hits.tsv" ||
    die "fresh V5 reviewable inventory differs from recertification evidence"
  cmp -s "$attempt_dir/v5_scratch_summary.txt" "$V5_SCRATCH_SUMMARY" ||
    die "fresh V5 scratch summary differs from recertification evidence"
  cmp -s "$attempt_dir/v5_scratch_inventory.tsv" "$V5_SCRATCH_INVENTORY" ||
    die "fresh V5 scratch inventory differs from recertification evidence"
  require_final_line "$V5_INSTANCE_LOG" "exit_code: 0"
  require_final_line "$AUTO_IMPLICIT_LOG" "exit_code: 0"
  require_text "$V5_SCRATCH_SUMMARY" "verdict: PASS"
  record_evidence "$attempt_dir" \
    "$attempt_dir/v5_library.json" \
    "$attempt_dir/v5_library.tsv" \
    "$attempt_dir/v5_scratch.json" \
    "$attempt_dir/v5_scratch.tsv" \
    "$attempt_dir/v5_trust_summary.txt" \
    "$attempt_dir/v5_options.tsv" \
    "$attempt_dir/v5_instances.tsv" \
    "$attempt_dir/v5_all_instances.tsv" \
    "$attempt_dir/v5_reviewable.tsv" \
    "$attempt_dir/v5_scratch_summary.txt" \
    "$attempt_dir/v5_scratch_inventory.tsv"
  require_final_report "$VERIFY_DIR/05_escape_hatches.md"
}

stage_v8() {
  local attempt_dir="$1"
  record_evidence "$attempt_dir" \
    "$PROJECT_ROOT/.audit_work/verification/V8PackageLintRecertification.lean" \
    "$V8_LOG" \
    "$V8_JSON" \
    "$LOG_DIR/recert_v8_package_lint_driver.log" \
    "$LOG_DIR/recert_v8_package_lint_summary.txt" \
    "$LOG_DIR/recert_v8_package_lint_summary_command.log" \
    "$LOG_DIR/recert_v8_package_lint.tsv" \
    "$LOG_DIR/recert_v8_package_lint_tsv_command.log" \
    "$LOG_DIR/recert_v8_dry_run.log" \
    "$LOG_DIR/recert_v8_dry_run_command.log" \
    "$LOG_DIR/recert_v8_tests.log" \
    "$LOG_DIR/v2_orphan_recertification_summary.log" \
    "$VERIFY_DIR/07_definition_sanity.md" \
    "$VERIFY_DIR/08_linter_report.md"
  require_final_line "$LOG_DIR/recert_v8_tests.log" "exit_code: 0"
  require_final_line "$LOG_DIR/recert_v8_dry_run_command.log" "exit_code: 0"
  require_final_line "$V8_LOG" "exit_code: 1"
  require_final_line "$LOG_DIR/recert_v8_package_lint_driver.log" "exit_code: 0"
  require_final_line \
    "$LOG_DIR/recert_v8_package_lint_summary_command.log" "exit_code: 0"
  require_final_line \
    "$LOG_DIR/recert_v8_package_lint_tsv_command.log" "exit_code: 0"
  run_command "$PYTHON" -B "$SCRIPT_DIR/test_v8_package_lint.py"
  run_to_file "$attempt_dir/v8_dry_run.txt" \
    "$PYTHON" -B "$SCRIPT_DIR/run_v8_package_lint.py" \
    --dry-run --log "$V8_LOG" --report "$V8_JSON"
  cmp -s "$attempt_dir/v8_dry_run.txt" "$LOG_DIR/recert_v8_dry_run.log" ||
    die "fresh V8 dry-run command differs from recertification evidence"
  run_command "$PYTHON" -B -c \
    'import json, pathlib, sys; p=json.loads(pathlib.Path(sys.argv[1]).read_text()); assert p["coverage_complete"] is True; assert p["coverage_status"] == "COMPLETE"; assert p["overall_status"] == "PASS"; assert not p["diagnostics"]' \
    "$V8_JSON"
  run_command "$PYTHON" -B "$SCRIPT_DIR/v8_lint_parser.py" \
    "$V8_LOG" --format text \
    --output "$attempt_dir/v8_package_lint_summary.txt"
  run_command "$PYTHON" -B "$SCRIPT_DIR/v8_lint_parser.py" \
    "$V8_LOG" --format tsv \
    --output "$attempt_dir/v8_package_lint.tsv"
  cmp -s \
    "$attempt_dir/v8_package_lint_summary.txt" \
    "$LOG_DIR/recert_v8_package_lint_summary.txt" ||
    die "fresh V8 text summary differs from recertification evidence"
  cmp -s \
    "$attempt_dir/v8_package_lint.tsv" \
    "$LOG_DIR/recert_v8_package_lint.tsv" ||
    die "fresh V8 hit inventory differs from recertification evidence"
  require_final_report "$VERIFY_DIR/07_definition_sanity.md"
  require_final_report "$VERIFY_DIR/08_linter_report.md"
  record_evidence "$attempt_dir" \
    "$attempt_dir/v8_dry_run.txt" \
    "$attempt_dir/v8_package_lint_summary.txt" \
    "$attempt_dir/v8_package_lint.tsv"
}

stage_v9() {
  local attempt_dir="$1"
  record_evidence "$attempt_dir" \
    "$VERIFY_DIR/inventory/readme_correspondence.tsv" \
    "$VERIFY_DIR/inventory/review_census_838.tsv" \
    "$VERIFY_DIR/inventory/review_census_835.tsv" \
    "$VERIFY_DIR/inventory/review_census_835.json" \
    "$REVIEW_DIR/recert_v9_documentation_census.tsv" \
    "$REVIEW_DIR/recert_v9_documentation_census_summary.txt" \
    "$LOG_DIR/recert_v9_docstring_audit.log" \
    "$LOG_DIR/recert_v9_docstring_audit_command.log" \
    "$LOG_DIR/recert_v9_documentation_census_generate.log" \
    "$LOG_DIR/recert_v9_documentation_census_check.log" \
    "$LOG_DIR/recert_v9_matrix_concentration_scope.log" \
    "$LOG_DIR/recert_v9_matrix_concentration_scope_command.log" \
    "$LOG_DIR/recert_v9_readme_axioms_selftest.log" \
    "$LOG_DIR/recert_v9_readme_axioms_selftest_command.log" \
    "$LOG_DIR/recert_v9_readme_axioms_driver.log" \
    "$LOG_DIR/recert_v9_readme_axioms_check_only.log" \
    "$LOG_DIR/recert_v9_toolchain_check.log" \
    "$LOG_DIR/recert_v9_source_manifest_check.log" \
    "$LOG_DIR/recert_v9_report_validation.log" \
    "$LOG_DIR/recert_v9_root_readme_build_command.log" \
    "$LOG_DIR/recert_v9_main_readme_single_file_command.log" \
    "$V9_AXIOM_LOG" \
    "$V9_AXIOM_TSV" \
    "$V9_AXIOM_SUMMARY" \
    "$PROJECT_ROOT/.audit_work/verification/V9READMEProvedAxiomsRecertification.lean" \
    "$LOG_DIR/v1_build_recertification_summary.log" \
    "$LOG_DIR/v2_orphan_recertification_summary.log" \
    "$LOG_DIR/recert_v3_direct_sorry_summary.txt" \
    "$LOG_DIR/recert_axiom_audit.tsv" \
    "$LOG_DIR/recert_axiom_summary.txt" \
    "$LOG_DIR/build_appendix_recertification.log" \
    "$PROJECT_ROOT/lakefile.toml" \
    "$VERIFY_DIR/09_readme_claims.md" \
    "$PROJECT_ROOT/README.md" \
    "$HDP_DIR/README.md" \
    "$VERIFY_DIR/REVIEW_NOTES.md" \
    "$VERIFY_DIR/archive/FAITHFUL_PROOFREAD_REPORT.md" \
    "$VERIFY_DIR/CORRECTION_LEDGER.md" \
    "$HDP_DIR/APPENDIX_SUMMARY.md" \
    "$VERIFY_DIR/FINAL_CORRECTION_REPORT.md"
  run_to_file "$attempt_dir/docstring_audit.txt" \
    "$PYTHON" -B "$PROJECT_ROOT/scripts/audit_docstrings.py" --check
  cmp -s \
    "$attempt_dir/docstring_audit.txt" \
    "$LOG_DIR/recert_v9_docstring_audit.log" ||
    die "fresh V9 docstring audit differs from recertification evidence"
  require_final_line "$LOG_DIR/recert_v9_documentation_census_generate.log" \
    "exit_code: 0"
  require_final_line "$LOG_DIR/recert_v9_documentation_census_check.log" \
    "exit_code: 0"
  require_final_line "$LOG_DIR/recert_v9_root_readme_build_command.log" \
    "exit_code: 0"
  require_final_line "$LOG_DIR/recert_v9_main_readme_single_file_command.log" \
    "exit_code: 0"
  require_final_line "$LOG_DIR/recert_v9_docstring_audit_command.log" \
    "exit_code: 0"
  require_final_line "$LOG_DIR/recert_v9_matrix_concentration_scope_command.log" \
    "exit_code: 0"
  require_final_line "$LOG_DIR/recert_v9_readme_axioms_selftest_command.log" \
    "exit_code: 0"
  require_final_line "$LOG_DIR/recert_v9_readme_axioms_driver.log" \
    "exit_code: 0"
  require_final_line "$LOG_DIR/recert_v9_readme_axioms_check_only.log" \
    "exit_code: 0"
  require_final_line "$LOG_DIR/recert_v9_toolchain_check.log" \
    "exit_code: 0"
  require_final_line "$LOG_DIR/recert_v9_source_manifest_check.log" \
    "exit_code: 0"
  require_final_line "$LOG_DIR/recert_v9_report_validation.log" \
    "exit_code: 0"
  require_text "$LOG_DIR/recert_v9_report_validation.log" \
    "v9_report_gate: PASS"
  require_text "$LOG_DIR/recert_v9_toolchain_check.log" \
    "toolchain_pin_gate: PASS"
  run_command "$PYTHON" -B "$SCRIPT_DIR/v9_documentation_census.py" --check
  run_command "$PYTHON" -B "$SCRIPT_DIR/verify_readme_axioms.py" --self-test
  run_command "$PYTHON" -B "$SCRIPT_DIR/verify_readme_axioms.py" \
    --check-only \
    --raw-log "$V9_AXIOM_LOG" \
    --results "$V9_AXIOM_TSV" \
    --summary "$V9_AXIOM_SUMMARY"
  run_to_file "$attempt_dir/matrix_concentration_scope.txt" \
    "$PYTHON" -B "$SCRIPT_DIR/v9_matrix_concentration_scope.py"
  cmp -s \
    "$attempt_dir/matrix_concentration_scope.txt" \
    "$LOG_DIR/recert_v9_matrix_concentration_scope.log" ||
    die "fresh V9 MatrixConcentration scope differs from recertification evidence"
  require_final_line "$V9_AXIOM_LOG" "exit_code: 0"
  require_text "$V9_AXIOM_SUMMARY" "verdict: PASS"
  record_evidence "$attempt_dir" \
    "$attempt_dir/docstring_audit.txt" \
    "$attempt_dir/matrix_concentration_scope.txt"
  require_final_report "$VERIFY_DIR/09_readme_claims.md"
}

stage_v10() {
  local attempt_dir="$1"
  record_evidence "$attempt_dir" \
    "$PROJECT_ROOT/.audit_work/verification/V10ConditionalInterfaces.lean" \
    "$PROJECT_ROOT/.audit_work/verification/v10_conditional_positive.lean" \
    "$LOG_DIR/recert_v6_tier_b_endpoints.tsv" \
    "$LOG_DIR/recert_v6_tier_b_endpoint_exclusions.tsv" \
    "$LOG_DIR/recert_v6_tier_b_endpoint_summary.txt" \
    "$LOG_DIR/recert_definition_constants.tsv" \
    "$LOG_DIR/recert_definition_dependency_edges.tsv" \
    "$LOG_DIR/recert_definition_reverse_citations.tsv" \
    "$LOG_DIR/recert_definition_dead_code_sweep.tsv" \
    "$LOG_DIR/recert_definition_modules.txt" \
    "$LOG_DIR/recert_definition_module_coverage.txt" \
    "$LOG_DIR/recert_definition_sanity_summary.txt" \
    "$REVIEW_DIR/v6_tier_b_ch0_4.tsv" \
    "$REVIEW_DIR/v6_tier_b_ch5_7.tsv" \
    "$REVIEW_DIR/v6_tier_b_ch8_9.tsv" \
    "$REVIEW_DIR/v6_tier_b_supplement_ch0_4.tsv" \
    "$REVIEW_DIR/v6_tier_b_supplement_ch5_7.tsv" \
    "$REVIEW_DIR/v6_tier_b_supplement_ch8_9.tsv" \
    "$LOG_DIR/v10_environment_modules.txt" \
    "$LOG_DIR/v10_environment_candidates.tsv" \
    "$LOG_DIR/v10_environment_references.tsv" \
    "$LOG_DIR/v10_environment_inline_binders.tsv" \
    "$VERIFY_DIR/inventory/v10_textual_predicates.tsv" \
    "$VERIFY_DIR/inventory/v10_environment_predicates.tsv" \
    "$VERIFY_DIR/inventory/v10_environment_text_diff.tsv" \
    "$VERIFY_DIR/inventory/v10_predicate_census.tsv" \
    "$VERIFY_DIR/inventory/v10_consumers.tsv" \
    "$VERIFY_DIR/inventory/v10_inline_hypotheses.tsv" \
    "$REVIEW_DIR/v10_adjudication.tsv" \
    "$REVIEW_DIR/v10_ledger_reconciliation.tsv" \
    "$REVIEW_DIR/v10_v7_dead_reconciliation.tsv" \
    "$REVIEW_DIR/v10_primary_review_closure.tsv" \
    "$REVIEW_DIR/v10_inline_review_closure.tsv" \
    "$REVIEW_DIR/v10_v6_review_reconciliation.tsv" \
    "$LOG_DIR/v10_calibration.tsv" \
    "$LOG_DIR/v10_review_closure.txt" \
    "$V10_PLANTED_LOG" \
    "$V10_HARNESS_LOG" \
    "$V10_APPENDIX_WITNESS_LOG" \
    "$V10_SUMMARY" \
    "$LOG_DIR/v10_source_state.txt" \
    "$LOG_DIR/v10_command.log" \
    "$LOG_DIR/v10_self_test.log" \
    "$LOG_DIR/v10_source_preview.log" \
    "$V10_CHECK" \
    "$VERIFY_DIR/10_conditional_interfaces.md"
  run_command "$PYTHON" -B \
    "$SCRIPT_DIR/v10_conditional_interfaces.py" self-test
  run_command "$PYTHON" -B \
    "$SCRIPT_DIR/v10_conditional_interfaces.py" source-preview
  run_command "$PYTHON" -B \
    "$SCRIPT_DIR/v10_conditional_interfaces.py" check
  require_final_line "$V10_PLANTED_LOG" "exit_status: 0"
  require_final_line "$V10_HARNESS_LOG" "exit_status: 0"
  require_final_line "$V10_APPENDIX_WITNESS_LOG" "exit_status: 0"
  require_text "$V10_SUMMARY" "verdict: PASS-WITH-NOTES"
  require_text "$V10_CHECK" "V10 evidence check: PASS"
  require_final_report "$VERIFY_DIR/10_conditional_interfaces.md"
}

stage_consistency() {
  local attempt_dir="$1"
  local reports=(
    "$VERIFY_DIR/README.md"
    "$VERIFY_DIR/01_build_integrity.md"
    "$VERIFY_DIR/02_import_graph.md"
    "$VERIFY_DIR/03_sorry_audit.md"
    "$VERIFY_DIR/04_axiom_audit.md"
    "$VERIFY_DIR/05_escape_hatches.md"
    "$VERIFY_DIR/06_vacuity_triviality.md"
    "$VERIFY_DIR/07_definition_sanity.md"
    "$VERIFY_DIR/08_linter_report.md"
    "$VERIFY_DIR/09_readme_claims.md"
    "$VERIFY_DIR/10_conditional_interfaces.md"
  )
  local report report_index
  require_no_completion_placeholder "${reports[0]}"
  for ((report_index = 1; report_index < ${#reports[@]}; report_index++)); do
    report="${reports[$report_index]}"
    require_final_report "$report"
  done
  require_final_line "$LOG_DIR/recert_run_all_selftest.log" "exit_code: 0"
  require_text "$LOG_DIR/recert_run_all_selftest.log" \
    "PASS run_all self-test:"
  record_evidence "$attempt_dir" \
    "${reports[@]}" \
    "$LOG_DIR/recert_run_all_selftest.log" \
    "$SCRIPT_DIR/check_v6_final.py" \
    "$REVIEW_DIR/recert_v6_tier_c.tsv" \
    "$REVIEW_DIR/recert_v6_tier_c_summary.txt" \
    "$REVIEW_DIR/recert_v6_tier_c_seeded_population.tsv" \
    "$REVIEW_DIR/recert_v6_tier_c_seeded_frame.tsv" \
    "$REVIEW_DIR/recert_v6_tier_c_seeded_sample.tsv" \
    "$REVIEW_DIR/recert_v6_tier_c_seeded_sample_summary.txt" \
    "$LOG_DIR/recert_v6_tier_c_seeded_sample_build.log" \
    "$LOG_DIR/recert_v6_tier_c_ch0_4_build.log" \
    "$LOG_DIR/recert_v6_tier_c_ch0_4_axiom_build.log" \
    "$LOG_DIR/recert_v6_tier_c_ch0_4_axioms.tsv" \
    "$LOG_DIR/recert_v6_tier_c_ch5_7_build.log" \
    "$LOG_DIR/recert_v6_tier_c_ch5_7_axioms.log" \
    "$LOG_DIR/recert_v6_tier_c_ch8_9_build.log" \
    "$LOG_DIR/recert_v6_tier_c_ch8_9_axioms.log" \
    "$LOG_DIR/recert_v6_tier_c_planted_bad.log" \
    "$LOG_DIR/recert_v6_tier_c_command.log" \
    "$LOG_DIR/recert_v6_tier_c_check.log" \
    "$LOG_DIR/recert_v6_final_self_test.log" \
    "$LOG_DIR/recert_v6_final_check.log" \
    "$LOG_DIR/round10_docstring_delta.log" \
    "$LOG_DIR/exercise_reorganization_delta.log"
  require_text "$LOG_DIR/exercise_reorganization_delta.log" \
    "EXERCISE_REORGANIZATION_DELTA: PASS"
  require_final_line "$LOG_DIR/exercise_reorganization_delta.log" "exit_code: 0"
  run_to_file "$attempt_dir/v6_final_self_test.txt" \
    "$PYTHON" -B "$SCRIPT_DIR/check_v6_final.py" --self-test
  cmp -s \
    "$attempt_dir/v6_final_self_test.txt" \
    "$LOG_DIR/recert_v6_final_self_test.log" ||
    die "fresh V6 checker self-test differs from recertification evidence"
  run_to_file "$attempt_dir/v6_final_check.txt" \
    "$PYTHON" -B "$SCRIPT_DIR/check_v6_final.py"
  cmp -s \
    "$attempt_dir/v6_final_check.txt" \
    "$LOG_DIR/recert_v6_final_check.log" ||
    die "fresh V6 final check differs from recertification evidence"
  run_to_file "$attempt_dir/reorganization_layout.txt" \
    "$PYTHON" -B "$SCRIPT_DIR/verify_reorganization_layout.py"
  require_final_line \
    "$attempt_dir/reorganization_layout.txt" \
    "REORGANIZATION_LAYOUT: PASS"
  record_evidence "$attempt_dir" \
    "$attempt_dir/v6_final_self_test.txt" \
    "$attempt_dir/v6_final_check.txt" \
    "$SCRIPT_DIR/verify_reorganization_layout.py" \
    "$attempt_dir/reorganization_layout.txt"
  run_command "$PYTHON" -B "$SCRIPT_DIR/check_consistency.py" --self-test
  run_command "$PYTHON" -B "$SCRIPT_DIR/test_check_consistency.py"
  run_command "$PYTHON" -B "$SCRIPT_DIR/check_consistency.py" --no-log
}

stage_function() {
  case "$1" in
    01_v1_build_integrity) printf '%s\n' stage_v1 ;;
    02_v2_import_graph) printf '%s\n' stage_v2 ;;
    03_v3_placeholder_census) printf '%s\n' stage_v3 ;;
    04_v4_axiom_audit) printf '%s\n' stage_v4 ;;
    05_v5_escape_hatches) printf '%s\n' stage_v5 ;;
    08_v8_package_lint) printf '%s\n' stage_v8 ;;
    09_v9_published_claims) printf '%s\n' stage_v9 ;;
    10_v10_conditional_interfaces) printf '%s\n' stage_v10 ;;
    11_consistency) printf '%s\n' stage_consistency ;;
    *) die "unknown stage: $1" ;;
  esac
}

print_plan() {
  printf 'Manifest-first static machine plan\n'
  printf '  manifest: %s\n' "$SOURCE_MANIFEST"
  printf '  heavy evidence policy: validate/hash/reuse; never regenerate\n'
  printf '  scratch policy: path+content fingerprint in plan and markers\n'
  printf '  inventory policy: exact top-level Verification inventory fingerprint\n'
  printf '  concurrency policy: one exclusive lock per unfinished stage\n'
  printf '  runtime policy: Python identity and evidence overrides in plan\n'
  printf '  stages:\n'
  local stage
  for stage in "${STAGES[@]}"; do
    printf '    %s\n' "$stage"
  done
  printf '  final action: check_consistency.py --no-log\n'
}

print_status() {
  local stage marker
  assert_inputs_quiet
  printf 'state_dir: %s\n' "$STATE_DIR"
  for stage in "${STAGES[@]}"; do
    marker="$STATE_DIR/$stage.done"
    if [[ -e "$marker" ]]; then
      validate_stage_marker "$stage"
      assert_inputs_quiet
      printf 'COMPLETE %s\n' "$stage"
    else
      printf 'PENDING %s\n' "$stage"
    fi
  done
  assert_inputs_quiet
}

selftest_stage() {
  local attempt_dir="$1"
  printf 'self-test stage body\n'
  record_evidence "$attempt_dir" "$SELFTEST_EVIDENCE"
}

selftest_drift_stage() {
  local attempt_dir="$1"
  printf 'self-test drift stage body\n'
  record_evidence "$attempt_dir" "$SELFTEST_DRIFT_EVIDENCE"
  printf 'changed during stage validation\n' >>"$SELFTEST_DRIFT_EVIDENCE"
}

selftest_failure_stage() {
  local attempt_dir="$1"
  record_evidence "$attempt_dir" "$SELFTEST_FAILURE_EVIDENCE"
  /usr/bin/false
  printf 'failure was incorrectly masked\n'
}

cleanup_selftest() {
  local path="$1"
  case "$path" in
    "${TMPDIR:-/tmp}"/hdp-run-all-selftest.*)
      /bin/rm -rf -- "$path"
      ;;
    *)
      printf 'refusing unexpected self-test cleanup path: %s\n' "$path" >&2
      return 1
      ;;
  esac
}

self_test() {
  run_command /bin/bash -n "$SCRIPT_PATH"
  run_command "$PYTHON" -B -c \
    "compile(open('$STATIC_CHECKER', encoding='utf-8').read(), '$STATIC_CHECKER', 'exec')"
  local forbidden_build_ref='.lake'
  forbidden_build_ref+='/build'
  local forbidden_clean_helper='clean_build_once'
  forbidden_clean_helper+='.py'
  local forbidden_frozen_prefix='pass'
  forbidden_frozen_prefix+='07'
  if grep -Fq "$forbidden_build_ref" "$SCRIPT_PATH"; then
    die "self-test found a forbidden project build-directory deletion reference"
  fi
  if grep -Fq "$forbidden_clean_helper" "$SCRIPT_PATH"; then
    die "self-test found a forbidden second clean-build invocation"
  fi
  local frozen_reference_scan
  frozen_reference_scan="$(
    sed \
      "s/v10_${forbidden_frozen_prefix}_appendix_axioms_build\\.log//g" \
      "$SCRIPT_PATH"
  )"
  if grep -Fiq "$forbidden_frozen_prefix" <<<"$frozen_reference_scan"; then
    die "self-test found a forbidden frozen correction-pass evidence reference"
  fi

  local temporary
  temporary="$(mktemp -d "${TMPDIR:-/tmp}/hdp-run-all-selftest.XXXXXX")"
  trap 'cleanup_selftest "$temporary"' RETURN
  SELF_TEST_MODE=1
  SOURCE_DIGEST="$(printf 'f%.0s' {1..64})"
  SELFTEST_SCRATCH_DIR="$temporary/scratch"
  SELFTEST_INVENTORY_DIR="$temporary/inventory"
  mkdir -p "$SELFTEST_SCRATCH_DIR"
  mkdir -p "$SELFTEST_INVENTORY_DIR"
  printf 'scratch baseline\n' >"$SELFTEST_SCRATCH_DIR/baseline.lean"
  printf 'inventory baseline\n' >"$SELFTEST_INVENTORY_DIR/baseline.tsv"
  SCRATCH_DIGEST="$(current_scratch_digest)"
  INVENTORY_DIGEST="$(current_inventory_digest)"
  ORCHESTRATOR_SHA="$(shasum -a 256 "$SCRIPT_PATH" | awk '{print $1}')"
  CHECKER_SHA="$(shasum -a 256 "$STATIC_CHECKER" | awk '{print $1}')"
  TOOLCHAIN_SHA="$(compute_toolchain_sha)"
  CONFIG_DIGEST="$(compute_config_digest)"
  STATE_DIR="$temporary/state"
  mkdir -p "$STATE_DIR"
  SELFTEST_EVIDENCE="$temporary/input.txt"
  printf 'immutable input\n' >"$SELFTEST_EVIDENCE"

  local icon_junk_lock="$STATE_DIR/selftest_icon_junk.lock"
  mkdir "$icon_junk_lock"
  : >"$icon_junk_lock/Icon"$'\r'
  ACTIVE_STAGE_LOCK="$icon_junk_lock"
  release_stage_lock
  [[ ! -e "$icon_junk_lock" ]] ||
    die "Icon<CR> lock-junk cleanup calibration left its lock directory"

  run_stage "selftest_reentrant" selftest_stage
  local marker="$STATE_DIR/selftest_reentrant.done"
  validate_stage_marker "selftest_reentrant"
  local attempts_before attempts_after
  attempts_before="$(find "$STATE_DIR" -maxdepth 1 -type d \
    -name 'selftest_reentrant.attempt.*' | wc -l | tr -d ' ')"
  run_stage "selftest_reentrant" selftest_stage
  attempts_after="$(find "$STATE_DIR" -maxdepth 1 -type d \
    -name 'selftest_reentrant.attempt.*' | wc -l | tr -d ' ')"
  [[ "$attempts_before" == "$attempts_after" ]] ||
    die "re-entrant stage created a second attempt after completion"

  printf 'new scratch input\n' >"$SELFTEST_SCRATCH_DIR/added.lean"
  set +e
  (run_stage "selftest_reentrant" selftest_stage) >/dev/null 2>&1
  local scratch_rc=$?
  set -e
  [[ "$scratch_rc" != "0" ]] ||
    die "scratch-universe addition did not invalidate re-entry"
  /bin/rm -f -- "$SELFTEST_SCRATCH_DIR/added.lean"
  assert_scratch_quiet

  printf 'new inventory input\n' >"$SELFTEST_INVENTORY_DIR/added.tsv"
  set +e
  (run_stage "selftest_reentrant" selftest_stage) >/dev/null 2>&1
  local inventory_rc=$?
  set -e
  [[ "$inventory_rc" != "0" ]] ||
    die "inventory-universe addition did not invalidate re-entry"
  /bin/rm -f -- "$SELFTEST_INVENTORY_DIR/added.tsv"
  assert_inventory_quiet

  local saved_config="$CONFIG_DIGEST"
  CONFIG_DIGEST="$(printf '0%.0s' {1..64})"
  if (validate_stage_marker "selftest_reentrant") >/dev/null 2>&1; then
    die "runtime-configuration drift calibration was not rejected"
  fi
  CONFIG_DIGEST="$saved_config"

  printf 'tamper\n' >>"$SELFTEST_EVIDENCE"
  if (validate_stage_marker "selftest_reentrant") >/dev/null 2>&1; then
    die "immutable-evidence tamper calibration was not rejected"
  fi

  SELFTEST_DRIFT_EVIDENCE="$temporary/drift-input.txt"
  printf 'initial drift input\n' >"$SELFTEST_DRIFT_EVIDENCE"
  if (run_stage "selftest_drift" selftest_drift_stage) >/dev/null 2>&1; then
    die "within-stage evidence drift calibration was not rejected"
  fi
  [[ ! -e "$STATE_DIR/selftest_drift.done" ]] ||
    die "within-stage evidence drift produced a completion marker"

  SELFTEST_FAILURE_EVIDENCE="$temporary/failure-input.txt"
  printf 'failure input\n' >"$SELFTEST_FAILURE_EVIDENCE"
  set +e
  (run_stage "selftest_failure" selftest_failure_stage) >/dev/null 2>&1
  local failure_rc=$?
  set -e
  [[ "$failure_rc" != "0" ]] ||
    die "stage command failure was masked by a later command"
  [[ ! -e "$STATE_DIR/selftest_failure.done" ]] ||
    die "failed stage produced a completion marker"

  mkdir "$STATE_DIR/selftest_locked.lock"
  set +e
  (run_stage "selftest_locked" selftest_stage) >/dev/null 2>&1
  local lock_rc=$?
  set -e
  [[ "$lock_rc" != "0" ]] ||
    die "pre-existing stage lock did not reject concurrent execution"
  [[ ! -e "$STATE_DIR/selftest_locked.done" ]] ||
    die "locked stage produced a completion marker"
  /bin/rmdir "$STATE_DIR/selftest_locked.lock"

  local final_report="$temporary/final-report.md"
  printf '**Verdict: PASS**\n\nV8_FINAL_SECTION_TO_FILL\n' >"$final_report"
  if (require_final_report "$final_report") >/dev/null 2>&1; then
    die "TO_FILL final-report calibration was not rejected"
  fi
  printf '**Verdict: PASS**\n\n-DmaxSynthPendingDepth=3\n' >"$final_report"
  require_final_report "$final_report"
  printf '**Verdict: PASS**\n\nPENDING\n' >"$final_report"
  if (require_final_report "$final_report") >/dev/null 2>&1; then
    die "standalone PENDING final-report calibration was not rejected"
  fi
  printf '**Verdict: PASS**\n' >"$final_report"
  require_final_report "$final_report"
  printf '**Verdict: BANANA**\n' >"$final_report"
  if (require_final_report "$final_report") >/dev/null 2>&1; then
    die "unsupported final-report verdict calibration was not rejected"
  fi

  local final_line_evidence="$temporary/final-line.log"
  printf 'command: calibration\nexit_status: 0\n' >"$final_line_evidence"
  require_final_line "$final_line_evidence" "exit_status: 0"
  printf 'trailing output\n' >>"$final_line_evidence"
  if (require_final_line "$final_line_evidence" "exit_status: 0") \
      >/dev/null 2>&1; then
    die "exact-final-line calibration accepted trailing output"
  fi

  printf 'PASS run_all self-test: syntax, no clean deletion, no frozen correction-pass evidence except the current V10 Appendix witness replay, re-entry, scratch/inventory invalidation, config binding, stage lock, Icon<CR> lock-junk cleanup, failure propagation, placeholder-boundary/verdict rejection, exact-footer rejection, tamper rejection, within-stage drift rejection\n'
  cleanup_selftest "$temporary"
  trap - RETURN
}

main() {
  local action="${1:---run}"
  case "$action" in
    --self-test)
      [[ "$#" == "1" ]] ||
        die "--self-test takes no additional arguments"
      self_test
      return 0
      ;;
    --plan)
      [[ "$#" == "1" ]] ||
        die "--plan takes no additional arguments"
      print_plan
      return 0
      ;;
    --status)
      [[ "$#" == "1" ]] ||
        die "--status takes no additional arguments"
      ;;
    --run)
      if [[ "$#" == "1" ]]; then
        :
      elif [[ "$#" == "3" && "$2" == "--stop-after" ]]; then
        STOP_AFTER="$3"
        local stop_is_valid=0
        local candidate
        for candidate in "${STAGES[@]}"; do
          if [[ "$candidate" == "$STOP_AFTER" ]]; then
            stop_is_valid=1
            break
          fi
        done
        [[ "$stop_is_valid" == "1" ]] ||
          die "unknown --stop-after stage: $STOP_AFTER"
      else
        die "usage: run_all.sh --run [--stop-after STAGE]"
      fi
      ;;
    *)
      die "usage: run_all.sh [--run [--stop-after STAGE]|--status|--plan|--self-test]"
      ;;
  esac

  # Hard gate: no state directory, log, or marker is created before this
  # succeeds.
  manifest_check
  initialize_after_manifest

  if [[ "$action" == "--status" ]]; then
    print_status
    return 0
  fi

  local stage function_name
  for stage in "${STAGES[@]}"; do
    function_name="$(stage_function "$stage")"
    run_stage "$stage" "$function_name"
    if [[ -n "$STOP_AFTER" && "$stage" == "$STOP_AFTER" ]]; then
      assert_inputs_quiet
      printf 'STOP_AFTER reached: %s\n' "$stage"
      return 0
    fi
  done
  assert_inputs_quiet
  print_status
  printf 'RUN_ALL_COMPLETE source_digest=%s state_dir=%s\n' \
    "$SOURCE_DIGEST" "$STATE_DIR"
}

main "$@"
