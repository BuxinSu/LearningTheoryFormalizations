#!/usr/bin/env bash
# Reconstruct V1 clean-build evidence in a never-before-used root-package
# build directory.  This never deletes or writes `.lake/build`.

set -euo pipefail

SCRIPT_DIR="$(cd "$(dirname "${BASH_SOURCE[0]}")" && pwd)"
VERIFY="$(cd "$SCRIPT_DIR/.." && pwd)"
ROOT="$(cd "$VERIFY/../.." && pwd)"
LOGS="$VERIFY/logs"
WORK="$ROOT/.audit_work"
LAKE="$HOME/.elan/bin/lake"
CONFIG="$SCRIPT_DIR/v1_recovery_lakefile.toml"
RECOVERY_BUILD="$WORK/v1_recertification_recovery_build_v7"
DONE_MARKER="$WORK/v1_recovery_build.done"
BUILD_LOG="$LOGS/build_full.recertification-empty-recovery.log"
STATUS_LOG="$LOGS/build_full.recertification-empty-recovery.status.log"
REUSE_STATUS_LOG="$LOGS/v1_recovery_reuse_status.log"
MANIFEST_LOG="$LOGS/v1_recovery_manifest_check.log"
CONFIG_CHECK_LOG="$LOGS/v1_recovery_config_check.log"
CANONICAL_BEFORE="$LOGS/v1_canonical_build_before.tsv"
CANONICAL_AFTER="$LOGS/v1_canonical_build_after.tsv"
RECOVERY_TREE="$LOGS/v1_recovery_build_tree.tsv"
CACHE_LOG="$LOGS/cache_get.recertification-empty-recovery.log"
RECERT_START="$WORK/v1_recert_build_delete_started.marker"
RECERT_DELETED="$WORK/v1_recert_build_deleted.marker"
RECERT_DELETE_LOG="$LOGS/build_delete_once.recertification.log"
LOCK_FILE="$WORK/verification.run.lock"
FINALIZATION_GUARD="$WORK/verification.finalization.guard"
COORDINATION="$SCRIPT_DIR/verification_coordination.sh"
for directory in "$LOGS" "$WORK"; do
  if [[ -L "$directory" || ( -e "$directory" && ! -d "$directory" ) ]]; then
    echo "verification path is not a real directory: $directory" >&2
    exit 1
  fi
done
if [[ -L "$DONE_MARKER" ||
      (-e "$DONE_MARKER" && ! -f "$DONE_MARKER") ]]; then
  echo "V1 recovery completion marker is nonregular or symlinked" >&2
  exit 1
fi
if [[ -e "$DONE_MARKER" || -L "$DONE_MARKER" ]]; then
  STATUS_TARGET="$REUSE_STATUS_LOG"
  EVIDENCE_MODE="validated_existing_evidence"
else
  STATUS_TARGET="$STATUS_LOG"
  EVIDENCE_MODE="executed_fresh_reserved_empty_build_dir"
fi

mkdir -p "$LOGS" "$WORK"
cd "$ROOT"

source "$COORDINATION"
verification_authorize_finalization
RUN_ID="$(verification_new_run_id)"
export VERIFICATION_RUN_ID="$RUN_ID"
verification_acquire_writer_lock \
  "v1_recovery" "$LOGS/final_lifecycle_check.txt" "$RUN_ID"

STARTED_AT_UTC="$(date -u '+%Y-%m-%dT%H:%M:%SZ')"
STARTED_AT_EPOCH="$(date -u '+%s')"
VERIFICATION_INPUT_DIGEST="UNAVAILABLE"
SOURCE_DIGEST="UNAVAILABLE"
finish() {
  local code=$?
  local validation_code=0
  local release_code=0
  local state="FAIL"
  local status_tmp="$STATUS_TARGET.tmp.$$"
  local finished_at_utc
  local finished_at_epoch
  local build_log_sha256="UNAVAILABLE"
  local marker_sha256="UNAVAILABLE"
  trap - EXIT INT TERM
  verification_validate_active_lock || validation_code=$?
  if [[ "$code" -eq 0 && "$validation_code" -ne 0 ]]; then
    code="$validation_code"
  fi
  if [[ "$code" == "0" ]]; then
    state="PASS"
  fi
  finished_at_utc="$(date -u '+%Y-%m-%dT%H:%M:%SZ')"
  finished_at_epoch="$(date -u '+%s')"
  if [[ -f "$BUILD_LOG" && ! -L "$BUILD_LOG" ]]; then
    build_log_sha256="$(shasum -a 256 "$BUILD_LOG" | awk '{print $1}')"
  fi
  if [[ -f "$DONE_MARKER" && ! -L "$DONE_MARKER" ]]; then
    marker_sha256="$(shasum -a 256 "$DONE_MARKER" | awk '{print $1}')"
  fi
  write_status() {
    {
      echo "command: ./MatrixConcentration/Verification/scripts/v1_recovery_clean_build.sh"
      echo "run_id: $RUN_ID"
      echo "run_state: $state"
      echo "evidence_mode: $EVIDENCE_MODE"
      echo "verification_input_digest: $VERIFICATION_INPUT_DIGEST"
      echo "source_digest: $SOURCE_DIGEST"
      echo "started_at_utc: $STARTED_AT_UTC"
      echo "finished_at_utc: $finished_at_utc"
      echo "elapsed_seconds: $((finished_at_epoch - STARTED_AT_EPOCH))"
      echo "build_log_sha256: $build_log_sha256"
      echo "completion_marker_sha256: $marker_sha256"
      echo "exit_code: $code"
    } >"$status_tmp"
    mv "$status_tmp" "$STATUS_TARGET"
  }
  write_status
  verification_release_writer_lock || release_code=$?
  if [[ "$code" -eq 0 && "$release_code" -ne 0 ]]; then
    code="$release_code"
    state="FAIL"
    finished_at_utc="$(date -u '+%Y-%m-%dT%H:%M:%SZ')"
    finished_at_epoch="$(date -u '+%s')"
    write_status
  fi
  exit "$code"
}
trap finish EXIT
trap 'exit 130' INT
trap 'exit 143' TERM

verification_load_input_digest "$SCRIPT_DIR"
python3 "$SCRIPT_DIR/source_manifest.py" check >"$MANIFEST_LOG" 2>&1
cat "$MANIFEST_LOG"
SOURCE_DIGEST="$(
  awk '/^TOP_LEVEL_SHA256 / { print $2 }' "$MANIFEST_LOG"
)"
if [[ ! "$SOURCE_DIGEST" =~ ^[0-9a-f]{64}$ ]]; then
  echo "V1 recovery manifest check did not emit one digest" >&2
  exit 1
fi

python3 "$SCRIPT_DIR/check_v1_recovery_config.py" \
  >"$CONFIG_CHECK_LOG" 2>&1
cat "$CONFIG_CHECK_LOG"

for required in "$RECERT_START" "$RECERT_DELETED" "$RECERT_DELETE_LOG"; do
  if [[ ! -f "$required" || -L "$required" ]]; then
    echo "missing re-certification deletion evidence: $required" >&2
    exit 1
  fi
done
DELETE_COUNT="$(
  grep -c '^RECERTIFICATION_DELETE_ONCE ' "$RECERT_DELETE_LOG" || true
)"
if [[ "$DELETE_COUNT" != "1" ]]; then
  echo "expected exactly one re-certification deletion record, measured $DELETE_COUNT" >&2
  exit 1
fi

CONFIG_SHA256="$(shasum -a 256 "$CONFIG" | awk '{print $1}')"
RUNNER_SHA256="$(shasum -a 256 "$0" | awk '{print $1}')"
CONFIG_CHECKER_SHA256="$(
  shasum -a 256 "$SCRIPT_DIR/check_v1_recovery_config.py" | awk '{print $1}'
)"
HASH_TREE_SHA256="$(
  shasum -a 256 "$SCRIPT_DIR/hash_tree.py" | awk '{print $1}'
)"
if [[ -f "$DONE_MARKER" ]]; then
  if [[ ! -f "$BUILD_LOG" || ! -f "$CANONICAL_BEFORE" ||
        ! -f "$CANONICAL_AFTER" || ! -f "$RECOVERY_TREE" ||
        ! -d "$RECOVERY_BUILD" || -L "$RECOVERY_BUILD" ||
        ! -f "$STATUS_LOG" ]]; then
    echo "incomplete V1 recovery completion state" >&2
    exit 1
  fi
  if [[ "$(wc -l <"$DONE_MARKER" | tr -d ' ')" != "15" ]]; then
    echo "invalid V1 recovery completion marker shape" >&2
    exit 1
  fi
  grep -Fxq "marker_version=7" "$DONE_MARKER"
  ORIGINAL_RUN_ID="$(
    awk -F= '$1 == "run_id" { print $2 }' "$DONE_MARKER"
  )"
  if [[ ! "$ORIGINAL_RUN_ID" =~ ^[0-9a-f-]{36}$ ]]; then
    echo "invalid original V1 recovery run id" >&2
    exit 1
  fi
  grep -Fxq "verification_input_digest=$VERIFICATION_INPUT_DIGEST" \
    "$DONE_MARKER"
  grep -Fxq "source_digest=$SOURCE_DIGEST" "$DONE_MARKER"
  grep -Fxq "runner_sha256=$RUNNER_SHA256" "$DONE_MARKER"
  grep -Fxq "config_sha256=$CONFIG_SHA256" "$DONE_MARKER"
  grep -Fxq "config_checker_sha256=$CONFIG_CHECKER_SHA256" "$DONE_MARKER"
  grep -Fxq "hash_tree_sha256=$HASH_TREE_SHA256" "$DONE_MARKER"
  grep -Fxq "build_log_sha256=$(shasum -a 256 "$BUILD_LOG" | awk '{print $1}')" \
    "$DONE_MARKER"
  grep -Fxq "canonical_before_sha256=$(shasum -a 256 "$CANONICAL_BEFORE" | awk '{print $1}')" \
    "$DONE_MARKER"
  grep -Fxq "canonical_after_sha256=$(shasum -a 256 "$CANONICAL_AFTER" | awk '{print $1}')" \
    "$DONE_MARKER"
  grep -Fxq "recovery_tree_sha256=$(shasum -a 256 "$RECOVERY_TREE" | awk '{print $1}')" \
    "$DONE_MARKER"
  grep -Fxq "recovery_build_dir=.audit_work/v1_recertification_recovery_build_v7" \
    "$DONE_MARKER"
  grep -Fxq "canonical_build_unchanged=true" "$DONE_MARKER"
  if ! grep -Eq '^completed_at_utc=[0-9]{4}-[0-9]{2}-[0-9]{2}T[0-9]{2}:[0-9]{2}:[0-9]{2}Z$' \
    "$DONE_MARKER"; then
    echo "invalid V1 recovery completion timestamp" >&2
    exit 1
  fi
  grep -Fxq "EXIT_STATUS 0" "$BUILD_LOG"
  cmp -s "$CANONICAL_BEFORE" "$CANONICAL_AFTER"
  python3 "$SCRIPT_DIR/hash_tree.py" "$RECOVERY_BUILD" |
    cmp -s - "$RECOVERY_TREE"
  grep -Fxq "run_state: PASS" "$STATUS_LOG"
  grep -Fxq "run_id: $ORIGINAL_RUN_ID" "$STATUS_LOG"
  grep -Fxq "evidence_mode: executed_fresh_reserved_empty_build_dir" \
    "$STATUS_LOG"
  grep -Fxq \
    "build_log_sha256: $(shasum -a 256 "$BUILD_LOG" | awk '{print $1}')" \
    "$STATUS_LOG"
  grep -Fxq \
    "completion_marker_sha256: $(shasum -a 256 "$DONE_MARKER" | awk '{print $1}')" \
    "$STATUS_LOG"
  echo "V1 RECERTIFICATION EMPTY-BUILDDIR RECOVERY ALREADY COMPLETE"
  exit 0
fi

if [[ -e "$RECOVERY_BUILD" || -L "$RECOVERY_BUILD" ]]; then
  echo "ambiguous V1 recovery state: output exists without completion marker" >&2
  echo "refusing to delete, reuse, or overwrite $RECOVERY_BUILD" >&2
  exit 1
fi

python3 "$SCRIPT_DIR/hash_tree.py" "$ROOT/.lake/build" >"$CANONICAL_BEFORE"

# Atomically reserve the previously absent build path before any slow
# operation.  The directory is required to be a real, empty directory; a
# second writer can no longer claim the same path during cache refresh.
mkdir "$RECOVERY_BUILD"
if [[ -L "$RECOVERY_BUILD" ||
      -n "$(find "$RECOVERY_BUILD" -mindepth 1 -print -quit)" ]]; then
  echo "failed to reserve a real empty V1 recovery build directory" >&2
  exit 1
fi

set +e
{
  echo "V1 RECERTIFICATION EMPTY-BUILDDIR CACHE REFRESH"
  echo "START $(date '+%Y-%m-%d %H:%M:%S %Z')"
  /usr/bin/time -p "$LAKE" exe cache get
  cache_status=$?
  echo "EXIT_STATUS $cache_status"
  echo "END $(date '+%Y-%m-%d %H:%M:%S %Z')"
} >"$CACHE_LOG" 2>&1
set -e
if [[ "$cache_status" != "0" ]]; then
  exit "$cache_status"
fi

set +e
{
  echo "V1 RECERTIFICATION EMPTY-BUILDDIR ROOT BUILD"
  echo "ROOT $ROOT"
  echo "RUN_ID $RUN_ID"
  echo "VERIFICATION_INPUT_DIGEST $VERIFICATION_INPUT_DIGEST"
  echo "SOURCE_DIGEST $SOURCE_DIGEST"
  echo "CONFIG $CONFIG"
  echo "CONFIG_SHA256 $CONFIG_SHA256"
  echo "RECOVERY_BUILD_DIR $RECOVERY_BUILD"
  echo "RECOVERY_BUILD_DIR_EXISTED_AT_START false"
  echo "RECOVERY_BUILD_DIR_RESERVED_EMPTY true"
  echo "CANONICAL_BUILD_DIR $ROOT/.lake/build"
  echo "COMMAND $LAKE --file MatrixConcentration/Verification/scripts/v1_recovery_lakefile.toml --rehash --no-cache --no-ansi build MatrixConcentration"
  echo "START $(date '+%Y-%m-%d %H:%M:%S %Z')"
  /usr/bin/time -p "$LAKE" \
    --file MatrixConcentration/Verification/scripts/v1_recovery_lakefile.toml \
    --rehash --no-cache --no-ansi build MatrixConcentration
  build_status=$?
  echo "EXIT_STATUS $build_status"
  echo "END $(date '+%Y-%m-%d %H:%M:%S %Z')"
} >"$BUILD_LOG" 2>&1
set -e

python3 "$SCRIPT_DIR/hash_tree.py" "$ROOT/.lake/build" >"$CANONICAL_AFTER"
if ! cmp -s "$CANONICAL_BEFORE" "$CANONICAL_AFTER"; then
  echo "canonical .lake/build changed during isolated recovery build" >&2
  exit 1
fi
if [[ "$build_status" != "0" ]]; then
  exit "$build_status"
fi
if [[ ! -d "$RECOVERY_BUILD" || -L "$RECOVERY_BUILD" ]]; then
  echo "isolated recovery build directory was not created" >&2
  exit 1
fi

python3 "$SCRIPT_DIR/hash_tree.py" "$RECOVERY_BUILD" >"$RECOVERY_TREE"
BUILD_LOG_SHA256="$(shasum -a 256 "$BUILD_LOG" | awk '{print $1}')"
CANONICAL_BEFORE_SHA256="$(
  shasum -a 256 "$CANONICAL_BEFORE" | awk '{print $1}'
)"
CANONICAL_AFTER_SHA256="$(
  shasum -a 256 "$CANONICAL_AFTER" | awk '{print $1}'
)"
RECOVERY_TREE_SHA256="$(
  shasum -a 256 "$RECOVERY_TREE" | awk '{print $1}'
)"
MARKER_TMP="$DONE_MARKER.tmp.$$"
{
  echo "marker_version=7"
  echo "run_id=$RUN_ID"
  echo "verification_input_digest=$VERIFICATION_INPUT_DIGEST"
  echo "source_digest=$SOURCE_DIGEST"
  echo "runner_sha256=$RUNNER_SHA256"
  echo "config_sha256=$CONFIG_SHA256"
  echo "config_checker_sha256=$CONFIG_CHECKER_SHA256"
  echo "hash_tree_sha256=$HASH_TREE_SHA256"
  echo "build_log_sha256=$BUILD_LOG_SHA256"
  echo "canonical_before_sha256=$CANONICAL_BEFORE_SHA256"
  echo "canonical_after_sha256=$CANONICAL_AFTER_SHA256"
  echo "recovery_tree_sha256=$RECOVERY_TREE_SHA256"
  echo "recovery_build_dir=.audit_work/v1_recertification_recovery_build_v7"
  echo "canonical_build_unchanged=true"
  echo "completed_at_utc=$(date -u '+%Y-%m-%dT%H:%M:%SZ')"
} >"$MARKER_TMP"
mv "$MARKER_TMP" "$DONE_MARKER"
echo "V1 RECERTIFICATION EMPTY-BUILDDIR RECOVERY COMPLETE"
