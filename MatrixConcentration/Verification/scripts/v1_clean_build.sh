#!/usr/bin/env bash
set -euo pipefail

SCRIPT_DIR="$(cd "$(dirname "${BASH_SOURCE[0]}")" && pwd)"
VERIFY_DIR="$(cd "${SCRIPT_DIR}/.." && pwd)"
ROOT="$(cd "${VERIFY_DIR}/../.." && pwd)"
LOG_DIR="${VERIFY_DIR}/logs"
WORK_DIR="${ROOT}/.audit_work"
DELETE_MARKER="${WORK_DIR}/v1_build_deleted.marker"
DONE_MARKER="${WORK_DIR}/v1_clean_build.done"
DELETE_LOG="${LOG_DIR}/build_delete_once.log"
LOCK_FILE="${WORK_DIR}/verification.run.lock"
FINALIZATION_GUARD="${WORK_DIR}/verification.finalization.guard"
COORDINATION="${SCRIPT_DIR}/verification_coordination.sh"

for directory in "${LOG_DIR}" "${WORK_DIR}"; do
  if [[ -L "$directory" || ( -e "$directory" && ! -d "$directory" ) ]]; then
    echo "verification path is not a real directory: $directory" >&2
    exit 1
  fi
done
mkdir -p "${LOG_DIR}" "${WORK_DIR}"
cd "${ROOT}"

source "$COORDINATION"
verification_authorize_finalization
RUN_ID="${VERIFICATION_PARENT_RUN_ID:-$(verification_new_run_id)}"
export VERIFICATION_RUN_ID="$RUN_ID"
verification_acquire_writer_lock \
  "v1_clean_build" "${LOG_DIR}/final_lifecycle_check.txt" "$RUN_ID"
finish() {
  local code=$?
  local validation_code=0
  local release_code=0
  trap - EXIT INT TERM
  verification_validate_active_lock || validation_code=$?
  if [[ "$code" -eq 0 && "$validation_code" -ne 0 ]]; then
    code="$validation_code"
  fi
  verification_release_writer_lock || release_code=$?
  if [[ "$code" -eq 0 && "$release_code" -ne 0 ]]; then
    code="$release_code"
  fi
  exit "$code"
}
trap finish EXIT
trap 'exit 130' INT
trap 'exit 143' TERM

verification_load_input_digest "$SCRIPT_DIR"

if [[ -L "${DONE_MARKER}" ||
      (-e "${DONE_MARKER}" && ! -f "${DONE_MARKER}") ]]; then
  echo "V1 canonical completion marker is nonregular or symlinked" >&2
  exit 1
fi
if [[ ! -f "${DELETE_MARKER}" || ! -f "${DELETE_LOG}" ]]; then
  echo "missing historical V1 deletion evidence; refusing any deletion" >&2
  exit 1
fi

SOURCE_OUTPUT="$(python3 "${SCRIPT_DIR}/source_manifest.py" check)"
printf '%s\n' "$SOURCE_OUTPUT"
SOURCE_DIGEST="$(
  printf '%s\n' "$SOURCE_OUTPUT" |
    awk '/^TOP_LEVEL_SHA256 / { print $2 }'
)"
if [[ ! "$SOURCE_DIGEST" =~ ^[0-9a-f]{64}$ ]]; then
  echo "source manifest did not emit exactly one digest" >&2
  exit 1
fi

if [[ -f "${DONE_MARKER}" ]]; then
  if [[ ! -f "${LOG_DIR}/build_full.log" ||
        -L "${LOG_DIR}/build_full.log" ]]; then
    echo "incomplete V1 canonical completion state" >&2
    exit 1
  fi
  if [[ "$(wc -l <"$DONE_MARKER" | tr -d ' ')" != "7" ]]; then
    echo "invalid V1 canonical completion marker shape" >&2
    exit 1
  fi
  grep -Fxq "marker_version=2" "$DONE_MARKER"
  grep -Fxq "run_id=$RUN_ID" "$DONE_MARKER"
  grep -Fxq "verification_input_digest=$VERIFICATION_INPUT_DIGEST" \
    "$DONE_MARKER"
  grep -Fxq \
    "runner_sha256=$(shasum -a 256 "$0" | awk '{print $1}')" \
    "$DONE_MARKER"
  grep -Fxq "source_digest=$SOURCE_DIGEST" "$DONE_MARKER"
  grep -Fxq \
    "build_log_sha256=$(shasum -a 256 "${LOG_DIR}/build_full.log" | awk '{print $1}')" \
    "$DONE_MARKER"
  grep -Fxq "EXIT_STATUS 0" "${LOG_DIR}/build_full.log"
  echo "V1 canonical replay already complete; preserving all deletion invariants."
  exit 0
fi

set +e
{
  echo "V1 MATHLIB CACHE REFRESH"
  echo "START $(date '+%Y-%m-%d %H:%M:%S %Z')"
  /usr/bin/time -p "${HOME}/.elan/bin/lake" exe cache get
  cache_status=$?
  echo "EXIT_STATUS ${cache_status}"
  echo "END $(date '+%Y-%m-%d %H:%M:%S %Z')"
} > "${LOG_DIR}/cache_get.log" 2>&1
set -e
if [[ "${cache_status}" != "0" ]]; then
  exit "${cache_status}"
fi

# The destructive reset belongs to the frozen baseline history.  This
# post-recertification runner is intentionally incapable of deleting any
# build directory.  Clean-state reconstruction uses the separate, initially
# absent audit buildDir in v1_recovery_clean_build.sh.
echo "RESUME_WITHOUT_DELETE $(date '+%Y-%m-%d %H:%M:%S %Z') ${ROOT}/.lake/build" \
  >> "${DELETE_LOG}"

set +e
{
  echo "V1 CANONICAL ROOT REPLAY BUILD"
  echo "ROOT ${ROOT}"
  echo "RUN_ID ${RUN_ID}"
  echo "VERIFICATION_INPUT_DIGEST ${VERIFICATION_INPUT_DIGEST}"
  echo "SOURCE_DIGEST ${SOURCE_DIGEST}"
  echo "COMMAND ${HOME}/.elan/bin/lake --no-ansi build MatrixConcentration"
  echo "START $(date '+%Y-%m-%d %H:%M:%S %Z')"
  /usr/bin/time -p "${HOME}/.elan/bin/lake" --no-ansi build MatrixConcentration
  build_status=$?
  echo "EXIT_STATUS ${build_status}"
  echo "END $(date '+%Y-%m-%d %H:%M:%S %Z')"
} > "${LOG_DIR}/build_full.log" 2>&1
set -e
if [[ "${build_status}" != "0" ]]; then
  exit "${build_status}"
fi

MARKER_TMP="${DONE_MARKER}.tmp.$$"
{
  echo "marker_version=2"
  echo "run_id=$RUN_ID"
  echo "verification_input_digest=$VERIFICATION_INPUT_DIGEST"
  echo "runner_sha256=$(shasum -a 256 "$0" | awk '{print $1}')"
  echo "source_digest=$SOURCE_DIGEST"
  echo "build_log_sha256=$(shasum -a 256 "${LOG_DIR}/build_full.log" | awk '{print $1}')"
  echo "completed_at_utc=$(date -u '+%Y-%m-%dT%H:%M:%SZ')"
} >"$MARKER_TMP"
mv "$MARKER_TMP" "$DONE_MARKER"
echo "V1 CANONICAL REPLAY BUILD COMPLETE"
