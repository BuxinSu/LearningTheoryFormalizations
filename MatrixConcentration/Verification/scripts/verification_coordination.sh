#!/usr/bin/env bash
# Shared single-writer and finalization-guard primitives.
#
# Callers define LOCK_FILE and FINALIZATION_GUARD before sourcing this file.
# A finalization guard is authorized only by knowledge of a high-entropy token;
# the token itself is never stored in the repository or audit artifacts.

FINALIZATION_TOKEN_SHA256="0c51b9313f7556a6724d28a1c26fd3a79a9e5567ead30f449b8679d72e37e944"
OWNS_LOCK=0
ACTIVE_LOCK_TOKEN=""
LOCK_TOKEN=""
VERIFICATION_LOCK_CAPABILITY=""

verification_sha256_text() {
  printf '%s' "$1" |
    /usr/bin/shasum -a 256 |
    /usr/bin/awk '{print $1}'
}

verification_new_run_id() {
  /usr/bin/uuidgen | /usr/bin/tr '[:upper:]' '[:lower:]'
}

verification_new_capability() {
  printf '%s%s' \
    "$(/usr/bin/uuidgen)" \
    "$(/usr/bin/uuidgen)" |
    /usr/bin/tr -d '-' |
    /usr/bin/tr '[:upper:]' '[:lower:]'
}

verification_load_input_digest() {
  local script_dir="$1"
  local output
  output="$(
    python3 "$script_dir/verification_input_manifest.py" check
  )" || return $?
  printf '%s\n' "$output"
  VERIFICATION_INPUT_DIGEST="$(
    printf '%s\n' "$output" |
      /usr/bin/awk '/^TOP_LEVEL_SHA256 / { print $2 }'
  )"
  if [[ ! "$VERIFICATION_INPUT_DIGEST" =~ ^[0-9a-f]{64}$ ]]; then
    echo "verification input manifest did not emit one digest" >&2
    return 1
  fi
  export VERIFICATION_INPUT_DIGEST
}

verification_authorize_finalization() {
  if [[ ! -e "$FINALIZATION_GUARD" && ! -L "$FINALIZATION_GUARD" ]]; then
    return 0
  fi
  if [[ ! -f "$FINALIZATION_GUARD" || -L "$FINALIZATION_GUARD" ]]; then
    echo "verification finalization guard is not a regular file: $FINALIZATION_GUARD" >&2
    return 76
  fi
  local candidate
  local supplied_sha256
  candidate="${VERIFICATION_FINALIZATION_TOKEN:-${VERIFICATION_OUTER_LOCK_CAPABILITY:-}}"
  supplied_sha256="$(verification_sha256_text "$candidate")"
  if [[ "$supplied_sha256" != "$FINALIZATION_TOKEN_SHA256" ]]; then
    echo "verification finalization guard is active: $FINALIZATION_GUARD" >&2
    return 76
  fi
}

verification_acquire_writer_lock() {
  local runner="$1"
  local lifecycle_output="${2:-}"
  local lifecycle_run_id="${3:-${VERIFICATION_RUN_ID:-unknown}}"
  local observed
  local capability_sha256
  OWNS_LOCK=0
  ACTIVE_LOCK_TOKEN=""
  LOCK_TOKEN=""
  VERIFICATION_LOCK_CAPABILITY=""

  if [[ "${VERIFICATION_OUTER_LOCK_HELD:-0}" == "1" ]]; then
    if [[ ! -s "$LOCK_FILE" || -L "$LOCK_FILE" ||
          -z "${VERIFICATION_OUTER_LOCK_CAPABILITY:-}" ]]; then
      echo "outer verification lock was declared but is absent or unbound: $LOCK_FILE" >&2
      return 75
    fi
    observed="$(<"$LOCK_FILE")"
    capability_sha256="$(
      verification_sha256_text "$VERIFICATION_OUTER_LOCK_CAPABILITY"
    )"
    if [[ ! "$observed" =~ ^pid=[0-9]+\ runner=(run_all|finalization)\ capability_sha256=$capability_sha256\ run_id=[0-9a-f-]{36}$ ]]; then
      echo "outer verification capability does not match $LOCK_FILE" >&2
      return 75
    fi
    if [[ (-e "$FINALIZATION_GUARD" || -L "$FINALIZATION_GUARD") &&
          ! "$observed" =~ ^pid=[0-9]+\ runner=finalization\ capability_sha256=$FINALIZATION_TOKEN_SHA256\ run_id=[0-9a-f-]{36}$ ]]; then
      local explicit_finalization_sha256
      explicit_finalization_sha256="$(
        verification_sha256_text "${VERIFICATION_FINALIZATION_TOKEN:-}"
      )"
      if [[ "$explicit_finalization_sha256" != "$FINALIZATION_TOKEN_SHA256" ]]; then
        echo "guarded finalization requires explicit finalizer authorization" >&2
        return 75
      fi
    fi
    ACTIVE_LOCK_TOKEN="$observed"
    VERIFICATION_LOCK_CAPABILITY="$VERIFICATION_OUTER_LOCK_CAPABILITY"
  else
    local run_id
    VERIFICATION_LOCK_CAPABILITY="$(verification_new_capability)"
    capability_sha256="$(
      verification_sha256_text "$VERIFICATION_LOCK_CAPABILITY"
    )"
    run_id="${VERIFICATION_RUN_ID:-$(verification_new_run_id)}"
    LOCK_TOKEN="pid=$$ runner=$runner capability_sha256=$capability_sha256 run_id=$run_id"
    if ! (set -o noclobber; printf '%s\n' "$LOCK_TOKEN" >"$LOCK_FILE") 2>/dev/null; then
      echo "verification run already active: $LOCK_FILE" >&2
      return 75
    fi
    OWNS_LOCK=1
    ACTIVE_LOCK_TOKEN="$LOCK_TOKEN"
    local post_acquire_authorization=0
    verification_authorize_finalization ||
      post_acquire_authorization=$?
    if [[ "$post_acquire_authorization" -ne 0 ]]; then
      verification_release_writer_lock || return $?
      return "$post_acquire_authorization"
    fi
  fi

  export VERIFICATION_OUTER_LOCK_CAPABILITY="$VERIFICATION_LOCK_CAPABILITY"
  if [[ -n "$lifecycle_output" ]]; then
    local invalidate_code=0
    verification_invalidate_final_lifecycle \
      "$lifecycle_output" "$runner" "$lifecycle_run_id" ||
      invalidate_code=$?
    if [[ "$invalidate_code" -ne 0 ]]; then
      # Keep the lock as a visible validity gate if an older PASS transcript
      # could not be replaced by the non-PASS sentinel.
      return "$invalidate_code"
    fi
  fi
}

verification_validate_owned_lock() {
  if [[ "$OWNS_LOCK" != "1" ]]; then
    return 0
  fi
  local observed=""
  if [[ ! -f "$LOCK_FILE" || -L "$LOCK_FILE" ]]; then
    echo "verification lock is missing, nonregular, or symlinked: $LOCK_FILE" >&2
    return 74
  fi
  observed="$(<"$LOCK_FILE")"
  if [[ "$observed" != "$LOCK_TOKEN" ]]; then
    echo "verification lock ownership changed: $LOCK_FILE" >&2
    return 74
  fi
}

verification_validate_active_lock() {
  local observed=""
  if [[ ! -f "$LOCK_FILE" || -L "$LOCK_FILE" ]]; then
    echo "active verification lock is missing, nonregular, or symlinked: $LOCK_FILE" >&2
    return 74
  fi
  observed="$(<"$LOCK_FILE")"
  if [[ "$observed" != "$ACTIVE_LOCK_TOKEN" ]]; then
    echo "active verification lock ownership changed: $LOCK_FILE" >&2
    return 74
  fi
}

verification_invalidate_final_lifecycle() {
  local output="$1"
  local runner="$2"
  local run_id="$3"
  local temporary="${output}.tmp.$$"
  verification_validate_active_lock || return $?
  {
    echo "FINAL VERIFICATION LIFECYCLE CHECK"
    echo "state=INVALIDATED"
    echo "invalidated_by=$runner"
    echo "run_id=$run_id"
    echo "invalidated_at_utc=$(date -u '+%Y-%m-%dT%H:%M:%SZ')"
    echo "result=FAIL"
  } >"$temporary" || return $?
  mv -f -- "$temporary" "$output"
}

verification_release_writer_lock() {
  if [[ "$OWNS_LOCK" != "1" ]]; then
    return 0
  fi
  if ! verification_validate_owned_lock; then
    return 74
  fi
  if ! rm -f -- "$LOCK_FILE"; then
    echo "failed to remove owned verification lock: $LOCK_FILE" >&2
    return 74
  fi
  if [[ -e "$LOCK_FILE" || -L "$LOCK_FILE" ]]; then
    echo "owned verification lock remains after removal: $LOCK_FILE" >&2
    return 74
  fi
  OWNS_LOCK=0
}
