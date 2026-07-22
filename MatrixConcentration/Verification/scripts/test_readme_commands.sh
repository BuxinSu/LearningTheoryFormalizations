#!/usr/bin/env bash
# Exercise the corrected README commands and retain the old cwd as a negative control.

set -u

ROOT="$(cd "$(dirname "${BASH_SOURCE[0]}")/../../.." && pwd)"
SOURCE="$ROOT/MatrixConcentration"
LOGS="$SOURCE/Verification/logs"
LAKE="$HOME/.elan/bin/lake"
DIRECT="MatrixConcentration/Chapter4_MatrixGaussianAndRademacherSeries.lean"

set +e
(cd "$SOURCE" && "$LAKE" build) >"$LOGS/v9_readme_source_build.log" 2>&1
source_build=$?
(cd "$SOURCE" && "$LAKE" env lean "$DIRECT") \
  >"$LOGS/v9_readme_source_direct.log" 2>&1
source_direct=$?
(cd "$ROOT" && "$LAKE" build) >"$LOGS/v9_readme_root_build.log" 2>&1
root_build=$?
(cd "$ROOT" && "$LAKE" env lean "$DIRECT") \
  >"$LOGS/v9_readme_root_direct.log" 2>&1
root_direct=$?
set -e

if [[ $root_build -eq 0 && $root_direct -eq 0 &&
      $source_build -ne 0 && $source_direct -ne 0 ]]; then
  measured="PRINTED_PROJECT_ROOT_COMMANDS_SUCCEED_SOURCE_CWD_NEGATIVE_CONTROL_FAILS"
  status=0
else
  measured="UNEXPECTED_STATUS_PATTERN"
  status=1
fi

{
  echo "V9 README COMMAND CHECK"
  echo "readme=$SOURCE/README.md"
  echo "printed_context=Lake project root"
  echo "source_cwd=$SOURCE"
  echo "project_root=$ROOT"
  echo "source_build_status=$source_build"
  echo "source_direct_status=$source_direct"
  echo "root_build_status=$root_build"
  echo "root_direct_status=$root_direct"
  echo "measured_result=$measured"
} | tee "$LOGS/v9_readme_commands_summary.txt"

exit "$status"
