#!/usr/bin/env bash
# The V9 checker must reject a fake endpoint added only to a README copy.

set -u

ROOT="$(cd "$(dirname "${BASH_SOURCE[0]}")/../../.." && pwd)"
CHECKER="$ROOT/MatrixConcentration/Verification/scripts/verify_readme_claims.py"
FAKE="$ROOT/.audit_work/README_fake_name.md"
LOGS="$ROOT/MatrixConcentration/Verification/logs"

python3 "$CHECKER" --make-calibration-copy \
  >"$LOGS/v9_readme_calibration_setup.log" 2>&1

set +e
python3 "$CHECKER" --readme "$FAKE" \
  >"$LOGS/v9_readme_calibration_check.log" 2>&1
checker_status=$?
set -e

if [[ $checker_status -ne 0 ]] &&
   grep -q "verificationDefinitelyMissingEndpoint" \
     "$LOGS/v9_readme_calibration_check.log"; then
  result="PASS_EXPECTED_REJECTION"
  exit_status=0
else
  result="FAIL_NOT_REJECTED"
  exit_status=1
fi

{
  echo "V9 README CHECKER CALIBRATION"
  echo "plant=$FAKE"
  echo "planted_name=verificationDefinitelyMissingEndpoint"
  echo "checker_status=$checker_status"
  echo "result=$result"
} | tee "$LOGS/v9_readme_calibration_summary.txt"

exit "$exit_status"
