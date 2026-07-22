#!/usr/bin/env python3
"""Fail-closed acceptance check for the V6 Lean witness suite.

The positive suite is accepted only when Lean emitted neither errors nor
`sorry` warnings and every printed axiom set is contained in the audit's
allow-list.  The deliberately bad calibration witness must be rejected for its
`sorry` warning.
"""

from __future__ import annotations

import csv
import json
import re
import sys
from pathlib import Path


SCRIPT = Path(__file__).resolve()
VERIFICATION = SCRIPT.parent.parent
PACKAGE_ROOT = VERIFICATION.parent
REPO_ROOT = PACKAGE_ROOT.parent
LOGS = VERIFICATION / "logs"

GOOD_SOURCE = VERIFICATION / "scripts" / "witnesses" / "V6Witnesses.lean"
GOOD_COMPILE = LOGS / "v6_witnesses_compile.log"
GOOD_COMPILE_STATUS = LOGS / "v6_witnesses_compile_status.log"
GOOD_AXIOMS = LOGS / "v6_witness_axioms.tsv"
BAD_SOURCE = REPO_ROOT / ".audit_work" / "BadWitness.lean"
BAD_COMPILE = LOGS / "calibration_bad_witness_compile.log"
BAD_COMPILE_STATUS = LOGS / "calibration_bad_witness_compile_status.log"

OUTPUT_JSON = LOGS / "v6_witness_acceptance.json"
OUTPUT_LOG = LOGS / "v6_witness_acceptance.log"

ALLOWED_AXIOMS = {"propext", "Classical.choice", "Quot.sound"}
FORBIDDEN_GOOD = (
    r": error(?::|\b)",
    r"declaration uses ['`]?sorry",
    r"\bsorryAx\b",
)
BAD_SORRY = r"declaration uses ['`]?sorry"


def main() -> int:
    errors: list[str] = []
    for path in (
        GOOD_SOURCE,
        GOOD_COMPILE,
        GOOD_COMPILE_STATUS,
        GOOD_AXIOMS,
        BAD_SOURCE,
        BAD_COMPILE,
        BAD_COMPILE_STATUS,
    ):
        if not path.is_file():
            errors.append(f"missing required evidence: {path}")

    good_patterns: list[str] = []
    bad_has_sorry = False
    axiom_rows = 0
    disallowed: dict[str, list[str]] = {}
    duplicates: list[str] = []
    auto_implicit_false = False
    good_exit_zero = False
    bad_exit_zero = False

    if GOOD_SOURCE.is_file():
        good_source = GOOD_SOURCE.read_text(encoding="utf-8")
        auto_implicit_false = "set_option autoImplicit false" in good_source
        if not auto_implicit_false:
            errors.append("official witness source does not disable autoImplicit")

    if GOOD_COMPILE.is_file():
        good_compile = GOOD_COMPILE.read_text(encoding="utf-8")
        good_patterns = [
            pattern
            for pattern in FORBIDDEN_GOOD
            if re.search(pattern, good_compile, flags=re.IGNORECASE)
        ]
        if good_patterns:
            errors.append(
                "official witness compile contains forbidden patterns: "
                + ", ".join(good_patterns)
            )

    if GOOD_COMPILE_STATUS.is_file():
        status_text = GOOD_COMPILE_STATUS.read_text(encoding="utf-8")
        good_exit_zero = bool(
            re.search(r"(?m)^exit_code:\s*0\s*$", status_text)
        )
        if not good_exit_zero:
            errors.append(
                "official witness compile status does not record exit_code: 0"
            )

    if GOOD_AXIOMS.is_file():
        seen: set[str] = set()
        with GOOD_AXIOMS.open(newline="", encoding="utf-8") as handle:
            for row in csv.DictReader(handle, delimiter="\t"):
                axiom_rows += 1
                name = row["name"]
                if name in seen:
                    duplicates.append(name)
                seen.add(name)
                axioms = {item for item in row["axioms"].split(",") if item}
                extras = sorted(axioms - ALLOWED_AXIOMS)
                if extras:
                    disallowed[name] = extras
        if not axiom_rows:
            errors.append("official witness axiom ledger has no declarations")
        if duplicates:
            errors.append(
                "duplicate official witness axiom rows: "
                + ", ".join(sorted(duplicates))
            )
        if disallowed:
            errors.append(
                "official witnesses use disallowed axioms: "
                + json.dumps(disallowed, sort_keys=True)
            )

    if BAD_COMPILE.is_file():
        bad_compile = BAD_COMPILE.read_text(encoding="utf-8")
        bad_has_sorry = bool(
            re.search(BAD_SORRY, bad_compile, flags=re.IGNORECASE)
        )
        if not bad_has_sorry:
            errors.append(
                "BadWitness calibration log lacks the expected `sorry` warning"
            )

    if BAD_COMPILE_STATUS.is_file():
        bad_status_text = BAD_COMPILE_STATUS.read_text(encoding="utf-8")
        bad_exit_zero = bool(
            re.search(r"(?m)^exit_code:\s*0\s*$", bad_status_text)
        )
        if not bad_exit_zero:
            errors.append(
                "BadWitness calibration compile status does not record exit_code: 0"
            )

    official_status = (
        "ACCEPTED"
        if not good_patterns
        and good_exit_zero
        and auto_implicit_false
        and axiom_rows > 0
        and not duplicates
        and not disallowed
        else "REJECTED"
    )
    bad_status = "REJECTED" if bad_has_sorry else "NOT_REJECTED"
    status = (
        "PASS"
        if not errors
        and official_status == "ACCEPTED"
        and bad_status == "REJECTED"
        else "FAIL"
    )

    result = {
        "status": status,
        "official_witness_suite": official_status,
        "bad_witness_calibration": bad_status,
        "official_axiom_rows": axiom_rows,
        "allowed_axioms": sorted(ALLOWED_AXIOMS),
        "autoImplicit_false": auto_implicit_false,
        "official_compile_exit_zero": good_exit_zero,
        "official_forbidden_compile_patterns": good_patterns,
        "disallowed_axioms": disallowed,
        "bad_witness_sorry_warning_detected": bad_has_sorry,
        "bad_witness_compile_exit_zero": bad_exit_zero,
        "errors": errors,
    }
    OUTPUT_JSON.write_text(
        json.dumps(result, indent=2, sort_keys=True) + "\n",
        encoding="utf-8",
    )

    lines = [
        "positive_compile_command: ~/.elan/bin/lake env lean "
        "-DmaxSynthPendingDepth=3 -DrelaxedAutoImplicit=false "
        "MatrixConcentration/Verification/scripts/witnesses/V6Witnesses.lean "
        "> MatrixConcentration/Verification/logs/v6_witnesses_compile.log 2>&1",
        "negative_compile_command: ~/.elan/bin/lake env lean "
        "-DmaxSynthPendingDepth=3 -DrelaxedAutoImplicit=false "
        ".audit_work/BadWitness.lean "
        "> MatrixConcentration/Verification/logs/"
        "calibration_bad_witness_compile.log 2>&1",
        f"status: {status}",
        f"official_witness_suite: {official_status}",
        f"official_compile_exit_zero: {str(good_exit_zero).lower()}",
        f"official_axiom_rows: {axiom_rows}",
        "allowed_axioms: " + ",".join(sorted(ALLOWED_AXIOMS)),
        f"bad_witness_calibration: {bad_status}",
        f"bad_witness_compile_exit_zero: {str(bad_exit_zero).lower()}",
        f"bad_witness_sorry_warning_detected: {str(bad_has_sorry).lower()}",
    ]
    lines.extend(f"ERROR: {error}" for error in errors)
    OUTPUT_LOG.write_text("\n".join(lines) + "\n", encoding="utf-8")
    print("\n".join(lines))
    return 0 if status == "PASS" else 1


if __name__ == "__main__":
    sys.exit(main())
