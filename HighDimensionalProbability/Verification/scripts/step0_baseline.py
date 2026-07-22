#!/usr/bin/env python3
"""Measure and print the adapted current-tree verification baseline."""

from __future__ import annotations

import re
from pathlib import Path

from file_universe import ROOT


HDP = ROOT / "HighDimensionalProbability"
VERIFICATION = HDP / "Verification"
REVIEW = VERIFICATION / "REVIEW_NOTES.md"
FAITHFUL = VERIFICATION / "archive" / "FAITHFUL_PROOFREAD_REPORT.md"
CORRECTION = VERIFICATION / "CORRECTION_LEDGER.md"
APPENDIX_SUMMARY = HDP / "APPENDIX_SUMMARY.md"


def matching_lines(path: Path, patterns: tuple[str, ...]) -> list[str]:
    compiled = [re.compile(pattern) for pattern in patterns]
    result: list[str] = []
    for number, line in enumerate(path.read_text(encoding="utf-8").splitlines(), start=1):
        if any(pattern.search(line) for pattern in compiled):
            result.append(f"{path.relative_to(ROOT)}:{number}: {line}")
    return result


def code_sorry_lines(path: Path) -> list[tuple[int, str]]:
    pattern = re.compile(r"^\s*(?:by\s+)?sorry\s*(?:--.*)?$")
    return [
        (number, line)
        for number, line in enumerate(path.read_text(encoding="utf-8").splitlines(), start=1)
        if pattern.match(line)
    ]


def main() -> int:
    review_text = REVIEW.read_text(encoding="utf-8")
    faithful_text = FAITHFUL.read_text(encoding="utf-8")
    correction_text = CORRECTION.read_text(encoding="utf-8")
    summary_text = APPENDIX_SUMMARY.read_text(encoding="utf-8")

    exercise_files = sorted(HDP.glob("Exercise/Chapter*/*.lean"))
    appendix_files = sorted((HDP / "Appendix").rglob("*.lean")) + [HDP / "Appendix.lean"]
    exercise_sorries = {
        path.relative_to(ROOT).as_posix(): code_sorry_lines(path)
        for path in exercise_files
        if code_sorry_lines(path)
    }
    appendix_sorries = {
        path.relative_to(ROOT).as_posix(): code_sorry_lines(path)
        for path in appendix_files
        if code_sorry_lines(path)
    }
    marker_count = sum(
        path.read_text(encoding="utf-8").count("EXERCISE-SORRY")
        for path in exercise_files
    )

    review_current = all(
        token in review_text
        for token in (
            "**835 = 769 core-formalized + 66 Appendix-proved + 0",
            "There are zero core-partial and zero missing in-scope conclusions.",
            "**14/14 source-faithful PROVED**",
            "zero active deferred/source-limited census rows",
        )
    )
    faithful_historical = all(
        token in faithful_text
        for token in (
            "historical Pass 05 audit",
            "not the\n> active tree",
            "**763 core-formalized**",
            "**5 core-partial**",
        )
    )
    appendix_current = all(
        token in summary_text
        for token in (
            "**14/14 source-faithful proved",
            "The Appendix aggregator has 15 direct imports",
            "The three former non-source-faithful scopes are closed by removal",
            "**835 = 769 core + 66 Appendix + 0",
        )
    )
    correction_current = all(
        token in correction_text
        for token in (
            "exactly 228 executable `sorry` proofs",
            "Appendix\nsource has zero `sorry`, `admit`, `axiom`, `unsafe`, or `native_decide`",
            "**14/14 source-faithful proved**",
            "**835 = 769 core + 66 Appendix proved + 0 deferred/source-limited**",
        )
    )
    correction_stale = any(
        token in correction_text
        for token in (
            "exactly three `sorryAx` witnesses",
            "231 executable placeholders total",
            "17 targets, split 13 proved / 4 unresolved",
        )
    )

    print("ADAPTED STEP 0 CURRENT-TREE BASELINE")
    print("====================================")
    print("Authorization: the project owner explicitly selected the current-tree adaptation path.")
    print("Policy: current source and APPENDIX_SUMMARY.md are authoritative; incompatible")
    print("historical ledger claims are findings, not seed facts.")
    print()
    print("[measured source placeholder boundary]")
    print(f"exercise_code_sorries: {sum(len(lines) for lines in exercise_sorries.values())}")
    print(f"exercise_files_with_code_sorry: {len(exercise_sorries)}")
    print(f"exercise_marker_occurrences: {marker_count}")
    print(f"appendix_code_sorries: {sum(len(lines) for lines in appendix_sorries.values())}")
    print(f"appendix_files_with_code_sorry: {len(appendix_sorries)}")
    print()
    print("[record-state checks]")
    print(f"review_current_835_769_66_0: {str(review_current).lower()}")
    print(f"faithful_body_explicitly_historical_763_5_65_5: {str(faithful_historical).lower()}")
    print(f"appendix_summary_current_14_of_14_and_three_scopes_removed: {str(appendix_current).lower()}")
    print(f"correction_ledger_current_228_0_14_of_14_and_835: {str(correction_current).lower()}")
    print(f"correction_ledger_contains_stale_3_sorryAx_231_13_plus_4: {str(correction_stale).lower()}")
    print()
    print("[active 835-census reconciliation]")
    print("core_formalized: 769")
    print("core_partial: 0")
    print("appendix_proved: 66")
    print("appendix_unresolved_or_deferred: 0")
    print("total_valid_conclusions: 835")
    print("derivation: project the frozen 838-row record onto the active tree; remove the")
    print("positive-Ricci, arbitrary-set Chevet, and Borell scope rows, retain the finite")
    print("Chevet theorem and Exercise 8.39(b), and keep Brownian source-faithful proved.")
    print()
    print("[supporting record excerpts]")
    for path, patterns in (
        (REVIEW, (r"835 = 769 core-formalized", r"zero core-partial", r"14/14 source-faithful PROVED", r"zero active deferred", r"removed on")),
        (FAITHFUL, (r"historical", r"not descriptions of the corrected tree", r"763 core-formalized", r"5 core-partial")),
        (CORRECTION, (r"exactly 228 executable `sorry`", r"Appendix source has zero", r"14/14 source-faithful proved", r"835 = 769 core")),
        (APPENDIX_SUMMARY, (r"14/14 source-faithful proved", r"15 direct imports", r"RESOLVED BY REMOVAL", r"835 = 769 core")),
    ):
        for line in matching_lines(path, patterns):
            print(line)

    expected = (
        review_current
        and faithful_historical
        and appendix_current
        and correction_current
        and not correction_stale
        and sum(len(lines) for lines in exercise_sorries.values()) == 228
        and len(exercise_sorries) == 46
        and not appendix_sorries
    )
    print()
    print(f"adapted_step0_baseline_ok: {str(expected).lower()}")
    return 0 if expected else 1


if __name__ == "__main__":
    raise SystemExit(main())
