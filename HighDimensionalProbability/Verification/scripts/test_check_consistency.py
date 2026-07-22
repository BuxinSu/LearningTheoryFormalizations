#!/usr/bin/env python3
"""Static tests for the Verification README/report consistency checker."""

from __future__ import annotations

import re
import sys
import tempfile
import unittest
from pathlib import Path

SCRIPT_DIR = Path(__file__).resolve().parent
if str(SCRIPT_DIR) not in sys.path:
    sys.path.insert(0, str(SCRIPT_DIR))

from check_consistency import (
    EXPECTED_REPORTS,
    _mutate_text,
    _split_markdown_row,
    _write_synthetic_bundle,
    check_consistency,
    run_self_test,
)


class ConsistencyCheckerTests(unittest.TestCase):
    def setUp(self) -> None:
        self.temporary = tempfile.TemporaryDirectory(
            prefix="hdp-consistency-test-"
        )
        self.root = Path(self.temporary.name)
        _write_synthetic_bundle(self.root)

    def tearDown(self) -> None:
        self.temporary.cleanup()

    def problems(self) -> tuple[str, ...]:
        return check_consistency(self.root).problems

    def assert_problem(self, fragment: str) -> None:
        problems = self.problems()
        self.assertTrue(
            any(fragment in problem for problem in problems),
            f"{fragment!r} absent from {problems!r}",
        )

    def test_valid_ten_report_bundle_passes(self) -> None:
        result = check_consistency(self.root)
        self.assertTrue(result.passed, result.problems)
        self.assertEqual(sorted(result.reports), list(range(1, 11)))
        self.assertEqual(len(result.index_rows), 10)
        self.assertEqual(len(result.summary_findings), 4)

    def test_markdown_row_parser_keeps_escaped_and_code_pipes(self) -> None:
        self.assertEqual(
            _split_markdown_row(r"| a \| b | `x | y` | z |"),
            [r"a \| b", "`x | y`", "z"],
        )

    def test_duplicate_and_missing_report_ids_are_rejected(self) -> None:
        path = self.root / EXPECTED_REPORTS[1]
        needle = "| V1-F1 | MAJOR | Synthetic finding. | evidence |"
        _mutate_text(
            path, lambda text: text.replace(needle, f"{needle}\n{needle}", 1)
        )
        self.assert_problem("duplicate finding ID V1-F1")

        _write_synthetic_bundle(self.root)
        _mutate_text(path, lambda text: text.replace("V1-F1", "V1-F2", 1))
        self.assert_problem("missing finding IDs in contiguous sequence: V1-F1")

    def test_index_count_and_verdict_disagreements_are_rejected(self) -> None:
        readme = self.root / "README.md"
        _mutate_text(
            readme,
            lambda text: re.sub(
                r"(?m)^(\| V1 \|.*\| )0/1/0/0( \| \[)",
                r"\g<1>0/0/0/0\2",
                text,
                count=1,
            ),
        )
        self.assert_problem("README counts 0/0/0/0 differ")

        _write_synthetic_bundle(self.root)
        report = self.root / EXPECTED_REPORTS[4]
        _mutate_text(
            report,
            lambda text: text.replace(
                "**Verdict: PASS**", "**Verdict: PASS-WITH-NOTES**", 1
            ),
        )
        self.assert_problem("violates severity mapping")
        self.assert_problem("README verdict 'PASS' differs")

    def test_missing_duplicate_and_mismatched_summary_rows_are_rejected(
        self,
    ) -> None:
        readme = self.root / "README.md"
        _mutate_text(
            readme,
            lambda text: re.sub(
                r"(?m)^\| V2-F1 \| MINOR \|.*\|\n", "", text, count=1
            ),
        )
        self.assert_problem("README findings summary missing V2-F1")

        _write_synthetic_bundle(self.root)
        line = next(
            item
            for item in readme.read_text(encoding="utf-8").splitlines()
            if item.startswith("| V3-F1 |")
        )
        _mutate_text(
            readme, lambda text: text.replace(line, f"{line}\n{line}", 1)
        )
        self.assert_problem("duplicate summary finding V3-F1")

        _write_synthetic_bundle(self.root)
        _mutate_text(
            readme,
            lambda text: text.replace(
                "| V2-F1 | MINOR |", "| V2-F1 | MAJOR |", 1
            ),
        )
        self.assert_problem("V2-F1: README severity MAJOR differs")

    def test_broken_links_and_placeholders_are_rejected(self) -> None:
        readme = self.root / "README.md"
        _mutate_text(
            readme,
            lambda text: text.replace(
                "(01_build_integrity.md)", "(missing.md)", 1
            ),
        )
        self.assert_problem("does not resolve to 01_build_integrity.md")

        _write_synthetic_bundle(self.root)
        report = self.root / EXPECTED_REPORTS[9]
        _mutate_text(report, lambda text: text + "\nPENDING final edit\n")
        self.assert_problem("unresolved placeholder")

    def test_exact_report_and_index_coverage_is_required(self) -> None:
        (self.root / EXPECTED_REPORTS[8]).unlink()
        self.assert_problem("missing final report 08_linter_report.md")

        _write_synthetic_bundle(self.root)
        (self.root / "10_extra.md").write_text("# extra\n", encoding="utf-8")
        self.assert_problem("unexpected numbered report 10_extra.md")

        (self.root / "10_extra.md").unlink()
        readme = self.root / "README.md"
        text = readme.read_text(encoding="utf-8")
        row = next(line for line in text.splitlines() if line.startswith("| V4 |"))
        _mutate_text(
            readme, lambda value: value.replace(row, f"{row}\n{row}", 1)
        )
        self.assert_problem("duplicate verification index row V4")

    def test_embedded_self_calibration_passes(self) -> None:
        self.assertEqual(run_self_test(verbose=False), [])


if __name__ == "__main__":
    unittest.main()
