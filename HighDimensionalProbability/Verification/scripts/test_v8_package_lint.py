#!/usr/bin/env python3
"""Static and planted-log tests for the deferred V8 lint pass.

These tests never invoke Lean or Lake.  They validate the exact harness
surface, runner command construction, multiline Batteries output parsing,
nonzero-on-hit semantics, and the count-in-thousands coverage gate.
"""

from __future__ import annotations

import unittest

from file_universe import ROOT
from run_v8_package_lint import (
    FAILED_ORPHAN_IMPORTS,
    FULL_SURFACE_HARNESS,
    FULL_SURFACE_IMPORTS,
    HARNESS,
    REQUIRED_IMPORTS,
    build_lean_command,
    validate_all_harnesses,
    validate_harness,
    validate_v2_orphan_evidence,
)
from v8_lint_parser import (
    EXPECTED_PACKAGES,
    FULL_SURFACE_HARNESS_REL,
    MAXIMAL_HARNESS_REL,
    REQUIRED_D_FLAGS,
    parse_lint_log,
    render_tsv,
)


CALIBRATION = (
    ROOT
    / ".audit_work"
    / "verification"
    / "v8_package_lint_calibration.log"
)


class V8PackageLintTests(unittest.TestCase):
    @classmethod
    def setUpClass(cls) -> None:
        cls.text = CALIBRATION.read_text(encoding="utf-8").replace(
            ".audit_work/verification/V8PackageLint.lean",
            MAXIMAL_HARNESS_REL,
        )
        cls.report = parse_lint_log(
            cls.text,
            log_path=".audit_work/verification/v8_package_lint_calibration.log",
        )
        cls.by_package = {
            package.package: package for package in cls.report.packages
        }

    def test_current_harness_has_exact_full_surface(self) -> None:
        self.assertEqual(validate_harness(HARNESS), [])
        code = HARNESS.read_text(encoding="utf-8")
        for module in REQUIRED_IMPORTS:
            self.assertIn(f"import {module}\n", code)
        for module in FAILED_ORPHAN_IMPORTS:
            self.assertNotIn(f"import {module}\n", code)
        self.assertEqual(tuple(self.by_package), EXPECTED_PACKAGES)

    def test_full_surface_alias_is_the_current_harness(self) -> None:
        self.assertEqual(validate_harness(FULL_SURFACE_HARNESS), [])
        self.assertEqual(validate_all_harnesses(), [])
        code = FULL_SURFACE_HARNESS.read_text(encoding="utf-8")
        for module in FULL_SURFACE_IMPORTS:
            self.assertIn(f"import {module}\n", code)
        self.assertEqual(validate_v2_orphan_evidence(), [])

    def test_runner_uses_required_D_flags(self) -> None:
        command = build_lean_command()
        self.assertEqual(command[:3], ["lake", "env", "lean"])
        for flag in REQUIRED_D_FLAGS:
            self.assertIn(flag, command)
        self.assertEqual(
            command[-1], MAXIMAL_HARNESS_REL
        )
        self.assertEqual(
            build_lean_command(FULL_SURFACE_HARNESS)[-1],
            FULL_SURFACE_HARNESS_REL,
        )

    def test_current_log_is_structurally_valid_and_complete(self) -> None:
        self.assertTrue(self.report.gate_passed, self.report.diagnostics)
        self.assertEqual(self.report.surface_profile, "full-physical-surface")
        self.assertTrue(self.report.coverage_complete)
        self.assertEqual(self.report.overall_status, "PASS")
        self.assertEqual(self.report.excluded_modules, ())

    def test_full_surface_compatibility_profile_is_complete(self) -> None:
        full = parse_lint_log(
            self.text.replace(
                MAXIMAL_HARNESS_REL, FULL_SURFACE_HARNESS_REL, 1
            )
        )
        self.assertTrue(full.gate_passed, full.diagnostics)
        self.assertEqual(full.surface_profile, "full-physical-surface")
        self.assertTrue(full.coverage_complete)
        self.assertEqual(full.overall_status, "PASS")
        self.assertEqual(full.excluded_modules, ())

    def test_multiline_summaries_and_thousands_gate(self) -> None:
        self.assertTrue(self.report.gate_passed, self.report.diagnostics)
        hdp = self.by_package["HighDimensionalProbability"]
        matrix = self.by_package["MatrixConcentration"]
        self.assertEqual(hdp.declarations_examined, 3142)
        self.assertEqual(hdp.automatically_generated, 517)
        self.assertEqual(matrix.declarations_examined, 1876)
        self.assertEqual(matrix.automatically_generated, 293)
        self.assertGreaterEqual(hdp.declarations_examined, 1000)
        self.assertGreaterEqual(matrix.declarations_examined, 1000)

    def test_linter_and_module_hit_inventory(self) -> None:
        hdp = self.by_package["HighDimensionalProbability"]
        matrix = self.by_package["MatrixConcentration"]
        self.assertEqual(hdp.found_errors, 3)
        self.assertEqual(len(hdp.hits), 3)
        self.assertEqual(
            hdp.linter_hit_counts(), {"docBlame": 2, "unusedArguments": 1}
        )
        self.assertEqual(
            hdp.module_hit_counts(),
            {
                "HighDimensionalProbability.Appendix.BrownianReflection": 1,
                "HighDimensionalProbability.Chapter1.Basic": 2,
            },
        )
        self.assertEqual(matrix.found_errors, 1)
        self.assertEqual(
            matrix.linter_module_hit_counts(),
            {
                "unusedArguments": {
                    "MatrixConcentration.Chapter7_IntrinsicDimension": 1
                }
            },
        )

    def test_fake_hits_inside_warning_comment_are_ignored(self) -> None:
        declarations = {
            hit.declaration
            for package in self.report.packages
            for hit in package.hits
        }
        modules = {
            hit.module
            for package in self.report.packages
            for hit in package.hits
        }
        self.assertNotIn("fakeInsideWarning", declarations)
        self.assertNotIn("MatrixConcentration.FakeInsideWarning", modules)

    def test_expected_nonzero_exit_is_not_a_gate_failure(self) -> None:
        self.assertEqual(self.report.exit_code, 1)
        self.assertGreater(self.report.total_errors, 0)
        self.assertTrue(self.report.gate_passed)
        inconsistent = parse_lint_log(
            self.text.replace("exit_code: 1", "exit_code: 0")
        )
        self.assertFalse(inconsistent.gate_passed)
        self.assertTrue(
            any(
                "expected linter-error code 1" in item
                for item in inconsistent.diagnostics
            )
        )

    def test_below_one_thousand_is_rejected(self) -> None:
        report = parse_lint_log(
            self.text.replace(
                "1,876 declarations", "999 declarations", 1
            )
        )
        self.assertFalse(report.gate_passed)
        self.assertTrue(
            any(
                "MatrixConcentration: examined only 999" in item
                for item in report.diagnostics
            )
        )

    def test_missing_D_flag_is_rejected(self) -> None:
        report = parse_lint_log(
            self.text.replace("-DwarningAsError=false ", "", 1)
        )
        self.assertFalse(report.gate_passed)
        self.assertTrue(
            any(
                "-DwarningAsError=false" in item
                for item in report.diagnostics
            )
        )

    def test_non_lint_error_is_rejected(self) -> None:
        report = parse_lint_log(
            self.text
            + "\nUnexpected.lean:1:0: error: unknown declaration `boom`\n"
        )
        self.assertFalse(report.gate_passed)
        self.assertTrue(
            any("non-lint Lean error" in item for item in report.diagnostics)
        )

    def test_zero_hit_success_exit_is_accepted(self) -> None:
        command = " ".join(
            [
                "command: lake env lean",
                *REQUIRED_D_FLAGS,
                MAXIMAL_HARNESS_REL,
            ]
        )
        text = "\n".join(
            (
                command,
                "-- Found 0 errors in 2,001 declarations "
                "(plus 101 automatically generated ones) in "
                "HighDimensionalProbability with 12 linters",
                "-- Found 0 errors in 1,001 declarations "
                "(plus 51 automatically generated ones) in "
                "MatrixConcentration with 12 linters",
                "exit_code: 0",
                "",
            )
        )
        report = parse_lint_log(text)
        self.assertTrue(report.gate_passed, report.diagnostics)
        self.assertEqual(report.total_hits, 0)
        self.assertEqual(report.overall_status, "PASS")

    def test_tsv_has_one_row_per_hit(self) -> None:
        rows = render_tsv(self.report).splitlines()
        self.assertEqual(len(rows), 1 + self.report.total_hits)
        self.assertEqual(
            rows[0], "package\tlinter\tmodule\tdeclaration\tlog_line"
        )


if __name__ == "__main__":
    unittest.main(verbosity=2)
