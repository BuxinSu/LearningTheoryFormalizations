#!/usr/bin/env python3
"""Calibration and regression tests for the reusable V3/V5 scanners.

This test intentionally scans only planted files in
``.audit_work/verification``.  It does not execute the final V3 or V5 library
audits, which must wait for V2's import classification.
"""

from __future__ import annotations

import unittest

from file_universe import ROOT, enumerate_universe
from lean_source_scanner import mask_lean_noncode, scan_paths, scan_text
from scanner_profiles import V3_PATTERNS, V5_PATTERNS


POSITIVE = (
    ROOT
    / ".audit_work"
    / "verification"
    / "RecertV3V5ScannerPositive.lean"
)
NONCODE = (
    ROOT
    / ".audit_work"
    / "verification"
    / "RecertV3V5ScannerNoncode.lean"
)
KNOWN_EXERCISE_SORRY = (
    ROOT
    / "HighDimensionalProbability"
    / "Exercise"
    / "Chapter1"
    / "Sec01.lean"
)
CURRENT_GAUSSIAN_CHEVET = (
    ROOT
    / "HighDimensionalProbability"
    / "Chapter8_Chaining.lean"
)
DELETED_GAUSSIAN_CHEVET = (
    ROOT
    / "HighDimensionalProbability"
    / "Appendix"
    / "GaussianChevet.lean"
)


def counts(hits: list[object]) -> dict[str, tuple[int, int]]:
    result: dict[str, tuple[int, int]] = {}
    for pattern_id in {getattr(hit, "pattern_id") for hit in hits}:
        matching = [hit for hit in hits if getattr(hit, "pattern_id") == pattern_id]
        result[pattern_id] = (
            len(matching),
            sum(bool(getattr(hit, "in_code")) for hit in matching),
        )
    return result


class ScannerCalibrationTests(unittest.TestCase):
    def test_file_walk_rules_include_real_mc_and_exclude_audit_artifacts(self) -> None:
        universe = enumerate_universe()
        library = list(universe["file_walk_universe"])
        self.assertEqual(len(library), len(set(library)))
        self.assertEqual(
            sum(path.startswith("MatrixConcentration/") for path in library),
            10,
        )
        self.assertFalse(
            any(path.startswith("Pre_MatrixConcentration/") for path in library)
        )
        self.assertFalse(any("/Verification/" in path for path in library))
        self.assertNotIn(
            ".audit_work/verification/RecertV3V5ScannerPositive.lean", library
        )
        self.assertNotIn(
            ".audit_work/verification/RecertV3V5ScannerNoncode.lean", library
        )
        hits, diagnostics = scan_paths(
            profile="V5",
            paths=[ROOT / "MatrixConcentration" / "Prelude.lean"],
            patterns=V5_PATTERNS,
        )
        self.assertFalse(diagnostics)
        self.assertIsInstance(hits, list)

    def test_nested_comments_and_strings_are_offset_preserving(self) -> None:
        source = (
            'def before := "sorry /- axiom -/"\n'
            "/- outer native_decide /- nested run_cmd -/ unsafe -/\n"
            "theorem after : True := by sorry\n"
        )
        masked, diagnostics = mask_lean_noncode(source)
        self.assertEqual(len(source), len(masked))
        self.assertEqual(source.count("\n"), masked.count("\n"))
        self.assertFalse(diagnostics)
        self.assertEqual(masked.count("sorry"), 1)
        self.assertNotIn("native_decide", masked)
        self.assertNotIn("run_cmd", masked)

    def test_v3_positive_calibration(self) -> None:
        hits, diagnostics = scan_paths(
            profile="V3", paths=[POSITIVE], patterns=V3_PATTERNS
        )
        self.assertFalse(diagnostics)
        measured = counts(hits)
        for pattern_id in (
            "v3.sorry",
            "v3.admit",
            "v3.sorryAx",
            "v3.proof_wanted",
            "v3.exit",
            "v3.stop",
        ):
            self.assertGreaterEqual(
                measured.get(pattern_id, (0, 0))[1],
                1,
                f"missing planted executable calibration for {pattern_id}",
            )
        for pattern_id in (
            "v3.todo",
            "v3.wip",
            "v3.exercise_sorry_marker",
            "v3.appendix_unresolved_marker",
            "v3.external_sorry_marker",
            "v3.forward_sorry_marker",
            "v3.unresolved_proof_marker",
        ):
            self.assertGreaterEqual(
                measured.get(pattern_id, (0, 0))[0],
                1,
                f"missing planted raw calibration for {pattern_id}",
            )

    def test_v3_current_tree_known_positive_and_stale_seed(self) -> None:
        self.assertFalse(
            DELETED_GAUSSIAN_CHEVET.exists(),
            "the removed GaussianChevet Appendix module reappeared",
        )
        exercise_hits, diagnostics = scan_paths(
            profile="V3",
            paths=[KNOWN_EXERCISE_SORRY],
            patterns=V3_PATTERNS,
        )
        self.assertFalse(diagnostics)
        live_sorries = [
            hit
            for hit in exercise_hits
            if hit.pattern_id == "v3.sorry" and hit.in_code
        ]
        self.assertEqual(
            [(hit.line, hit.column) for hit in live_sorries],
            [(37, 3)],
            "the current-tree known Exercise sorry calibration drifted",
        )

        chevet_hits, diagnostics = scan_paths(
            profile="V3",
            paths=[CURRENT_GAUSSIAN_CHEVET],
            patterns=V3_PATTERNS,
        )
        self.assertFalse(diagnostics)
        self.assertFalse(
            [
                hit
                for hit in chevet_hits
                if hit.pattern_id in {"v3.sorry", "v3.admit", "v3.sorryAx"}
                and hit.in_code
            ],
            "the adapted current-tree Gaussian Chevet theorem must be proved",
        )

    def test_v5_positive_calibration(self) -> None:
        hits, diagnostics = scan_paths(
            profile="V5", paths=[POSITIVE], patterns=V5_PATTERNS
        )
        self.assertFalse(diagnostics)
        measured = counts(hits)
        required = {pattern.pattern_id for pattern in V5_PATTERNS}
        missing = sorted(
            pattern_id
            for pattern_id in required
            if measured.get(pattern_id, (0, 0))[1] < 1
        )
        self.assertFalse(
            missing,
            "missing planted executable V5 calibrations: " + ", ".join(missing),
        )
        for minimum in (
            "v5.native_decide",
            "v5.axiom",
            "v5.unsafe",
            "v5.run_cmd",
        ):
            self.assertGreaterEqual(measured[minimum][1], 1)

    def test_noncode_calibration_has_raw_but_no_code_hits(self) -> None:
        for profile, patterns in (("V3", V3_PATTERNS), ("V5", V5_PATTERNS)):
            with self.subTest(profile=profile):
                hits, diagnostics = scan_paths(
                    profile=profile, paths=[NONCODE], patterns=patterns
                )
                self.assertFalse(diagnostics)
                self.assertGreater(len(hits), 0)
                self.assertEqual(
                    sum(hit.in_code for hit in hits),
                    0,
                    "comment/string calibration leaked into executable hits",
                )

    def test_lexer_diagnostic_is_reported(self) -> None:
        _, diagnostics = scan_text(
            profile="V3",
            relative_path="<planted-unterminated>",
            text="/- planted unterminated comment",
            patterns=V3_PATTERNS,
        )
        self.assertEqual(len(diagnostics), 1)
        self.assertEqual(diagnostics[0].kind, "unterminated_block_comment")


if __name__ == "__main__":
    unittest.main(verbosity=2)
