#!/usr/bin/env python3
"""Calibration/regression tests for the source V6 Tier-A scanner.

Only the planted file in ``.audit_work/verification`` is scanned here.  The
final FILE-WALK library scan must wait for V3/V4/V5 completion.
"""

from __future__ import annotations

import copy
import json
import tempfile
import unittest
from pathlib import Path

from file_universe import ROOT, enumerate_universe
from v6_tier_a_scanner import (
    AUTO_BOUND_REASON_ID,
    SourceDeclaration,
    apply_v4_auto_bound_triage,
    attach_v4_binders,
    attach_v4_types,
    extract_declarations,
    main,
    render_json,
    render_tsv,
    scan_paths,
    summary,
    validate_v4_join_contract,
)


CALIBRATION = (
    ROOT / ".audit_work" / "verification" / "RecertV6TierAPositive.lean"
)


class V6TierACalibrationTests(unittest.TestCase):
    @classmethod
    def setUpClass(cls) -> None:
        cls.declarations = scan_paths([CALIBRATION])
        joined_names = (
            "plantedAutoBoundSort",
            "plantedAutoBoundProp",
            "plantedExplicitSort",
            "plantedVariableProp",
            "plantedLongAutoBound",
        )
        attach_v4_types(
            cls.declarations,
            [
                {
                    "module": "",
                    "name": (
                        "VerificationV6TierAPositive."
                        + name
                    ),
                    "private_user_name": "",
                    "type_raw": "PLANTED_TYPE_RAW_MUST_NOT_BE_RETAINED",
                    "binder_count": "1",
                }
                for name in joined_names
            ],
        )
        binder_specs = (
            ("plantedAutoBoundSort", "A", "implicit",
             "Lean.Expr.sort (Lean.Level.succ (Lean.Level.zero))"),
            ("plantedAutoBoundProp", "p", "implicit",
             "Lean.Expr.sort (Lean.Level.zero)"),
            ("plantedExplicitSort", "B", "implicit",
             "Lean.Expr.sort (Lean.Level.succ (Lean.Level.zero))"),
            ("plantedVariableProp", "q", "implicit",
             "Lean.Expr.sort (Lean.Level.zero)"),
            ("plantedLongAutoBound", "Carrier", "implicit",
             "Lean.Expr.sort (Lean.Level.succ (Lean.Level.zero))"),
        )
        attach_v4_binders(
            cls.declarations,
            [
                {
                    "module": "",
                    "name": (
                        "VerificationV6TierAPositive."
                        + declaration_name
                    ),
                    "private_user_name": "",
                    "binder_index": "0",
                    "binder_name": binder_name,
                    "binder_info": binder_info,
                    "binder_type_raw": binder_type,
                }
                for (
                    declaration_name,
                    binder_name,
                    binder_info,
                    binder_type,
                ) in binder_specs
            ],
        )
        apply_v4_auto_bound_triage(cls.declarations)
        cls.by_name = {
            declaration.name: declaration for declaration in cls.declarations
        }

    def reasons(self, name: str) -> set[str]:
        return {
            reason.reason_id
            for reason in self.by_name[name].triage_reasons
        }

    def test_calibration_is_outside_library_universe(self) -> None:
        universe = enumerate_universe()["file_walk_universe"]
        self.assertNotIn(
            ".audit_work/verification/RecertV6TierAPositive.lean", universe
        )

    def test_complete_multiline_declaration_enumeration(self) -> None:
        self.assertEqual(len(self.declarations), 11)
        self.assertTrue(all(declaration.parsed for declaration in self.declarations))
        self.assertNotIn("fakeCommentedDeclaration", self.by_name)
        self.assertNotIn("fakeStringDeclaration", self.by_name)
        report = summary(
            self.declarations,
            scope="explicit-paths",
            scanned_file_count=1,
        )
        self.assertEqual(report["declaration_count"], 11)
        self.assertEqual(report["parsed_declaration_count"], 11)
        self.assertEqual(report["unparsed_declaration_count"], 0)

    def test_contradictory_numeric_calibration(self) -> None:
        self.assertIn(
            "contradictory_numeric_bounds",
            self.reasons("plantedContradictoryNumeric"),
        )

    def test_isempty_quantified_calibration(self) -> None:
        self.assertIn(
            "is_empty_domain", self.reasons("plantedIsEmptyQuantified")
        )

    def test_trivial_conclusion_calibrations(self) -> None:
        self.assertIn(
            "reflexive_equality_conclusion",
            self.reasons("plantedTrivialConclusion"),
        )
        self.assertIn(
            "top_upper_bound_conclusion",
            self.reasons("plantedTopConclusion"),
        )
        self.assertIn(
            "trivial_true_conclusion",
            self.reasons("plantedNestedAssignment"),
        )

    def test_nested_assignment_does_not_end_statement(self) -> None:
        declaration = self.by_name["plantedNestedAssignment"]
        self.assertIn("True", declaration.conclusion)
        self.assertIn("let f := fun x : Nat => x", declaration.statement)

    def test_negative_control_is_enumerated_unflagged(self) -> None:
        declaration = self.by_name["plantedSubstantiveControl"]
        self.assertTrue(declaration.parsed)
        self.assertFalse(declaration.triage_reasons)

    def test_v4_auto_bound_positive_calibrations(self) -> None:
        self.assertIn(AUTO_BOUND_REASON_ID, self.reasons("plantedAutoBoundSort"))
        self.assertIn(AUTO_BOUND_REASON_ID, self.reasons("plantedAutoBoundProp"))
        self.assertEqual(
            self.by_name["plantedAutoBoundSort"].auto_bound_candidates,
            ["A"],
        )
        self.assertEqual(
            self.by_name["plantedAutoBoundProp"].auto_bound_candidates,
            ["p"],
        )

    def test_v4_auto_bound_negative_calibrations(self) -> None:
        for name in (
            "plantedExplicitSort",
            "plantedVariableProp",
            "plantedLongAutoBound",
        ):
            self.assertNotIn(AUTO_BOUND_REASON_ID, self.reasons(name))
            self.assertFalse(self.by_name[name].auto_bound_candidates)
        self.assertIn(
            "B", self.by_name["plantedExplicitSort"].source_theorem_binders
        )
        self.assertIn(
            "q", self.by_name["plantedVariableProp"].source_variable_binders
        )

    def test_v4_type_tsv_join_contract(self) -> None:
        sentinel = "HUGE_TYPE_RAW_SENTINEL_MUST_NOT_APPEAR"
        declaration = SourceDeclaration(
            path="HighDimensionalProbability/Fake.lean",
            module="HighDimensionalProbability.Fake",
            kind="theorem",
            name="joined",
            start_line=1,
            end_line=1,
            parsed=True,
            statement="theorem joined : True",
            conclusion="True",
        )
        attach_v4_types(
            [declaration],
            [
                {
                    "module": "HighDimensionalProbability.Fake",
                    "name": "HDP.joined",
                    "private_user_name": "",
                    "type_raw": sentinel,
                }
            ],
        )
        self.assertEqual(declaration.v4_match_count, 1)
        self.assertEqual(declaration.v4_name, "HDP.joined")
        self.assertTrue(declaration.v4_type_present)
        report = summary(
            [declaration],
            scope="explicit-paths",
            scanned_file_count=1,
        )
        self.assertNotIn(sentinel, render_json(report, [declaration]))
        self.assertNotIn(sentinel, render_tsv([declaration]))

    def test_namespace_qualified_v4_join_disambiguates_duplicate_leaves(
        self,
    ) -> None:
        declarations = [
            SourceDeclaration(
                path="HighDimensionalProbability/Fake.lean",
                module="HighDimensionalProbability.Fake",
                kind="theorem",
                name="sameLeaf",
                source_namespace=namespace,
                start_line=index,
                end_line=index,
                parsed=True,
                statement="theorem sameLeaf : True",
                conclusion="True",
            )
            for index, namespace in enumerate(("HDP.Left", "HDP.Right"), 1)
        ]
        attach_v4_types(
            declarations,
            [
                {
                    "module": "HighDimensionalProbability.Fake",
                    "name": f"{namespace}.sameLeaf",
                    "private_user_name": "",
                    "type_raw": "Lean.Expr.const `True []",
                    "binder_count": "0",
                }
                for namespace in ("HDP.Left", "HDP.Right")
            ],
        )
        self.assertEqual(
            [row.v4_name for row in declarations],
            ["HDP.Left.sameLeaf", "HDP.Right.sameLeaf"],
        )
        self.assertTrue(all(row.v4_match_count == 1 for row in declarations))

    def test_equation_compiler_statement_boundary_regression(self) -> None:
        path = ROOT / "MatrixConcentration" / "Appendix_GoldenThompson.lean"
        declarations = extract_declarations(path)
        matches = [
            declaration
            for declaration in declarations
            if declaration.name == "exp_pow_nsmul"
        ]
        self.assertEqual(len(matches), 1)
        declaration = matches[0]
        self.assertTrue(declaration.parsed, declaration.parse_diagnostic)
        self.assertTrue(declaration.conclusion.startswith("∀ N : ℕ"))
        self.assertNotIn("| 0 =>", declaration.statement)
        self.assertNotIn("| N + 1 =>", declaration.statement)

    def test_absolute_value_is_not_an_equation_clause(self) -> None:
        path = (
            ROOT
            / "HighDimensionalProbability"
            / "Exercise"
            / "Chapter4"
            / "Sec01.lean"
        )
        declaration = next(
            item
            for item in extract_declarations(path)
            if item.name == "exercise_4_22_cut"
        )
        self.assertTrue(declaration.parsed, declaration.parse_diagnostic)
        self.assertTrue(declaration.conclusion.startswith("|∑ i"))
        self.assertIn(
            "| ≤ (1783 / 250 : ℝ) * C",
            declaration.conclusion,
        )

    def test_integral_absolute_value_is_not_an_equation_clause(self) -> None:
        path = (
            ROOT
            / "HighDimensionalProbability"
            / "Exercise"
            / "Chapter2"
            / "Sec07.lean"
        )
        declaration = next(
            item
            for item in extract_declarations(path)
            if item.name == "exercise_2_36b"
        )
        self.assertTrue(declaration.parsed, declaration.parse_diagnostic)
        self.assertEqual(declaration.conclusion.count("∫ ω"), 2)
        self.assertEqual(
            declaration.conclusion.count("|∑ i, a i * X i ω|"),
            2,
        )
        self.assertTrue(
            declaration.conclusion.endswith(
                "Real.sqrt (∑ i, a i ^ 2)"
            )
        )

    def test_rendering_is_deterministic_and_compact(self) -> None:
        report = summary(
            self.declarations,
            scope="explicit-paths",
            scanned_file_count=1,
        )
        self.assertEqual(
            render_json(report, self.declarations),
            render_json(report, self.declarations),
        )
        self.assertEqual(
            render_tsv(self.declarations),
            render_tsv(self.declarations),
        )
        rendered = render_json(report, self.declarations)
        self.assertNotIn("PLANTED_TYPE_RAW_MUST_NOT_BE_RETAINED", rendered)
        self.assertNotIn('"v4_type"', rendered)

    def test_cli_accepts_both_v4_metadata_paths(self) -> None:
        with tempfile.TemporaryDirectory() as temporary:
            directory = Path(temporary)
            types = directory / "types.tsv"
            binders = directory / "binders.tsv"
            output = directory / "report.json"
            oversized_type_raw = "CLI_TYPE_RAW_SENTINEL" + ("x" * 140_000)
            type_rows = []
            for declaration in self.declarations:
                qualified = ".".join(
                    part
                    for part in (
                        declaration.source_namespace,
                        declaration.name,
                    )
                    if part
                )
                binder_count = (
                    "1"
                    if declaration.name == "plantedAutoBoundSort"
                    else "0"
                )
                raw_type = (
                    oversized_type_raw
                    if declaration.name == "plantedAutoBoundSort"
                    else "Lean.Expr.const `True []"
                )
                type_rows.append(
                    f"\t{qualified}\t\t{binder_count}\t{raw_type}"
                )
            types.write_text(
                "module\tname\tprivate_user_name\tbinder_count\ttype_raw\n"
                + "\n".join(type_rows)
                + "\n",
                encoding="utf-8",
            )
            binders.write_text(
                "module\tname\tprivate_user_name\tbinder_index\t"
                "binder_name\tbinder_info\tbinder_type_raw\n"
                "\tVerificationV6TierAPositive.plantedAutoBoundSort\t"
                "\t0\tA\timplicit\t"
                "Lean.Expr.sort (Lean.Level.succ (Lean.Level.zero))\n",
                encoding="utf-8",
            )
            self.assertEqual(
                main(
                    [
                        "--path",
                        str(CALIBRATION),
                        "--v4-types-tsv",
                        str(types),
                        "--v4-binders-tsv",
                        str(binders),
                        "--require-complete-v4-join",
                        "--output",
                        str(output),
                    ]
                ),
                0,
            )
            data = json.loads(output.read_text(encoding="utf-8"))
            self.assertEqual(
                data["summary"]["v4_metadata"]["types_tsv"],
                types.as_posix(),
            )
            self.assertEqual(
                data["summary"]["v4_metadata"]["binders_tsv"],
                binders.as_posix(),
            )
            declaration = next(
                row
                for row in data["declarations"]
                if row["name"] == "plantedAutoBoundSort"
            )
            self.assertEqual(declaration["auto_bound_candidates"], ["A"])
            self.assertNotIn(
                "CLI_TYPE_RAW_SENTINEL",
                output.read_text(encoding="utf-8"),
            )
            compact = validate_v4_join_contract(
                data,
                expected_types_tsv=types.as_posix(),
                expected_binders_tsv=binders.as_posix(),
                expected_declaration_count=11,
            )
            self.assertEqual(compact["complete_binder_telescopes"], 11)
            self.assertEqual(compact["auto_bound_candidate_count"], 1)

            zero_consistent = copy.deepcopy(data)
            for row in zero_consistent["declarations"]:
                row["auto_bound_candidates"] = []
                row["triage_reasons"] = [
                    reason
                    for reason in row["triage_reasons"]
                    if reason.get("reason_id") != AUTO_BOUND_REASON_ID
                ]
            zero_consistent["summary"]["v4_metadata"][
                "auto_bound_candidate_count"
            ] = 0
            zero_consistent["summary"]["reason_counts"].pop(
                AUTO_BOUND_REASON_ID, None
            )
            compact_zero = validate_v4_join_contract(
                zero_consistent,
                expected_types_tsv=types.as_posix(),
                expected_binders_tsv=binders.as_posix(),
                expected_declaration_count=11,
            )
            self.assertEqual(compact_zero["auto_bound_candidate_count"], 0)
            self.assertEqual(
                compact_zero["auto_bound_flagged_declaration_count"], 0
            )

            stale_metadata = copy.deepcopy(zero_consistent)
            stale_metadata["summary"]["v4_metadata"][
                "auto_bound_candidate_count"
            ] = 1
            with self.assertRaisesRegex(
                ValueError, "summary auto-bound candidate count is stale"
            ):
                validate_v4_join_contract(
                    stale_metadata,
                    expected_types_tsv=types.as_posix(),
                    expected_binders_tsv=binders.as_posix(),
                    expected_declaration_count=11,
                )

            stale_reason_total = copy.deepcopy(zero_consistent)
            stale_reason_total["summary"]["reason_counts"][
                AUTO_BOUND_REASON_ID
            ] = 1
            with self.assertRaisesRegex(
                ValueError, "summary auto-bound reason count is stale"
            ):
                validate_v4_join_contract(
                    stale_reason_total,
                    expected_types_tsv=types.as_posix(),
                    expected_binders_tsv=binders.as_posix(),
                    expected_declaration_count=11,
                )

            row_mismatch = copy.deepcopy(zero_consistent)
            row_mismatch["declarations"][0][
                "auto_bound_candidates"
            ] = ["A"]
            with self.assertRaisesRegex(
                ValueError, "auto-bound candidate/reason mismatch"
            ):
                validate_v4_join_contract(
                    row_mismatch,
                    expected_types_tsv=types.as_posix(),
                    expected_binders_tsv=binders.as_posix(),
                    expected_declaration_count=11,
                )

    def test_all_tier_c_runners_require_the_v4_join_contract(self) -> None:
        scripts = ROOT / "HighDimensionalProbability" / "Verification" / "scripts"
        for filename in (
            "run_v6_tier_c_ch0_4.py",
            "run_v6_tier_c_ch5_7.py",
            "run_v6_tier_c_ch8_9.py",
        ):
            source = (scripts / filename).read_text(encoding="utf-8")
            with self.subTest(filename=filename):
                self.assertIn('"--v4-types-tsv"', source)
                self.assertIn('"--v4-binders-tsv"', source)
                self.assertIn("validate_v4_join_contract(", source)
                self.assertIn(
                    "expected_declaration_count="
                    "EXPECTED_TIER_A_DECLARATION_COUNT",
                    source,
                )


if __name__ == "__main__":
    unittest.main(verbosity=2)
