#!/usr/bin/env python3
"""Static tests for the V7 load-bearing definition review framework."""

from __future__ import annotations

import csv
import sys
import tempfile
import unittest
from pathlib import Path

SCRIPT_DIR = Path(__file__).resolve().parent
if str(SCRIPT_DIR) not in sys.path:
    sys.path.insert(0, str(SCRIPT_DIR))

import v7_definition_review as review_module
from v7_definition_review import (
    ALLOWED_AXIOMS,
    REVIEW_COLUMNS,
    WITNESS_EVIDENCE_COLUMNS,
    _read_tsv,
    _synthetic_inputs,
    _write_tsv,
    prepare,
    self_test,
    validate,
)


class V7DefinitionReviewTests(unittest.TestCase):
    def setUp(self) -> None:
        self.temporary = tempfile.TemporaryDirectory(
            prefix="hdp-v7-review-test-"
        )
        self.root = Path(self.temporary.name)
        self.original_project_root = review_module.ROOT
        review_module.ROOT = self.root
        citation_source = (
            self.root
            / "HighDimensionalProbability"
            / "Chapter1_AnalysisAndProbabilityRefresher.lean"
        )
        citation_source.parent.mkdir(parents=True)
        citation_source.write_text(
            "theorem syntheticThresholdDef_eq : True := True.intro\n"
            "def unrelatedAnchor : Nat := 0\n",
            encoding="utf-8",
        )
        self.load, self.candidates = _synthetic_inputs(self.root)
        self.review = self.root / "review"
        prepare(
            load_path=self.load,
            candidates_path=self.candidates,
            output_dir=self.review,
            shard_count=2,
            force=False,
        )

    def tearDown(self) -> None:
        review_module.ROOT = self.original_project_root
        self.temporary.cleanup()

    def check(self, *, final: bool = False):
        return validate(
            load_path=self.load,
            candidates_path=self.candidates,
            review_dir=self.review,
            v4_path=self.root / "v4.tsv",
            witness_evidence_path=self.root / "witness.tsv",
            require_final=final,
        )

    def find_row(self, name: str) -> tuple[Path, list[dict[str, str]], dict[str, str]]:
        for path in sorted(
            self.review.glob("v7_definition_review_shard_*.tsv")
        ):
            rows = _read_tsv(path, REVIEW_COLUMNS)
            for row in rows:
                if row["name"] == name:
                    return path, rows, row
        raise AssertionError(name)

    def test_complete_unreviewed_scaffold_is_valid_but_not_final(self) -> None:
        result = self.check()
        self.assertTrue(result.passed, result.problems)
        self.assertFalse(result.final_ready)
        final = self.check(final=True)
        self.assertFalse(final.passed)
        self.assertTrue(
            any(
                "final validation forbids UNREVIEWED" in problem
                for problem in final.problems
            )
        )

    def test_candidate_is_not_automatically_evidence(self) -> None:
        path, rows, row = self.find_row("HDP.syntheticThresholdDef")
        row["review_status"] = "VERIFIED_CITATION"
        row["evidence_method"] = "citation"
        row["evidence_name"] = "HDP.syntheticThresholdDef_eq"
        _write_tsv(path, REVIEW_COLUMNS, rows)
        result = self.check()
        self.assertFalse(result.passed)
        self.assertTrue(
            any(
                "required review fields are empty" in problem
                for problem in result.problems
            )
        )
        self.assertTrue(
            any("missing V4 evidence" in problem for problem in result.problems)
        )

    def test_verified_citation_requires_semantics_and_clean_v4(self) -> None:
        path, rows, row = self.find_row("HDP.syntheticThresholdDef")
        row.update(
            {
                "review_status": "VERIFIED_CITATION",
                "evidence_method": "citation",
                "evidence_name": "HDP.syntheticThresholdDef_eq",
                "evidence_location": (
                    "HighDimensionalProbability/"
                    "Chapter1_AnalysisAndProbabilityRefresher.lean:1"
                ),
                "evidence_axioms": ";".join(sorted(ALLOWED_AXIOMS)),
                "semantic_nontriviality_claim": "The equality fixes a nonzero value.",
                "nondegenerate_model": "A one-dimensional nonzero input.",
                "constant_or_zero_collapse_check": "The exact value is nonzero.",
                "junk_or_empty_boundary_check": "The index is Fin 1.",
                "measure_or_typeclass_check": "No degenerate typeclass is used.",
                "review_rationale": "The cited statement would fail for the zero definition.",
                "reviewer": "synthetic-reviewer",
                "review_date": "2026-07-18",
            }
        )
        _write_tsv(path, REVIEW_COLUMNS, rows)

        def write_v4(axioms: str) -> None:
            with (self.root / "v4.tsv").open(
                "w", encoding="utf-8", newline=""
            ) as handle:
                writer = csv.DictWriter(
                    handle,
                    fieldnames=("module", "name", "kind", "axioms"),
                    delimiter="\t",
                    lineterminator="\n",
                )
                writer.writeheader()
                writer.writerow(
                    {
                        "module": (
                            "HighDimensionalProbability."
                            "Chapter1_AnalysisAndProbabilityRefresher"
                        ),
                        "name": "HDP.syntheticThresholdDef_eq",
                        "kind": "theorem",
                        "axioms": axioms,
                    }
                )

        write_v4(";".join(sorted(ALLOWED_AXIOMS)))
        result = self.check()
        self.assertTrue(result.passed, result.problems)

        row["evidence_axioms"] = "(none)"
        _write_tsv(path, REVIEW_COLUMNS, rows)
        write_v4("")
        constructive = self.check()
        self.assertTrue(constructive.passed, constructive.problems)

        row["evidence_location"] = (
            "HighDimensionalProbability/"
            "Chapter1_AnalysisAndProbabilityRefresher.lean:2"
        )
        _write_tsv(path, REVIEW_COLUMNS, rows)
        wrong_anchor = self.check()
        self.assertFalse(wrong_anchor.passed)
        self.assertTrue(
            any(
                "does not anchor the named declaration" in problem
                for problem in wrong_anchor.problems
            )
        )

        row["evidence_location"] = (
            "HighDimensionalProbability/"
            "Chapter1_AnalysisAndProbabilityRefresher.lean:1"
        )
        row["evidence_axioms"] = ";".join(
            sorted((ALLOWED_AXIOMS - {"Quot.sound"}) | {"sorryAx"})
        )
        _write_tsv(path, REVIEW_COLUMNS, rows)
        write_v4(row["evidence_axioms"])
        rejected = self.check()
        self.assertFalse(rejected.passed)
        self.assertTrue(
            any("disallowed axioms" in problem for problem in rejected.problems)
        )

    def test_missing_or_duplicate_load_bearing_rows_are_rejected(self) -> None:
        path, rows, _ = self.find_row("HDP.syntheticThresholdDef")
        _write_tsv(path, REVIEW_COLUMNS, rows[:-1])
        missing = self.check()
        self.assertFalse(missing.passed)
        self.assertTrue(
            any(
                "shard/load-bearing coverage mismatch" in problem
                for problem in missing.problems
            )
        )

        prepare(
            load_path=self.load,
            candidates_path=self.candidates,
            output_dir=self.review,
            shard_count=2,
            force=True,
        )
        path, rows, row = self.find_row("HDP.syntheticThresholdDef")
        _write_tsv(path, REVIEW_COLUMNS, [*rows, row])
        duplicate = self.check()
        self.assertFalse(duplicate.passed)
        self.assertTrue(
            any(
                "review shards duplicate review_id" in problem
                for problem in duplicate.problems
            )
        )

    def test_rows_must_remain_in_their_declared_physical_shard(self) -> None:
        paths = sorted(
            self.review.glob("v7_definition_review_shard_*.tsv")
        )
        self.assertEqual(len(paths), 2)
        first = _read_tsv(paths[0], REVIEW_COLUMNS)
        second = _read_tsv(paths[1], REVIEW_COLUMNS)
        self.assertTrue(first and second)
        _write_tsv(paths[0], REVIEW_COLUMNS, second)
        _write_tsv(paths[1], REVIEW_COLUMNS, first)
        result = self.check()
        self.assertFalse(result.passed)
        self.assertTrue(
            any(
                "declares shard" in problem
                for problem in result.problems
            )
        )

    def test_grouped_findings_and_status_fields_are_fail_closed(self) -> None:
        paths = sorted(
            self.review.glob("v7_definition_review_shard_*.tsv")
        )
        edited = 0
        for path in paths:
            rows = _read_tsv(path, REVIEW_COLUMNS)
            for row in rows:
                if edited >= 2:
                    break
                row.update(
                    {
                        "review_status": "UNVERIFIED_SANITY",
                        "evidence_method": "none",
                        "finding_id": "V7-F1",
                        "finding_severity": (
                            "MAJOR" if edited == 0 else "MINOR"
                        ),
                        "blocker": (
                            "first blocker" if edited == 0 else "second blocker"
                        ),
                        "review_rationale": "No acceptable evidence exists.",
                        "reviewer": "synthetic-reviewer",
                        "review_date": "2026-07-18",
                    }
                )
                edited += 1
            _write_tsv(path, REVIEW_COLUMNS, rows)
        self.assertEqual(edited, 2)
        grouped = self.check()
        self.assertFalse(grouped.passed)
        self.assertTrue(
            any(
                "grouped finding rows have inconsistent severities" in problem
                for problem in grouped.problems
            )
        )
        self.assertTrue(
            any(
                "grouped finding rows have inconsistent blockers" in problem
                for problem in grouped.problems
            )
        )

        prepare(
            load_path=self.load,
            candidates_path=self.candidates,
            output_dir=self.review,
            shard_count=2,
            force=True,
        )
        path, rows, row = self.find_row("HDP.syntheticPreludeDef")
        row.update(
            {
                "review_status": "UNVERIFIED_SANITY",
                "evidence_method": "none",
                "evidence_name": "staleWitness",
                "finding_id": "V7-F1",
                "finding_severity": "MAJOR",
                "blocker": "No acceptable evidence exists.",
                "review_rationale": "The row remains unverified.",
                "reviewer": "synthetic-reviewer",
                "review_date": "2026-07-18",
            }
        )
        _write_tsv(path, REVIEW_COLUMNS, rows)
        stale = self.check()
        self.assertFalse(stale.passed)
        self.assertTrue(
            any(
                "status-inapplicable fields must be empty" in problem
                for problem in stale.problems
            )
        )

    def test_witness_requires_clean_source_and_independent_evidence(self) -> None:
        source_relative = (
            "HighDimensionalProbability/Verification/scripts/witnesses/"
            "SyntheticDefinitionWitness.lean"
        )
        log_relative = (
            "HighDimensionalProbability/Verification/logs/"
            "synthetic_definition_witness.log"
        )
        collector_source_relative = (
            ".audit_work/verification/SyntheticDefinitionWitnessAxioms.lean"
        )
        collector_log_relative = (
            "HighDimensionalProbability/Verification/logs/"
            "synthetic_definition_witness_axioms.log"
        )
        source = self.root / source_relative
        build_log = self.root / log_relative
        collector_source = self.root / collector_source_relative
        collector_log = self.root / collector_log_relative
        source.parent.mkdir(parents=True)
        build_log.parent.mkdir(parents=True)
        collector_source.parent.mkdir(parents=True)
        source.write_text(
            "set_option autoImplicit false\n"
            "theorem syntheticPreludeDef_witness : "
            "HDP.syntheticPreludeDef = HDP.syntheticPreludeDef := rfl\n"
            "def unrelatedWitnessAnchor : Nat := 0\n",
            encoding="utf-8",
        )
        collector_source.write_text(
            "import Lean\n"
            "import HighDimensionalProbability.Verification.scripts."
            "witnesses.SyntheticDefinitionWitness\n"
            "set_option autoImplicit false\n"
            "open Lean\n"
            "run_cmd do\n"
            "  let _ := collectAxioms `syntheticPreludeDef_witness\n"
            "  let _ := (← getEnv).constants.toList[0]!.2.type.getUsedConstants\n"
            "  IO.println \"V7_WITNESS_COLLECTOR\\t"
            "syntheticPreludeDef_witness\"\n",
            encoding="utf-8",
        )

        def completed_log(
            command_source: str, body: str = ""
        ) -> str:
            middle = body.rstrip("\n")
            return (
                "started: 2026-07-18T00:00:00+00:00\n"
                f"cwd: {self.root}\n"
                f"command: /tmp/lake env lean {command_source}\n"
                "\n"
                f"{middle}\n"
                "\n"
                "finished: 2026-07-18T00:00:01+00:00\n"
                "elapsed_seconds: 1.000\n"
                "exit_code: 0\n"
            )

        build_log.write_text(
            completed_log(source_relative), encoding="utf-8"
        )
        collector_row = (
            "V7_WITNESS_COLLECTOR\t"
            "HighDimensionalProbability.Verification.scripts.witnesses."
            "SyntheticDefinitionWitness\t"
            "syntheticPreludeDef_witness\ttheorem\t\t\t"
            "HDP.syntheticPreludeDef"
        )
        unrelated_collector_row = (
            "V7_WITNESS_COLLECTOR\t"
            "HighDimensionalProbability.Verification.scripts.witnesses."
            "SyntheticDefinitionWitness\t"
            "unrelatedWitnessAnchor\tdefinition\t\t\tNat"
        )
        collector_log.write_text(
            completed_log(
                collector_source_relative,
                f"{unrelated_collector_row}\n{collector_row}",
            ),
            encoding="utf-8",
        )
        _write_tsv(
            self.root / "witness.tsv",
            WITNESS_EVIDENCE_COLUMNS,
            [
                {
                    "definition": "HDP.syntheticPreludeDef",
                    "witness": "syntheticPreludeDef_witness",
                    "witness_module": (
                        "HighDimensionalProbability.Verification.scripts."
                        "witnesses.SyntheticDefinitionWitness"
                    ),
                    "source_path": source_relative,
                    "build_log": log_relative,
                    "collector_source": collector_source_relative,
                    "collector_log": collector_log_relative,
                }
            ],
        )
        path, rows, row = self.find_row("HDP.syntheticPreludeDef")
        row.update(
            {
                "review_status": "VERIFIED_WITNESS",
                "evidence_method": "compiled_named_witness",
                "evidence_name": "syntheticPreludeDef_witness",
                "evidence_location": f"{source_relative}:2",
                "evidence_axioms": "(none)",
                "semantic_nontriviality_claim": "The witness has a nonzero value.",
                "nondegenerate_model": "A concrete synthetic input.",
                "constant_or_zero_collapse_check": "The value is not zero.",
                "junk_or_empty_boundary_check": "The input domain is inhabited.",
                "measure_or_typeclass_check": "No degenerate instance is used.",
                "review_rationale": "A zero definition cannot satisfy this value.",
                "witness_evidence_key": (
                    "HDP.syntheticPreludeDef|syntheticPreludeDef_witness"
                ),
                "reviewer": "synthetic-reviewer",
                "review_date": "2026-07-18",
            }
        )
        _write_tsv(path, REVIEW_COLUMNS, rows)
        accepted = self.check()
        self.assertTrue(accepted.passed, accepted.problems)

        collector_log.write_text(
            completed_log(
                collector_source_relative,
                f"{collector_row}\n{collector_row}",
            ),
            encoding="utf-8",
        )
        duplicate_witness_row = self.check()
        self.assertFalse(duplicate_witness_row.passed)
        self.assertTrue(
            any(
                "collector contains duplicate witness rows" in problem
                for problem in duplicate_witness_row.problems
            ),
            duplicate_witness_row.problems,
        )
        collector_log.write_text(
            completed_log(
                collector_source_relative,
                f"{unrelated_collector_row}\n{collector_row}",
            ),
            encoding="utf-8",
        )

        row["evidence_location"] = f"{source_relative}:3"
        _write_tsv(path, REVIEW_COLUMNS, rows)
        wrong_witness_anchor = self.check()
        self.assertFalse(wrong_witness_anchor.passed)
        self.assertTrue(
            any(
                "does not anchor the named declaration" in problem
                for problem in wrong_witness_anchor.problems
            )
        )
        row["evidence_location"] = f"{source_relative}:2"
        _write_tsv(path, REVIEW_COLUMNS, rows)

        source.write_text(
            "set_option autoImplicit false\n"
            "theorem syntheticPreludeDef_witness : "
            "HDP.syntheticPreludeDef = HDP.syntheticPreludeDef := by sorry\n",
            encoding="utf-8",
        )
        rejected = self.check()
        self.assertFalse(rejected.passed)
        self.assertTrue(
            any(
                "witness source contains executable sorry/admit/sorryAx"
                in problem
                for problem in rejected.problems
            )
        )

        source.write_text(
            "set_option autoImplicit false\n"
            "theorem syntheticPreludeDef_witness : "
            "HDP.syntheticPreludeDef = HDP.syntheticPreludeDef := rfl\n"
            "def unrelatedWitnessAnchor : Nat := 0\n",
            encoding="utf-8",
        )
        collector_log.write_text(
            completed_log(
                collector_source_relative,
                "V7_WITNESS_COLLECTOR\t"
                "HighDimensionalProbability.Verification.scripts.witnesses."
                "SyntheticDefinitionWitness\t"
                "syntheticPreludeDef_witness\ttheorem\t\t\t",
            ),
            encoding="utf-8",
        )
        no_type_dependency = self.check()
        self.assertFalse(no_type_dependency.passed)
        self.assertTrue(
            any(
                "type does not directly mention the audited definition"
                in problem
                for problem in no_type_dependency.problems
            )
        )

        collector_log.write_text(
            completed_log(collector_source_relative, collector_row),
            encoding="utf-8",
        )
        row["evidence_axioms"] = "propext"
        _write_tsv(path, REVIEW_COLUMNS, rows)
        forged_axioms = self.check()
        self.assertFalse(forged_axioms.passed)
        self.assertTrue(
            any(
                "differ from exact collector output" in problem
                for problem in forged_axioms.problems
            ),
            forged_axioms.problems,
        )
        row["evidence_axioms"] = "(none)"
        _write_tsv(path, REVIEW_COLUMNS, rows)

        collector_log.write_text(
            completed_log(collector_source_relative, collector_row)
            + "forged trailing text\n",
            encoding="utf-8",
        )
        nonterminal_exit = self.check()
        self.assertFalse(nonterminal_exit.passed)
        self.assertTrue(
            any(
                "not the terminal nonempty log line" in problem
                for problem in nonterminal_exit.problems
            )
        )

    def test_module_coherent_partition_is_deterministic(self) -> None:
        other = self.root / "other"
        prepare(
            load_path=self.load,
            candidates_path=self.candidates,
            output_dir=other,
            shard_count=2,
            force=False,
        )
        first = (self.review / "v7_definition_review_manifest.tsv").read_text(
            encoding="utf-8"
        )
        second = (other / "v7_definition_review_manifest.tsv").read_text(
            encoding="utf-8"
        )
        self.assertEqual(first, second)

    def test_embedded_calibration_passes(self) -> None:
        self.assertEqual(self_test(), 0)


if __name__ == "__main__":
    unittest.main()
