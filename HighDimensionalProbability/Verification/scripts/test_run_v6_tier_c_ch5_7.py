#!/usr/bin/env python3
"""Static calibration tests for the Chapters 5--7 Tier-C runner."""

from __future__ import annotations

import csv
import json
import sys
import tempfile
import unittest
from pathlib import Path

SCRIPT_DIR = Path(__file__).resolve().parent
if str(SCRIPT_DIR) not in sys.path:
    sys.path.insert(0, str(SCRIPT_DIR))

import run_v6_tier_c_ch5_7 as runner


class QueueSamplingTests(unittest.TestCase):
    def setUp(self) -> None:
        self.temporary = tempfile.TemporaryDirectory(
            prefix="hdp-v6-ch5-7-queue-"
        )
        self.root = Path(self.temporary.name)
        self.original_root = runner.ROOT
        runner.ROOT = self.root

        ranking: list[dict[str, object]] = []
        head: list[dict[str, object]] = []
        ledger_rows: list[dict[str, str]] = []
        for chapter, row_ids in runner.QUEUE_IDS.items():
            for rank, row_id in enumerate(row_ids, start=1):
                candidate = {
                    "sample_kind": "ok_row_candidate_order",
                    "chapter": chapter,
                    "rank": rank,
                    "target_id": row_id,
                }
                ranking.append(candidate)
                head.append(
                    {
                        **candidate,
                        "sample_kind": "ok_review_queue_head",
                    }
                )
                if row_id in runner.CITATION_EVIDENCE:
                    evidence = runner.CITATION_EVIDENCE[row_id]
                    citation = str(evidence["citing"])
                    resolved = str(evidence["target"])
                else:
                    citation = "FRESH_NAMED_WITNESS: synthetic model"
                    resolved = "HDP.Synthetic.target"
                ledger_rows.append(
                    {
                        "row_set": "sampling_plan",
                        "sample_kind": "ok_review_queue_head",
                        "sample_rank": str(rank),
                        "row_id": row_id,
                        "chapter": chapter,
                        "resolved_declarations": resolved,
                        "verdict": "OK",
                        "witness_by_citation_candidate": citation,
                        "tier_c_required": "yes",
                    }
                )

        self.sampling_plan = {
            "schema_version": 1,
            "semantic_verdicts_assigned": False,
            "ok_candidate_ranking": ranking,
            "ok_review_queue_head": head,
        }
        self.write_json(runner.SAMPLING_PLAN_REL, self.sampling_plan)
        self.write_json(
            runner.INVENTORY_SUMMARY_REL,
            {"review_census": {"row_count": 835, "frozen_row_count": 838}},
        )
        ledger = self.root / runner.LEDGER_REL
        ledger.parent.mkdir(parents=True, exist_ok=True)
        with ledger.open("w", encoding="utf-8", newline="") as handle:
            writer = csv.DictWriter(
                handle,
                fieldnames=tuple(ledger_rows[0]),
                delimiter="\t",
                lineterminator="\n",
            )
            writer.writeheader()
            writer.writerows(ledger_rows)

    def tearDown(self) -> None:
        runner.ROOT = self.original_root
        self.temporary.cleanup()

    def write_json(self, relative: Path, payload: object) -> None:
        path = self.root / relative
        path.parent.mkdir(parents=True, exist_ok=True)
        path.write_text(json.dumps(payload) + "\n", encoding="utf-8")

    def test_exact_full_census_queue_is_accepted(self) -> None:
        report = runner.check_queue()
        self.assertEqual(report["row_count"], 15)
        self.assertEqual(
            report["sampling_frame"]["census_row_count"], 835
        )

    def test_queue_head_drift_is_rejected(self) -> None:
        self.sampling_plan["ok_review_queue_head"][0]["target_id"] = (
            "census-planted-drift"
        )
        self.write_json(runner.SAMPLING_PLAN_REL, self.sampling_plan)
        with self.assertRaisesRegex(
            runner.AuditFailure, "queue head differs"
        ):
            runner.check_queue()


class CitationEvidenceTests(unittest.TestCase):
    def setUp(self) -> None:
        self.temporary = tempfile.TemporaryDirectory(
            prefix="hdp-v6-ch5-7-citation-"
        )
        self.root = Path(self.temporary.name)
        self.original_root = runner.ROOT
        self.original_evidence = runner.CITATION_EVIDENCE
        runner.ROOT = self.root
        runner.CITATION_EVIDENCE = {
            "synthetic-row": {
                "target": "HDP.syntheticTarget",
                "citing": "HDP.syntheticPrivateCiting",
                "location": "HighDimensionalProbability/Synthetic.lean:2",
                "rationale": (
                    "The private citing theorem constructs and applies the "
                    "synthetic target."
                ),
            }
        }
        source = self.root / "HighDimensionalProbability" / "Synthetic.lean"
        source.parent.mkdir(parents=True)
        source.write_text(
            "theorem syntheticTarget : True := True.intro\n"
            "private theorem syntheticPrivateCiting : True := "
            "HDP.syntheticTarget\n",
            encoding="utf-8",
        )
        self.logs = (
            self.root / "HighDimensionalProbability" / "Verification" / "logs"
        )
        self.logs.mkdir(parents=True)
        self.write_axioms("")
        self.write_dependency("value")

    def tearDown(self) -> None:
        runner.ROOT = self.original_root
        runner.CITATION_EVIDENCE = self.original_evidence
        self.temporary.cleanup()

    def write_axioms(self, citing_axioms: str) -> None:
        path = self.root / runner.V4_AXIOMS_REL
        with path.open("w", encoding="utf-8", newline="") as handle:
            writer = csv.DictWriter(
                handle,
                fieldnames=(
                    "module",
                    "name",
                    "kind",
                    "private_user_name",
                    "axioms",
                ),
                delimiter="\t",
                lineterminator="\n",
            )
            writer.writeheader()
            writer.writerows(
                (
                    {
                        "module": "HighDimensionalProbability.Synthetic",
                        "name": "HDP.syntheticTarget",
                        "kind": "theorem",
                        "private_user_name": "",
                        "axioms": "",
                    },
                    {
                        "module": "HighDimensionalProbability.Synthetic",
                        "name": (
                            "_private.HighDimensionalProbability.Synthetic."
                            "0.HDP.syntheticPrivateCiting"
                        ),
                        "kind": "theorem",
                        "private_user_name": "HDP.syntheticPrivateCiting",
                        "axioms": citing_axioms,
                    },
                )
            )

    def write_dependency(self, origin: str) -> None:
        path = self.root / runner.V4_DEPENDENCIES_REL
        with path.open("w", encoding="utf-8", newline="") as handle:
            writer = csv.DictWriter(
                handle,
                fieldnames=(
                    "source_module",
                    "source",
                    "source_kind",
                    "origin",
                    "target_module",
                    "target",
                ),
                delimiter="\t",
                lineterminator="\n",
            )
            writer.writeheader()
            writer.writerow(
                {
                    "source_module": "HighDimensionalProbability.Synthetic",
                    "source": (
                        "_private.HighDimensionalProbability.Synthetic."
                        "0.HDP.syntheticPrivateCiting"
                    ),
                    "source_kind": "theorem",
                    "origin": origin,
                    "target_module": "HighDimensionalProbability.Synthetic",
                    "target": "HDP.syntheticTarget",
                }
            )

    def test_private_direct_value_edge_is_accepted(self) -> None:
        rows = runner.validate_citation_evidence()
        self.assertEqual(len(rows), 1)
        self.assertEqual(rows[0]["direct_dependency_origin"], "value")
        self.assertEqual(
            rows[0]["citing_internal_name"],
            (
                "_private.HighDimensionalProbability.Synthetic."
                "0.HDP.syntheticPrivateCiting"
            ),
        )

    def test_type_only_edge_is_rejected(self) -> None:
        self.write_dependency("type")
        with self.assertRaisesRegex(
            runner.AuditFailure, "direct value edge"
        ):
            runner.validate_citation_evidence()

    def test_sorry_axiom_is_rejected(self) -> None:
        self.write_axioms("sorryAx")
        with self.assertRaisesRegex(
            runner.AuditFailure, "disallowed axioms"
        ):
            runner.validate_citation_evidence()


if __name__ == "__main__":
    unittest.main()
