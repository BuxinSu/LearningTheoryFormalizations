#!/usr/bin/env python3
"""Regression tests for the mechanical README/census inventory."""

from __future__ import annotations

import csv
import hashlib
import io
import json
import sys
import unittest
from pathlib import Path

sys.path.insert(0, str(Path(__file__).resolve().parent))
import row_inventory


class MarkdownRowTests(unittest.TestCase):
    def test_inline_code_pipe_is_not_a_separator(self) -> None:
        self.assertEqual(
            row_inventory.split_markdown_row(
                "| first | `x | y` and text | third |"
            ),
            ["first", "`x | y` and text", "third"],
        )

    def test_long_inline_code_delimiter_is_paired(self) -> None:
        self.assertEqual(
            row_inventory.split_markdown_row(
                "| first | ``x ` y | z`` | third |"
            ),
            ["first", "``x ` y | z``", "third"],
        )

    def test_escaped_pipe_is_not_a_separator(self) -> None:
        self.assertEqual(
            row_inventory.split_markdown_row(
                r"| first | escaped \| pipe | third |"
            ),
            ["first", r"escaped \| pipe", "third"],
        )

    def test_unterminated_inline_code_is_rejected(self) -> None:
        with self.assertRaises(row_inventory.InventoryError):
            row_inventory.split_markdown_row("| first | `unterminated |")


class EndpointResolutionTests(unittest.TestCase):
    def test_namespace_inheritance_is_left_to_right(self) -> None:
        occurrences, ignored = row_inventory.resolve_endpoint_cell(
            "`HDP.Chapter0.first`; `second`; `Other.third`; `fourth`"
        )
        self.assertEqual(ignored, [])
        self.assertEqual(
            [occurrence["resolved"] for occurrence in occurrences],
            [
                "HDP.Chapter0.first",
                "HDP.Chapter0.second",
                "Other.third",
                "Other.fourth",
            ],
        )
        self.assertEqual(
            [occurrence["mode"] for occurrence in occurrences],
            [
                "qualified",
                "namespace_inherited",
                "qualified",
                "namespace_inherited",
            ],
        )

    def test_non_identifier_code_span_is_retained_as_ignored(self) -> None:
        occurrences, ignored = row_inventory.resolve_endpoint_cell(
            "`HDP.Chapter1.good`; `f x`; `path/File.lean`"
        )
        self.assertEqual(
            [occurrence["resolved"] for occurrence in occurrences],
            ["HDP.Chapter1.good"],
        )
        self.assertEqual(ignored, ["f x", "path/File.lean"])


class LiveInventoryTests(unittest.TestCase):
    @classmethod
    def setUpClass(cls) -> None:
        cls.artifacts, cls.summary = row_inventory.build_artifacts()

    def test_exact_publication_and_census_counts(self) -> None:
        self.assertEqual(self.summary["readme"]["row_count"], 611)
        self.assertEqual(
            self.summary["readme"]["unique_endpoint_count"], 540
        )
        self.assertEqual(
            self.summary["frozen_review_census"]["row_count"], 838
        )
        self.assertEqual(
            self.summary["frozen_review_census"][
                "coverage_bucket_counts"
            ],
            {
                "appendix_proved": 65,
                "appendix_unresolved_or_deferred": 5,
                "core_formalized": 768,
            },
        )
        self.assertEqual(self.summary["review_census"]["row_count"], 835)
        self.assertEqual(
            self.summary["review_census"]["coverage_bucket_counts"],
            {
                "appendix_proved": 66,
                "core_formalized": 769,
            },
        )
        self.assertEqual(
            self.summary["endpoint_union"]["unique_endpoint_count"], 634
        )

    def test_explicit_census_derivation(self) -> None:
        review = self.summary["frozen_review_census"]
        self.assertEqual(review["raw_frozen_display_rows"], 724)
        self.assertEqual(review["frozen_display_only_extras"], 7)
        self.assertEqual(review["frozen_census_rows"], 717)
        self.assertEqual(review["original_appendix_rows"], 67)
        self.assertEqual(review["raw_gap_rows"], 89)
        self.assertEqual(review["accepted_gap_rows"], 54)
        self.assertEqual(review["rejected_gap_rows"], 35)
        current = self.summary["review_census"]
        self.assertEqual(
            current["removed_row_ids"],
            sorted(row_inventory.CURRENT_REMOVED_ROW_IDS),
        )
        self.assertEqual(
            current["derivation"], "838 - 3 removed conclusions = 835"
        )

    def test_current_projection_rows_and_endpoints(self) -> None:
        rows = list(
            csv.DictReader(
                io.StringIO(self.artifacts["review_census_835.tsv"]),
                delimiter="\t",
            )
        )
        by_id = {row["row_id"]: row for row in rows}
        self.assertTrue(
            row_inventory.CURRENT_REMOVED_ROW_IDS.isdisjoint(by_id)
        )
        exercise = by_id[row_inventory.CURRENT_EXERCISE_8_39_ROW_ID]
        self.assertEqual(exercise["book_ref"], "Exercise 8.39(b)")
        self.assertEqual(exercise["coverage_bucket"], "core_formalized")
        self.assertEqual(
            json.loads(exercise["direct_endpoint_names"]),
            [row_inventory.CURRENT_EXERCISE_8_39_ENDPOINT],
        )
        brownian = by_id[row_inventory.CURRENT_BROWNIAN_ROW_ID]
        self.assertEqual(brownian["coverage_bucket"], "appendix_proved")
        self.assertEqual(
            json.loads(brownian["direct_endpoint_names"]),
            [row_inventory.CURRENT_BROWNIAN_ENDPOINT],
        )

        endpoints = {
            row["endpoint"]
            for row in csv.DictReader(
                io.StringIO(self.artifacts["endpoint_union.tsv"]),
                delimiter="\t",
            )
        }
        self.assertTrue(
            row_inventory.REMOVED_CONDITIONAL_ENDPOINTS.isdisjoint(
                endpoints
            )
        )
        self.assertIn(
            row_inventory.CURRENT_EXERCISE_8_39_ENDPOINT, endpoints
        )
        self.assertIn(row_inventory.CURRENT_BROWNIAN_ENDPOINT, endpoints)

    def test_frozen_census_render_is_unchanged(self) -> None:
        for name, expected in (
            (
                "review_census_838.tsv",
                row_inventory.EXPECTED_FROZEN_CENSUS_TSV_SHA256,
            ),
            (
                "review_census_838.json",
                row_inventory.EXPECTED_FROZEN_CENSUS_JSON_SHA256,
            ),
        ):
            with self.subTest(name=name):
                digest = hashlib.sha256(
                    self.artifacts[name].encode("utf-8")
                ).hexdigest()
                self.assertEqual(digest, expected)

    def test_sample_quotas(self) -> None:
        self.assertEqual(
            self.summary["ok_candidate_plan"]["queue_head_counts"],
            {chapter: 5 for chapter in row_inventory.CHAPTERS},
        )
        sampling = self.artifacts["sampling_plan.tsv"].splitlines()
        # Header + 3 * 9 exercise rows + 5 * 10 OK-candidate heads.
        self.assertEqual(len(sampling), 1 + 27 + 50)

    def test_render_is_deterministic(self) -> None:
        second_artifacts, second_summary = row_inventory.build_artifacts()
        self.assertEqual(self.artifacts, second_artifacts)
        self.assertEqual(self.summary, second_summary)


if __name__ == "__main__":
    unittest.main()
