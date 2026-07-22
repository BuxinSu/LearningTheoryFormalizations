#!/usr/bin/env python3
"""Calibrate the two Appetizer--Chapter 4 Tier-B read-only check modes."""

from __future__ import annotations

import hashlib
import tempfile
import unittest
from pathlib import Path
from unittest.mock import patch

import build_v6_tier_b_ch0_4 as main_builder
import build_v6_tier_b_supplement_ch0_4 as supplement_builder


def digest(path: Path) -> str:
    return hashlib.sha256(path.read_bytes()).hexdigest()


class CheckModeTests(unittest.TestCase):
    def exercise_builder(self, module: object, stem: str) -> None:
        with tempfile.TemporaryDirectory() as directory:
            root = Path(directory)
            output = root / f"{stem}.tsv"
            summary = root / f"{stem}_summary.txt"
            with (
                patch.object(module, "OUTPUT", output),
                patch.object(module, "SUMMARY", summary),
            ):
                self.assertEqual(module.main(["--write"]), 0)
                before = (
                    digest(output),
                    digest(summary),
                    output.stat().st_mtime_ns,
                    summary.stat().st_mtime_ns,
                )
                self.assertEqual(module.main(["--check"]), 0)
                after = (
                    digest(output),
                    digest(summary),
                    output.stat().st_mtime_ns,
                    summary.stat().st_mtime_ns,
                )
                self.assertEqual(before, after)

                stale = summary.read_text(encoding="utf-8") + "planted drift\n"
                summary.write_text(stale, encoding="utf-8")
                with self.assertRaisesRegex(
                    ValueError, "generated artifact is stale"
                ):
                    module.main(["--check"])
                self.assertEqual(summary.read_text(encoding="utf-8"), stale)

    def test_main_builder_check_is_read_only_and_fail_closed(self) -> None:
        self.exercise_builder(main_builder, "main")

    def test_supplement_builder_check_is_read_only_and_fail_closed(self) -> None:
        self.exercise_builder(supplement_builder, "supplement")


if __name__ == "__main__":
    unittest.main(verbosity=2)
