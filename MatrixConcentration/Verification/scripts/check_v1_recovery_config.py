#!/usr/bin/env python3
"""Verify that the V1 recovery Lake file only changes the root build directory."""

from __future__ import annotations

import sys
import tomllib
from pathlib import Path


SCRIPT = Path(__file__).resolve()
ROOT = SCRIPT.parent.parent.parent.parent
LIVE = ROOT / "lakefile.toml"
RECOVERY = SCRIPT.parent / "v1_recovery_lakefile.toml"
EXPECTED_ADDITION = (
    'buildDir = ".audit_work/v1_recertification_recovery_build_v7"\n'
)
ANCHOR = 'defaultTargets = ["MatrixConcentration"]\n'


def main() -> int:
    live = LIVE.read_text(encoding="utf-8")
    recovery = RECOVERY.read_text(encoding="utf-8")
    anchor_count = live.count(ANCHOR)
    expected = (
        live.replace(ANCHOR, ANCHOR + EXPECTED_ADDITION, 1)
        if anchor_count == 1
        else ""
    )
    parsed = tomllib.loads(recovery)
    top_level_build_dir = parsed.get("buildDir")
    exact_bytes = recovery == expected
    parsed_top_level = (
        top_level_build_dir
        == ".audit_work/v1_recertification_recovery_build_v7"
    )
    passed = anchor_count == 1 and exact_bytes and parsed_top_level
    print("V1 RECOVERY CONFIG CHECK")
    print(f"live={LIVE.relative_to(ROOT)}")
    print(f"recovery={RECOVERY.relative_to(ROOT)}")
    print(f"anchor_count={anchor_count}")
    print(f"exact_full_file={str(exact_bytes).lower()}")
    print(f"parsed_top_level_build_dir={str(parsed_top_level).lower()}")
    print(f"result={'PASS' if passed else 'FAIL'}")
    return 0 if passed else 1


if __name__ == "__main__":
    sys.exit(main())
