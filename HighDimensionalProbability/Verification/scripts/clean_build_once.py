#!/usr/bin/env python3
"""Delete only the project's .lake/build, at most once for this evidence folder."""

from __future__ import annotations

import argparse
import datetime as dt
import shutil
from pathlib import Path


ROOT = Path(__file__).resolve().parents[3]
TARGET = ROOT / ".lake" / "build"
DEFAULT_MARKER = (
    ROOT
    / "HighDimensionalProbability"
    / "Verification"
    / "logs"
    / "clean_build_once.marker"
)


def main() -> int:
    parser = argparse.ArgumentParser()
    parser.add_argument("--marker", type=Path, default=DEFAULT_MARKER)
    args = parser.parse_args()
    marker = args.marker if args.marker.is_absolute() else ROOT / args.marker
    expected = (ROOT / ".lake" / "build").resolve(strict=False)
    if TARGET.resolve(strict=False) != expected:
        raise RuntimeError("refusing unexpected deletion target")

    if marker.exists():
        print(f"one-time deletion already recorded: {marker}")
        print("no deletion performed")
        return 0

    existed = TARGET.exists()
    if existed:
        shutil.rmtree(TARGET)
    marker.parent.mkdir(parents=True, exist_ok=True)
    marker.write_text(
        "\n".join(
            (
                "V1 one-time clean-build deletion",
                f"timestamp: {dt.datetime.now().astimezone().isoformat()}",
                f"target: {TARGET}",
                f"target_existed_before: {str(existed).lower()}",
                f"target_exists_after: {str(TARGET.exists()).lower()}",
                "deleted_other_paths: false",
                "",
            )
        ),
        encoding="utf-8",
    )
    print(f"target: {TARGET}")
    print(f"target_existed_before: {str(existed).lower()}")
    print(f"target_exists_after: {str(TARGET.exists()).lower()}")
    print(f"marker: {marker}")
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
