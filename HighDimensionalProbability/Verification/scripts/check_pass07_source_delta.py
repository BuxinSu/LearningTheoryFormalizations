#!/usr/bin/env python3
"""Verify the exact source delta from the historical V4-bound manifest."""

from __future__ import annotations

import hashlib
from pathlib import Path

from file_universe import ROOT


ARCHIVE = (
    ROOT
    / "HighDimensionalProbability"
    / "Verification"
    / "logs"
    / "source_manifest.pre-final-correction.txt"
)
EXPECTED_ARCHIVE_DIGEST = (
    "f3eac62acff55cab3c2da95b9a88ccdb2f0a6e7cb4ef8381254546e0ad594888"
)
EXPECTED_CHANGED = {
    "HighDimensionalProbability/Appendix/BerryEsseen.lean",
    "HighDimensionalProbability/Appendix/Infra/SLT/GaussianLSI/BernoulliLSI.lean",
    "HighDimensionalProbability/Appendix/PositiveRicciConcentration.lean",
    "HighDimensionalProbability/Chapter8_Chaining.lean",
}


def sha256(path: Path) -> str:
    digest = hashlib.sha256()
    with path.open("rb") as handle:
        for chunk in iter(lambda: handle.read(1024 * 1024), b""):
            digest.update(chunk)
    return digest.hexdigest()


def main() -> int:
    lines = ARCHIVE.read_text(encoding="utf-8").splitlines()
    declared = next(
        line.removeprefix("# digest_of_digests: ")
        for line in lines
        if line.startswith("# digest_of_digests: ")
    )
    if declared != EXPECTED_ARCHIVE_DIGEST:
        raise RuntimeError(
            f"archive digest header changed: {declared} != {EXPECTED_ARCHIVE_DIGEST}"
        )

    entries: dict[str, str] = {}
    for line in lines:
        if not line or line.startswith("#"):
            continue
        old_hash, relative = line.split("  ", 1)
        entries[relative] = old_hash

    missing = sorted(relative for relative in entries if not (ROOT / relative).is_file())
    if missing:
        raise RuntimeError("manifest paths missing: " + ", ".join(missing))

    current = {relative: sha256(ROOT / relative) for relative in entries}
    changed = {
        relative
        for relative, old_hash in entries.items()
        if current[relative] != old_hash
    }
    if changed != EXPECTED_CHANGED:
        raise RuntimeError(
            "unexpected historical-to-current source delta: "
            f"expected {sorted(EXPECTED_CHANGED)}, observed {sorted(changed)}"
        )

    print("PASS: historical V4-bound manifest to current source has exact four-file delta")
    print(f"archive_digest_of_digests: {declared}")
    print(f"entries: {len(entries)}")
    print(f"unchanged_entries: {len(entries) - len(changed)}")
    print(f"changed_entries: {len(changed)}")
    for relative in sorted(changed):
        print(f"{relative}")
        print(f"  historical_sha256: {entries[relative]}")
        print(f"  current_sha256:    {current[relative]}")
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
