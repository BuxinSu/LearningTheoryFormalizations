#!/usr/bin/env python3
"""Record the locations of mechanically checkable published claims."""

from __future__ import annotations

from pathlib import Path


SCRIPT = Path(__file__).resolve()
VERIFY = SCRIPT.parent.parent
ROOT = VERIFY.parent.parent
OUT = VERIFY / "logs" / "claim_locations.txt"

SOURCES: tuple[tuple[Path, tuple[str, ...]], ...] = (
    (
        ROOT / "MatrixConcentration" / "README.md",
        (
            "Lean / Mathlib version",
            "Published modules",
            "Public `theorem`",
            "Book → Lean correspondence",
            "Verified kernel status",
            "From this directory",
            "~/.elan/bin/lake build",
            "~/.elan/bin/lake env lean",
            "This table contains",
            "Chapter counts are",
        ),
    ),
    (
        ROOT / "MatrixConcentration" / "APPENDIX_SUMMARY.md",
        (
            "UP-004 Golden",
            "UP-005 Gaussian",
            "UP-006 matrix",
            "UP-007 / Book display",
            "Related symmetric and centered-with-loss variants",
            "UP-008 symmetric",
            "contain no `sorry`",
            "exactly",
            "root module",
            "~/.elan/bin/lake build",
        ),
    ),
    (
        ROOT.parent / "TranslationReport" / "Chapter6_build_report.md",
        ("UP-001", "UP-002", "UP-003"),
    ),
    (
        ROOT.parent / "TranslationReport" / "Chapter8_checkpoint.md",
        ("UP-003 discharged", "UP-004", "UP-008"),
    ),
    (
        ROOT.parent / "TranslationReport" / "SOURCES.md",
        ("UP-004", "UP-005", "UP-006", "UP-007", "UP-008"),
    ),
    (
        ROOT.parent / "TranslationReport" / "SOURCE_FAITHFULNESS_LEDGER.md",
        ("## Verification fields", "Verified implementation outcomes", "RN9"),
    ),
)


def main() -> None:
    chunks: list[str] = [
        "MECHANICALLY CHECKABLE CLAIM LOCATIONS",
        "Line numbers refer to the source snapshot in source_manifest.txt.",
        "",
    ]
    for path, needles in SOURCES:
        relative = path.relative_to(ROOT.parent)
        chunks.append(f"[{relative}]")
        lines = path.read_text(encoding="utf-8").splitlines()
        selected: set[int] = set()
        for index, line in enumerate(lines, start=1):
            if any(needle in line for needle in needles):
                selected.add(index)
                if index < len(lines):
                    selected.add(index + 1)
        for index in sorted(selected):
            chunks.append(f"{index}: {lines[index - 1]}")
        chunks.append("")
    OUT.write_text("\n".join(chunks), encoding="utf-8")
    print(f"WROTE {OUT.relative_to(ROOT)}")


if __name__ == "__main__":
    main()
