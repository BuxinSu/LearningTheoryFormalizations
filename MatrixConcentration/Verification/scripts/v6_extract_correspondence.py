#!/usr/bin/env python3
"""Extract the fixed V6 Book→Lean correspondence row set.

The source of truth is the table under ``## Book → Lean correspondence`` in
``MatrixConcentration/README.md``.  This script deliberately refuses to
continue unless it measures the published per-chapter row shape.  The refusal
prevents a truncated or accidentally broadened review from looking complete.
"""

from __future__ import annotations

import csv
import html
import re
from pathlib import Path


SCRIPT = Path(__file__).resolve()
VERIFY = SCRIPT.parent.parent
ROOT = VERIFY.parent.parent
README = ROOT / "MatrixConcentration" / "README.md"
LOGS = VERIFY / "logs"

EXPECTED = {1: 21, 2: 136, 3: 35, 4: 55, 5: 71, 6: 62, 7: 63, 8: 24}


def plain_cell(cell: str) -> str:
    """Remove the small amount of Markdown used inside correspondence cells."""

    cell = html.unescape(cell.strip())
    cell = re.sub(r"\[([^\]]+)\]\([^)]+\)", r"\1", cell)
    cell = cell.replace("<br>", " ").replace("<br/>", " ")
    cell = cell.replace("`", "")
    return re.sub(r"\s+", " ", cell).strip()


def parse() -> list[dict[str, str | int]]:
    text = README.read_text(encoding="utf-8")
    in_table = False
    chapter: int | None = None
    chapter_row = 0
    rows: list[dict[str, str | int]] = []
    for line_number, line in enumerate(text.splitlines(), start=1):
        if line == "## Book → Lean correspondence":
            in_table = True
            continue
        if in_table and line.startswith("## ") and not line.startswith("### "):
            break
        match = re.fullmatch(r"### Chapter ([1-8])", line)
        if in_table and match:
            chapter = int(match.group(1))
            chapter_row = 0
            continue
        if not in_table or chapter is None or not line.startswith("|"):
            continue
        cells = [part.strip() for part in line.strip().strip("|").split("|")]
        if len(cells) != 5:
            raise RuntimeError(
                f"README line {line_number}: expected 5 cells, measured {len(cells)}"
            )
        if cells[0] == "Book source" or all(set(cell) <= {":", "-"} for cell in cells):
            continue
        chapter_row += 1
        rows.append(
            {
                "global_row": len(rows) + 1,
                "chapter": chapter,
                "chapter_row": chapter_row,
                "readme_line": line_number,
                "book_source": plain_cell(cells[0]),
                "declaration": plain_cell(cells[1]),
                "final_module": plain_cell(cells[2]),
                "role": plain_cell(cells[3]),
                "notes": plain_cell(cells[4]),
            }
        )
    return rows


def main() -> int:
    rows = parse()
    measured = {
        chapter: sum(row["chapter"] == chapter for row in rows)
        for chapter in sorted(EXPECTED)
    }
    problems = []
    if len(rows) != sum(EXPECTED.values()):
        problems.append(
            f"total expected {sum(EXPECTED.values())}, measured {len(rows)}"
        )
    for chapter, expected in EXPECTED.items():
        if measured[chapter] != expected:
            problems.append(
                f"chapter {chapter} expected {expected}, measured {measured[chapter]}"
            )
    duplicate_positions = len(
        {(row["chapter"], row["chapter_row"]) for row in rows}
    ) != len(rows)
    if duplicate_positions:
        problems.append("duplicate chapter/row positions")
    missing_names = [row for row in rows if not row["declaration"]]
    if missing_names:
        problems.append(f"{len(missing_names)} blank declaration cells")

    LOGS.mkdir(parents=True, exist_ok=True)
    output = LOGS / "v6_correspondence_rows.tsv"
    fields = [
        "global_row",
        "chapter",
        "chapter_row",
        "readme_line",
        "book_source",
        "declaration",
        "final_module",
        "role",
        "notes",
    ]
    with output.open("w", encoding="utf-8", newline="") as handle:
        writer = csv.DictWriter(handle, fieldnames=fields, delimiter="\t")
        writer.writeheader()
        writer.writerows(rows)

    summary = [
        "V6 CORRESPONDENCE ROW EXTRACTION",
        f"SOURCE {README.relative_to(ROOT)}",
        "RULE rows in the eight Chapter tables under '## Book → Lean correspondence'; "
        "header and separator rows excluded; one Markdown body row equals one review row",
        f"TOTAL {len(rows)}",
        *(f"CHAPTER_{chapter} {measured[chapter]}" for chapter in sorted(measured)),
        f"UNIQUE_DECLARATION_CELLS {len({row['declaration'] for row in rows})}",
        f"PROBLEMS {len(problems)}",
        *problems,
        f"VERDICT {'PASS' if not problems else 'FAIL'}",
    ]
    (LOGS / "v6_correspondence_extraction.log").write_text(
        "\n".join(summary) + "\n", encoding="utf-8"
    )
    print("\n".join(summary))
    return 0 if not problems else 1


if __name__ == "__main__":
    raise SystemExit(main())
