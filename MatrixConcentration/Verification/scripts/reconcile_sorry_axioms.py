#!/usr/bin/env python3
"""Reconcile V3's textual result with V4's declaration-level axiom census."""

from __future__ import annotations

import csv
import json
from pathlib import Path
import sys

from lean_source_scan import LOGS, relative


def main() -> int:
    textual_path = LOGS / "sorry_audit.json"
    axiom_path = LOGS / "axiom_audit.tsv"
    output = LOGS / "sorry_axiom_reconciliation.txt"

    missing = [path for path in (textual_path, axiom_path) if not path.is_file()]
    if missing:
        with output.open("w", encoding="utf-8") as out:
            out.write("V3/V4 SORRYAX RECONCILIATION\n")
            out.write("status\tINPUT-MISSING\n")
            for path in missing:
                out.write(f"missing\t{relative(path)}\n")
            out.write(
                "required_input\tcomplete V3 textual JSON and V4 per-declaration TSV\n"
            )
        print("missing input(s): " + ", ".join(relative(path) for path in missing))
        return 2

    textual = json.loads(textual_path.read_text(encoding="utf-8"))
    textual_active = int(textual["active_construct_or_marker_hits"])
    sorry_like = sum(
        int(textual["active_counts"].get(name, 0))
        for name in ("sorry", "admit", "sorryAx")
    )

    with axiom_path.open(encoding="utf-8", newline="") as handle:
        reader = csv.DictReader(handle, delimiter="\t")
        expected = {"module", "name", "user_name", "kind", "axioms"}
        if reader.fieldnames is None or not expected.issubset(reader.fieldnames):
            print("axiom TSV has an unexpected or incomplete header", file=sys.stderr)
            return 2
        rows = list(reader)
    sorry_declarations = [
        row
        for row in rows
        if "sorryAx" in {part for part in row["axioms"].split(",") if part}
    ]

    agreement = sorry_like == 0 and not sorry_declarations
    # A nonempty textual result needs source-to-declaration reconciliation by
    # hand, so it is never automatically pronounced agreement.
    status = "AGREE-EMPTY" if agreement else "DISCREPANCY-REQUIRES-REVIEW"
    with output.open("w", encoding="utf-8") as out:
        out.write("V3/V4 SORRYAX RECONCILIATION\n")
        out.write(f"status\t{status}\n")
        out.write(f"v3_active_all_constructs_or_markers\t{textual_active}\n")
        out.write(f"v3_active_sorry_admit_sorryAx\t{sorry_like}\n")
        out.write(f"v4_declarations_audited\t{len(rows)}\n")
        out.write(
            f"v4_declarations_depending_on_sorryAx\t{len(sorry_declarations)}\n"
        )
        for row in sorry_declarations:
            out.write(
                "v4_sorryAx_declaration\t"
                f"{row['module']}\t{row['name']}\t{row['user_name']}\n"
            )
        if status == "AGREE-EMPTY":
            out.write(
                "interpretation\ttextual and declaration-level kernel censuses "
                "independently return the same empty set\n"
            )
        else:
            out.write(
                "interpretation\treconcile each source hit to its enclosing "
                "declaration before assigning a verdict\n"
            )
    print(f"status={status}")
    print(f"v3_active_sorry_admit_sorryAx={sorry_like}")
    print(f"v4_declarations_depending_on_sorryAx={len(sorry_declarations)}")
    print(f"evidence={relative(output)}")
    return 0 if agreement else 1


if __name__ == "__main__":
    raise SystemExit(main())
