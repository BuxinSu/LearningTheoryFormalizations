#!/usr/bin/env python3
"""Light chronology-aware consistency check of the separate audit trail."""

from __future__ import annotations

from pathlib import Path


SCRIPT = Path(__file__).resolve()
VERIFY = SCRIPT.parent.parent
ROOT = VERIFY.parent.parent
REPORTS = ROOT.parent / "TranslationReport"
LOG = VERIFY / "logs" / "v9_translation_consistency.txt"
# This sibling ledger is shared by more than one formalization workspace.
# `Appendix_checkpoint.md` belongs to the HighDimensionalProbability project
# (its contents and links say so explicitly), so it is not a MatrixConcentration
# translation record.
NONPROJECT_RECORDS = {"Appendix_checkpoint.md"}


def require(path: Path, needle: str, problems: list[str]) -> None:
    if needle not in path.read_text(encoding="utf-8"):
        problems.append(f"{path.name}: missing {needle!r}")


def main() -> int:
    problems: list[str] = []
    content = sorted(
        path
        for path in REPORTS.glob("*.md")
        if path.name not in NONPROJECT_RECORDS
    )
    if len(content) != 63:
        problems.append(f"expected 63 Markdown records, measured {len(content)}")

    checkpoints = [
        "Chapter_1_and_2_checkpoint.md",
        "Chapter3_checkpoint.md",
        "Chapter4_checkpoint.md",
        "Chapter5_checkpoint.md",
        "Chapter6_checkpoint.md",
        "Chapter7_checkpoint.md",
        "Chapter8_checkpoint.md",
    ]
    for filename in checkpoints:
        require(REPORTS / filename, "**Status: COMPLETE", problems)

    require(
        REPORTS / "Chapter6_build_report.md",
        "| UP-001 | Chapter1/03 (Thm 1.6.2 tail) | **discharged this chapter** |",
        problems,
    )
    require(
        REPORTS / "Chapter6_build_report.md",
        "| UP-002 | Chapter1/03 (Thm 1.6.2 expectation) | **discharged this chapter** |",
        problems,
    )
    require(REPORTS / "Chapter8_checkpoint.md", "**UP-003 discharged**", problems)
    require(
        REPORTS / "PUBLICATION_AUDIT_GPT.md",
        "Book display (6.1.6) is the sole declared formal-coverage exception.",
        problems,
    )
    require(
        REPORTS / "PUBLICATION_AUDIT_GPT.md",
        "There are\nzero open blockers within this declared scope.",
        problems,
    )

    historical_files = [
        "Chapter6_build_report.md",
        "Chapter7_build_report.md",
        "Appendix_report.md",
    ]
    historical_by_file: dict[str, int] = {}
    for filename in historical_files:
        historical_by_file[filename] = 0
        for line in (REPORTS / filename).read_text(encoding="utf-8").splitlines():
            if line.startswith("| UP-") and " open" in line.lower():
                historical_by_file[filename] += 1
    historical_open = sum(historical_by_file.values())
    expected_historical = {
        "Chapter6_build_report.md": 4,
        "Chapter7_build_report.md": 6,
        "Appendix_report.md": 4,
    }
    if historical_by_file != expected_historical:
        problems.append(
            "historical open-row distribution differs: "
            f"expected {expected_historical}, measured {historical_by_file}"
        )

    lines = [
        "V9 TRANSLATION-RECORD LIGHT CONSISTENCY CHECK",
        f"record_directory={REPORTS}",
        f"markdown_content_files={len(content)}",
        f"complete_checkpoint_files={len(checkpoints)}",
        "up001_up002_closure_record=Chapter6_build_report.md",
        "up003_closure_record=Chapter8_checkpoint.md",
        "final_declared_scope_record=PUBLICATION_AUDIT_GPT.md",
        "formal_coverage_exception=Book display (6.1.6)",
        *(
            f"historical_open_rows_{filename}={historical_by_file[filename]}"
            for filename in historical_files
        ),
        f"historical_open_rows_in_earlier_records={historical_open}",
        "historical_open_rows_interpretation=superseded chronology, not current status",
        "faithfulness_reaudit=OUT_OF_SCOPE",
        f"problems={len(problems)}",
        *(f"PROBLEM {problem}" for problem in problems),
        f"result={'PASS' if not problems else 'FAIL'}",
        "",
    ]
    LOG.write_text("\n".join(lines), encoding="utf-8")
    print("\n".join(lines), end="")
    return 0 if not problems else 1


if __name__ == "__main__":
    raise SystemExit(main())
