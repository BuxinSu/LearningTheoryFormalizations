#!/usr/bin/env python3
"""Fail closed unless the Exercise and Markdown reorganization is exact."""

from __future__ import annotations

import re
import sys
from pathlib import Path


SCRIPT = Path(__file__).resolve()
SOURCE_ROOT = SCRIPT.parents[2]
PROJECT_ROOT = SCRIPT.parents[3]
VERIFY = SOURCE_ROOT / "Verification"
EXERCISE = SOURCE_ROOT / "Exercise"

ROOT_MARKDOWN = {
    "README.md",
    "APPENDIX_SUMMARY.md",
    "HUMAN_VERIFICATION_LOG.md",
}
ACTIVE_REPORTS = {
    "README.md",
    "01_build_integrity.md",
    "02_import_graph.md",
    "03_sorry_audit.md",
    "04_axiom_audit.md",
    "05_escape_hatches.md",
    "06_vacuity_triviality.md",
    "07_definition_sanity.md",
    "08_linter_report.md",
    "09_readme_claims.md",
    "10_conditional_interfaces.md",
    "REVIEW_NOTES.md",
    "CORRECTION_LEDGER.md",
    "FINAL_CORRECTION_REPORT.md",
}
ARCHIVE_MARKDOWN = {
    "FAITHFUL_PROOFREAD_REPORT.md",
    "README.pre-recertification.md",
    "REVIEW_NOTES.pre-correction.md",
    "REVIEW_NOTES.pre-final-correction.md",
    "REVIEW_NOTES.pre-final.md",
}
CHAPTER_COUNTS = {1: 5, 2: 10, 3: 7, 4: 8, 5: 8, 6: 7, 7: 7, 8: 7, 9: 8}
OLD_PATH = re.compile(r"(?:HighDimensionalProbability/)?Chapter[1-9]/Exercise/")
OLD_MODULE = re.compile(r"HighDimensionalProbability\.Chapter[1-9]\.Exercise\.")
NEW_MODULE = re.compile(r"HighDimensionalProbability\.Exercise\.Chapter[1-9]\.")
OLD_RECORD_PATHS = (
    "Appendix/APPENDIX_SUMMARY.md",
    "HighDimensionalProbability/FAITHFUL_PROOFREAD_REPORT.md",
    "HighDimensionalProbability/REVIEW_NOTES.md",
    "HighDimensionalProbability/CORRECTION_LEDGER.md",
    "HighDimensionalProbability/FINAL_CORRECTION_REPORT.md",
)


def fail(message: str) -> None:
    raise RuntimeError(message)


def regular_files(directory: Path, suffix: str) -> list[Path]:
    result = sorted(path for path in directory.rglob(f"*{suffix}") if path.is_file())
    bad = [path for path in result if path.is_symlink()]
    if bad:
        fail("symlinked files are forbidden: " + ", ".join(map(str, bad)))
    return result


def check_markdown_layout() -> tuple[int, int, int]:
    root_names = {path.name for path in SOURCE_ROOT.glob("*.md") if path.is_file()}
    if root_names != ROOT_MARKDOWN:
        fail(f"source-root Markdown mismatch: {sorted(root_names)}")

    active_names = {path.name for path in VERIFY.glob("*.md") if path.is_file()}
    if active_names != ACTIVE_REPORTS:
        fail(f"Verification top-level Markdown mismatch: {sorted(active_names)}")

    archive = VERIFY / "archive"
    archive_names = {path.name for path in archive.glob("*.md") if path.is_file()}
    if archive_names != ARCHIVE_MARKDOWN:
        fail(f"Verification archive mismatch: {sorted(archive_names)}")

    all_markdown = regular_files(SOURCE_ROOT, ".md")
    misplaced = [
        path for path in all_markdown
        if path.parent != SOURCE_ROOT and VERIFY not in path.parents
    ]
    if misplaced:
        fail("Markdown outside the root/Verification layout: " + ", ".join(map(str, misplaced)))

    active_docs = [PROJECT_ROOT / "README.md"]
    active_docs.extend(sorted(SOURCE_ROOT.glob("*.md")))
    active_docs.extend(sorted(VERIFY.glob("*.md")))
    active_docs.extend(sorted((VERIFY / "review").rglob("*.md")))
    stale: list[str] = []
    for path in active_docs:
        text = path.read_text(encoding="utf-8")
        if OLD_PATH.search(text):
            stale.append(f"{path}: legacy Exercise path")
        if OLD_MODULE.search(text):
            stale.append(f"{path}: legacy Exercise module")
        for old in OLD_RECORD_PATHS:
            if old in text:
                stale.append(f"{path}: legacy record path {old}")
    if stale:
        fail("active documentation has stale paths:\n" + "\n".join(stale))
    return len(all_markdown), len(active_docs), len(archive_names)


def check_exercise_layout() -> tuple[int, int]:
    expected = {f"Chapter{chapter}" for chapter in CHAPTER_COUNTS}
    entries = sorted(EXERCISE.iterdir())
    immediate = {path.name for path in entries if path.is_dir() and not path.is_symlink()}
    if immediate != expected or any(path.name not in expected for path in entries):
        fail(f"Exercise root-entry mismatch: {[path.name for path in entries]}")

    total = 0
    for chapter, expected_count in CHAPTER_COUNTS.items():
        directory = EXERCISE / f"Chapter{chapter}"
        files = sorted(directory.iterdir())
        bad = [path for path in files if path.is_symlink() or not path.is_file() or path.suffix != ".lean"]
        if bad:
            fail(f"invalid Exercise entries in {directory}: {bad}")
        if len(files) != expected_count:
            fail(f"{directory}: {len(files)} files != {expected_count}")
        if not (directory / "Main.lean").is_file():
            fail(f"{directory}: Main.lean is missing")
        total += len(files)

    old_directories = [
        SOURCE_ROOT / f"Chapter{chapter}" / "Exercise"
        for chapter in CHAPTER_COUNTS
        if (SOURCE_ROOT / f"Chapter{chapter}" / "Exercise").exists()
    ]
    if old_directories:
        fail("legacy Exercise directories remain: " + ", ".join(map(str, old_directories)))

    lean_files = regular_files(SOURCE_ROOT, ".lean")
    source_text = "\n".join(path.read_text(encoding="utf-8") for path in lean_files)
    if OLD_MODULE.search(source_text):
        fail("legacy Exercise module import/reference remains in Lean source")
    new_module_refs = len(NEW_MODULE.findall(source_text))
    if new_module_refs != 86:
        fail(f"new Exercise module-reference count {new_module_refs} != 86")

    root_aggregator = (PROJECT_ROOT / "HighDimensionalProbability.lean").read_text(encoding="utf-8")
    for chapter in CHAPTER_COUNTS:
        expected_import = f"import HighDimensionalProbability.Exercise.Chapter{chapter}.Main"
        if root_aggregator.count(expected_import) != 1:
            fail(f"root aggregator does not contain exactly one {expected_import!r}")
    return total, new_module_refs


def main() -> int:
    try:
        markdown_files, active_docs, archive_files = check_markdown_layout()
        exercise_files, module_refs = check_exercise_layout()
    except (OSError, UnicodeError, RuntimeError) as error:
        print(f"REORGANIZATION_LAYOUT: FAIL: {error}", file=sys.stderr)
        return 1
    print(f"source_root_markdown={len(ROOT_MARKDOWN)}")
    print(f"verification_top_level_markdown={len(ACTIVE_REPORTS)}")
    print(f"verification_archive_markdown={archive_files}")
    print(f"markdown_files_checked={markdown_files}")
    print(f"active_documents_checked={active_docs}")
    print(f"exercise_files={exercise_files}")
    print(f"new_exercise_module_references={module_refs}")
    print("legacy_exercise_directories=0")
    print("legacy_active_paths=0")
    print("REORGANIZATION_LAYOUT: PASS")
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
