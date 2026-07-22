#!/usr/bin/env python3
"""Certify the content-preserving Exercise-tree reorganization.

The semantic baseline for this check is the manifest-pinned Round-10 tree.
Exactly 67 Lean files move from ``ChapterN/Exercise`` to
``Exercise/ChapterN``.  The only permitted source-text changes are the module
imports forced by that move, the nine root-aggregator imports, and four
specified path/module references in comments.  Every other byte in the
source-manifest universe must be unchanged.

The emitted certificate is intentionally usable by later verification gates:
it binds the exact Round-10 digest to the dynamically recomputed current
digest, so callers never accept a new digest by bare allowlisting.
"""

from __future__ import annotations

import argparse
import hashlib
import re
import sys
from pathlib import Path

from file_universe import ROOT, enumerate_universe
from source_manifest import build_manifest


ROUND10_SOURCE_DIGEST = (
    "bca641bd4c523754aa472b97cb1ed5638a6eb7361f99158a3f231a03a7446460"
)
EXPECTED_LIBRARY_FILES = 222
EXPECTED_MOVED_FILES = 67
EXPECTED_MOVED_IMPORT_REWRITES = 68
EXPECTED_ROOT_IMPORT_REWRITES = 9
EXTRA_FILES = (
    "HighDimensionalProbability.lean",
    "lakefile.toml",
    "lake-manifest.json",
    "lean-toolchain",
)
CERTIFICATE_LOG = (
    ROOT
    / "HighDimensionalProbability"
    / "Verification"
    / "logs"
    / "exercise_reorganization_delta.log"
)
SOURCE_MANIFEST = (
    ROOT / "HighDimensionalProbability" / "Verification" / "logs" /
    "source_manifest.txt"
)

OLD_EXERCISE = re.compile(
    r"^HighDimensionalProbability/Chapter([1-9])/Exercise/(.+\.lean)$"
)
NEW_EXERCISE = re.compile(
    r"^HighDimensionalProbability/Exercise/Chapter([1-9])/(.+\.lean)$"
)
IMPORT_LINE = re.compile(r"^[ \t]*import(?:[ \t]|$)")
OLD_IMPORT = re.compile(
    r"HighDimensionalProbability\.Chapter([1-9])\.Exercise\."
)
COMMENT_REWRITES = {
    "HighDimensionalProbability/Appendix.lean": (
        ("Appendix/APPENDIX_SUMMARY.md", "APPENDIX_SUMMARY.md"),
    ),
    "HighDimensionalProbability/Chapter8/Main.lean": (
        ("Chapter8.Exercise.Main", "Exercise.Chapter8.Main"),
    ),
    "HighDimensionalProbability/Chapter1_AnalysisAndProbabilityRefresher.lean": (
        ("Chapter1.Exercise.Sec06", "Exercise.Chapter1.Sec06"),
    ),
    "HighDimensionalProbability/Chapter2_ConcentrationOfIndependentSums.lean": (
        ("Chapter2/Exercise/Sec09.lean", "Exercise/Chapter2/Sec09.lean"),
    ),
}


class ReorganizationError(RuntimeError):
    """Raised when the path-only source relation does not hold exactly."""


def sha256_file(path: Path) -> str:
    digest = hashlib.sha256()
    with path.open("rb") as handle:
        for block in iter(lambda: handle.read(1024 * 1024), b""):
            digest.update(block)
    return digest.hexdigest()


def library_paths(root: Path) -> list[str]:
    hdp = root / "HighDimensionalProbability"
    verification = hdp / "Verification"
    paths: list[str] = []
    for base in (hdp, root / "MatrixConcentration"):
        for path in base.rglob("*.lean"):
            if path.is_symlink() or not path.is_file():
                continue
            if base == hdp and (
                path == verification or verification in path.parents
            ):
                continue
            paths.append(path.relative_to(root).as_posix())
    return sorted(paths)


def manifest_digest(root: Path, paths: list[str]) -> str:
    all_paths = sorted(set(paths).union(EXTRA_FILES))
    missing = [relative for relative in all_paths if not (root / relative).is_file()]
    if missing:
        raise ReorganizationError(
            "manifest inputs are missing: " + ", ".join(missing)
        )
    body = "".join(
        f"{sha256_file(root / relative)}  {relative}\n"
        for relative in all_paths
    )
    return hashlib.sha256(body.encode("utf-8")).hexdigest()


def old_to_new_exercise_path(relative: str) -> str:
    """Translate one old exercise path, leaving every other path unchanged."""

    match = OLD_EXERCISE.fullmatch(relative)
    if match is None:
        return relative
    chapter, tail = match.groups()
    return f"HighDimensionalProbability/Exercise/Chapter{chapter}/{tail}"


def new_to_old_exercise_path(relative: str) -> str:
    """Return the stable pre-reorganization identity for an exercise path."""

    match = NEW_EXERCISE.fullmatch(relative)
    if match is None:
        return relative
    chapter, tail = match.groups()
    return f"HighDimensionalProbability/Chapter{chapter}/Exercise/{tail}"


def rewrite_import_lines(text: str) -> tuple[str, int]:
    """Apply only the module-prefix rewrite on syntactic import lines."""

    output: list[str] = []
    replacements = 0
    for line in text.splitlines(keepends=True):
        if IMPORT_LINE.match(line):
            line, count = OLD_IMPORT.subn(
                lambda match: (
                    "HighDimensionalProbability.Exercise."
                    f"Chapter{match.group(1)}."
                ),
                line,
            )
            replacements += count
        output.append(line)
    return "".join(output), replacements


def expected_unmoved_text(relative: str, baseline_text: str) -> tuple[str, int]:
    """Return the sole permitted current text for one unmoved Lean file."""

    if relative == "HighDimensionalProbability.lean":
        return rewrite_import_lines(baseline_text)
    replacements = COMMENT_REWRITES.get(relative, ())
    expected = baseline_text
    for old, new in replacements:
        if expected.count(old) != 1:
            raise ReorganizationError(
                f"{relative}: expected exactly one baseline comment token {old!r}"
            )
        expected = expected.replace(old, new)
    return expected, len(replacements)


def require_current_manifest() -> tuple[str, str]:
    rendered, digest = build_manifest()
    if not SOURCE_MANIFEST.is_file():
        raise ReorganizationError(f"source manifest is missing: {SOURCE_MANIFEST}")
    if SOURCE_MANIFEST.read_text(encoding="utf-8") != rendered:
        raise ReorganizationError("source manifest file is stale")
    return rendered, digest


def require_certificate(
    log_path: Path = CERTIFICATE_LOG,
    *,
    require_manifest: bool = True,
) -> str:
    """Validate the installed certificate and return its current digest."""

    if require_manifest:
        _rendered, current_digest = require_current_manifest()
    else:
        _rendered, current_digest = build_manifest()
    if not log_path.is_file():
        raise ReorganizationError(
            f"exercise-reorganization certificate is missing: {log_path}"
        )
    text = log_path.read_text(encoding="utf-8", errors="replace")
    required = (
        f"baseline_digest: {ROUND10_SOURCE_DIGEST}",
        f"current_digest: {current_digest}",
        f"library_files_before: {EXPECTED_LIBRARY_FILES}",
        f"library_files_after: {EXPECTED_LIBRARY_FILES}",
        f"exercise_files_moved: {EXPECTED_MOVED_FILES}",
        f"moved_file_import_rewrites: {EXPECTED_MOVED_IMPORT_REWRITES}",
        f"root_import_rewrites: {EXPECTED_ROOT_IMPORT_REWRITES}",
        f"comment_only_rewrites: {len(COMMENT_REWRITES)}",
        "declaration_namespace_or_body_changes: 0",
        "unexpected_source_changes: 0",
        "EXERCISE_REORGANIZATION_DELTA: PASS",
    )
    missing = [fragment for fragment in required if fragment not in text]
    if missing:
        raise ReorganizationError(
            "exercise-reorganization certificate is incomplete: "
            + ", ".join(missing)
        )
    if text.splitlines()[-1:] != ["exit_code: 0"]:
        raise ReorganizationError(
            "exercise-reorganization certificate lacks final exit_code: 0"
        )
    return current_digest


def certify(baseline: Path) -> str:
    baseline = baseline.resolve()
    before = library_paths(baseline)
    current_universe = enumerate_universe()["file_walk_universe"]
    if not isinstance(current_universe, list):
        raise ReorganizationError("current file universe has invalid shape")
    after = sorted(str(path) for path in current_universe)
    if len(before) != EXPECTED_LIBRARY_FILES or len(after) != EXPECTED_LIBRARY_FILES:
        raise ReorganizationError(
            f"library counts changed: before={len(before)} after={len(after)}"
        )
    baseline_digest = manifest_digest(baseline, before)
    if baseline_digest != ROUND10_SOURCE_DIGEST:
        raise ReorganizationError(
            f"baseline digest {baseline_digest} != {ROUND10_SOURCE_DIGEST}"
        )

    moved = sorted(path for path in before if OLD_EXERCISE.fullmatch(path))
    if len(moved) != EXPECTED_MOVED_FILES:
        raise ReorganizationError(
            f"expected {EXPECTED_MOVED_FILES} exercise files, found {len(moved)}"
        )
    mapped = {path: old_to_new_exercise_path(path) for path in moved}
    expected_after = sorted((set(before) - set(moved)) | set(mapped.values()))
    if after != expected_after:
        missing = sorted(set(expected_after) - set(after))
        extra = sorted(set(after) - set(expected_after))
        raise ReorganizationError(
            f"current universe is not the exact move: missing={missing}, extra={extra}"
        )
    surviving_old = [relative for relative in moved if (ROOT / relative).exists()]
    if surviving_old:
        raise ReorganizationError(
            "old exercise source paths remain: " + ", ".join(surviving_old)
        )

    moved_imports = 0
    byte_identical_moves = 0
    for old_relative, new_relative in mapped.items():
        before_path = baseline / old_relative
        after_path = ROOT / new_relative
        baseline_text = before_path.read_text(encoding="utf-8")
        expected_text, replacements = rewrite_import_lines(baseline_text)
        current_text = after_path.read_text(encoding="utf-8")
        if current_text != expected_text:
            raise ReorganizationError(
                f"{old_relative} -> {new_relative}: content changed outside imports"
            )
        moved_imports += replacements
        if before_path.read_bytes() == after_path.read_bytes():
            byte_identical_moves += 1
    if moved_imports != EXPECTED_MOVED_IMPORT_REWRITES:
        raise ReorganizationError(
            f"moved import rewrites {moved_imports} != "
            f"{EXPECTED_MOVED_IMPORT_REWRITES}"
        )

    comment_rewrites = 0
    mapped_targets = set(mapped.values())
    for relative in after:
        if relative in mapped_targets:
            continue
        baseline_text = (baseline / relative).read_text(encoding="utf-8")
        expected_text, replacements = expected_unmoved_text(relative, baseline_text)
        current_text = (ROOT / relative).read_text(encoding="utf-8")
        if current_text != expected_text:
            raise ReorganizationError(
                f"{relative}: unexpected change outside the exact reorganization"
            )
        comment_rewrites += replacements

    root_relative = "HighDimensionalProbability.lean"
    baseline_root_text = (baseline / root_relative).read_text(encoding="utf-8")
    expected_root_text, root_imports = expected_unmoved_text(
        root_relative, baseline_root_text
    )
    if (ROOT / root_relative).read_text(encoding="utf-8") != expected_root_text:
        raise ReorganizationError(
            "HighDimensionalProbability.lean changed outside import rewrites"
        )
    if root_imports != EXPECTED_ROOT_IMPORT_REWRITES:
        raise ReorganizationError(
            f"root import rewrites {root_imports} != {EXPECTED_ROOT_IMPORT_REWRITES}"
        )
    if comment_rewrites != len(COMMENT_REWRITES):
        raise ReorganizationError(
            f"comment rewrites {comment_rewrites} != {len(COMMENT_REWRITES)}"
        )

    for relative in EXTRA_FILES[1:]:
        if (baseline / relative).read_bytes() != (ROOT / relative).read_bytes():
            raise ReorganizationError(f"configuration input changed: {relative}")

    _rendered, current_digest = require_current_manifest()
    print("EXERCISE TREE REORGANIZATION DELTA")
    print("==================================")
    print(f"baseline_digest: {baseline_digest}")
    print(f"current_digest: {current_digest}")
    print(f"library_files_before: {len(before)}")
    print(f"library_files_after: {len(after)}")
    print(f"exercise_files_moved: {len(moved)}")
    print(f"byte_identical_moved_files: {byte_identical_moves}")
    print(f"moved_file_import_rewrites: {moved_imports}")
    print(f"root_import_rewrites: {root_imports}")
    print(f"comment_only_rewrites: {comment_rewrites}")
    print("declaration_namespace_or_body_changes: 0")
    print("unexpected_source_changes: 0")
    print()
    print("old_path\tnew_path\told_sha256\tnew_sha256")
    for old_relative, new_relative in mapped.items():
        print(
            f"{old_relative}\t{new_relative}\t"
            f"{sha256_file(baseline / old_relative)}\t"
            f"{sha256_file(ROOT / new_relative)}"
        )
    print("EXERCISE_REORGANIZATION_DELTA: PASS")
    return current_digest


def main() -> int:
    parser = argparse.ArgumentParser(description=__doc__)
    mode = parser.add_mutually_exclusive_group(required=True)
    mode.add_argument(
        "--baseline",
        type=Path,
        help="preserved Round-10 project root at the bca641 manifest",
    )
    mode.add_argument(
        "--check-log",
        action="store_true",
        help="validate the installed logged certificate against current source",
    )
    args = parser.parse_args()
    if args.baseline is not None:
        certify(args.baseline)
    else:
        digest = require_certificate()
        print(f"EXERCISE_REORGANIZATION_CERTIFICATE: PASS current_digest={digest}")
    return 0


if __name__ == "__main__":
    try:
        raise SystemExit(main())
    except (OSError, ReorganizationError, TypeError, ValueError) as error:
        print(f"EXERCISE_REORGANIZATION_DELTA: FAIL: {error}", file=sys.stderr)
        raise SystemExit(1)
