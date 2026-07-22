#!/usr/bin/env python3
"""Verify the Round 10 source delta against a preserved project copy.

The final-correction fixed point repaired package-linter ``docBlame`` rows
after the post-removal semantic audits were complete.  This checker proves
that the Lean FILE-WALK surface changed only by insertion of one-line
declaration docstrings (with one permitted replacement of a blank line).  It
also binds both sides to their expected source-manifest digests.
"""

from __future__ import annotations

import argparse
import hashlib
import re
import sys
from dataclasses import dataclass
from pathlib import Path

from file_universe import ROOT, enumerate_universe


BASELINE_DIGEST = (
    "83678e994eecf416759cb099d5e69f9d03c15921960d4f3b69d055a7a9e8fe27"
)
ROUND10_DIGEST = (
    "bca641bd4c523754aa472b97cb1ed5638a6eb7361f99158a3f231a03a7446460"
)
EXPECTED_CHANGED_FILES = 25
EXPECTED_DOCSTRINGS = 97
EXTRA_FILES = (
    "HighDimensionalProbability.lean",
    "lakefile.toml",
    "lake-manifest.json",
    "lean-toolchain",
)
DOCSTRING = re.compile(r"^\s*/--.*-/\s*$")


@dataclass(frozen=True)
class Addition:
    path: str
    line: int
    text: str
    replaced_blank: bool


def sha256_file(path: Path) -> str:
    digest = hashlib.sha256()
    with path.open("rb") as handle:
        for block in iter(lambda: handle.read(1024 * 1024), b""):
            digest.update(block)
    return digest.hexdigest()


def manifest_digest(root: Path, paths: list[str]) -> str:
    body = "".join(
        f"{sha256_file(root / relative)}  {relative}\n"
        for relative in sorted(set(paths).union(EXTRA_FILES))
    )
    return hashlib.sha256(body.encode("utf-8")).hexdigest()


def compare_lines(relative: str, before: str, after: str) -> list[Addition]:
    old = before.splitlines(keepends=True)
    new = after.splitlines(keepends=True)
    additions: list[Addition] = []
    old_index = 0
    new_index = 0

    while old_index < len(old) and new_index < len(new):
        if old[old_index] == new[new_index]:
            old_index += 1
            new_index += 1
            continue

        candidate = new[new_index].rstrip("\r\n")
        if not DOCSTRING.fullmatch(candidate):
            raise ValueError(
                f"{relative}: non-docstring change at current line "
                f"{new_index + 1}: {candidate!r}"
            )
        if len(candidate) > 100:
            raise ValueError(
                f"{relative}:{new_index + 1}: docstring exceeds 100 characters"
            )

        replaced_blank = False
        if new_index + 1 < len(new) and new[new_index + 1] == old[old_index]:
            pass
        elif (
            not old[old_index].strip()
            and old_index + 1 < len(old)
            and new_index + 1 < len(new)
            and new[new_index + 1] == old[old_index + 1]
        ):
            old_index += 1
            replaced_blank = True
        else:
            raise ValueError(
                f"{relative}:{new_index + 1}: docstring is not a pure "
                "insertion or blank-line replacement"
            )

        additions.append(
            Addition(
                path=relative,
                line=new_index + 1,
                text=candidate.strip(),
                replaced_blank=replaced_blank,
            )
        )
        new_index += 1

    while new_index < len(new):
        candidate = new[new_index].rstrip("\r\n")
        if not DOCSTRING.fullmatch(candidate) or len(candidate) > 100:
            raise ValueError(
                f"{relative}: unsupported trailing change at line "
                f"{new_index + 1}: {candidate!r}"
            )
        additions.append(
            Addition(relative, new_index + 1, candidate.strip(), False)
        )
        new_index += 1

    if old_index != len(old):
        raise ValueError(
            f"{relative}: {len(old) - old_index} baseline line(s) were deleted"
        )
    return additions


def main() -> int:
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument(
        "--baseline",
        required=True,
        type=Path,
        help="preserved pre-docstring project root",
    )
    args = parser.parse_args()
    baseline = args.baseline.resolve()

    universe = enumerate_universe()
    relative_paths = sorted(
        str(path) for path in universe["file_walk_universe"]
    )
    paths = [*relative_paths, "HighDimensionalProbability.lean"]
    missing = [
        str(root / relative)
        for root in (baseline, ROOT)
        for relative in [*paths, *EXTRA_FILES[1:]]
        if not (root / relative).is_file()
    ]
    if missing:
        raise FileNotFoundError("missing comparison inputs: " + ", ".join(missing))

    baseline_digest = manifest_digest(baseline, relative_paths)
    current_digest = manifest_digest(ROOT, relative_paths)
    if baseline_digest != BASELINE_DIGEST:
        raise ValueError(
            f"baseline digest {baseline_digest} != expected {BASELINE_DIGEST}"
        )
    if current_digest != ROUND10_DIGEST:
        raise ValueError(
            f"current digest {current_digest} != expected {ROUND10_DIGEST}"
        )

    additions: list[Addition] = []
    changed: list[str] = []
    for relative in paths:
        old_path = baseline / relative
        new_path = ROOT / relative
        if old_path.read_bytes() == new_path.read_bytes():
            continue
        file_additions = compare_lines(
            relative,
            old_path.read_text(encoding="utf-8"),
            new_path.read_text(encoding="utf-8"),
        )
        if not file_additions:
            raise ValueError(f"{relative}: byte drift without an allowed docstring")
        changed.append(relative)
        additions.extend(file_additions)

    if len(changed) != EXPECTED_CHANGED_FILES:
        raise ValueError(
            f"changed Lean file count {len(changed)} != {EXPECTED_CHANGED_FILES}"
        )
    if len(additions) != EXPECTED_DOCSTRINGS:
        raise ValueError(
            f"docstring count {len(additions)} != {EXPECTED_DOCSTRINGS}"
        )
    replaced = sum(item.replaced_blank for item in additions)
    if replaced != 1:
        raise ValueError(f"blank-line replacement count {replaced} != 1")

    print("ROUND 10 DOCSTRING-ONLY SOURCE DELTA")
    print("====================================")
    print(f"baseline_digest: {baseline_digest}")
    print(f"current_digest: {current_digest}")
    print(f"file_walk_lean_files_compared: {len(relative_paths)}")
    print("root_aggregator_compared: true")
    print(f"changed_lean_files: {len(changed)}")
    print(f"one_line_docstrings_added: {len(additions)}")
    print(f"blank_lines_replaced: {replaced}")
    print("nonblank_nondoc_source_changes: 0")
    print()
    print("path\told_sha256\tnew_sha256\tdocstrings")
    for relative in changed:
        count = sum(item.path == relative for item in additions)
        print(
            f"{relative}\t{sha256_file(baseline / relative)}\t"
            f"{sha256_file(ROOT / relative)}\t{count}"
        )
    print()
    print("path\tline\treplaced_blank\tdocstring")
    for item in additions:
        print(
            f"{item.path}\t{item.line}\t"
            f"{str(item.replaced_blank).lower()}\t{item.text}"
        )
    print("ROUND10_DOCSTRING_DELTA: PASS")
    return 0


if __name__ == "__main__":
    try:
        raise SystemExit(main())
    except (OSError, TypeError, ValueError) as error:
        print(f"ROUND10_DOCSTRING_DELTA: FAIL: {error}", file=sys.stderr)
        raise SystemExit(1)
