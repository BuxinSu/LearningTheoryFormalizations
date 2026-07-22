#!/usr/bin/env python3
"""Pin verification code, curation, and external read-only ledger inputs."""

from __future__ import annotations

import hashlib
import os
from pathlib import Path
import sys


SCRIPT = Path(__file__).resolve()
VERIFY = SCRIPT.parent.parent
ROOT = VERIFY.parent.parent
LOGS = VERIFY / "logs"
MANIFEST = LOGS / "verification_input_manifest.tsv"
SUMMARY = LOGS / "verification_input_manifest_summary.txt"
INPUT_ROOTS = (
    SCRIPT.parent,
    VERIFY / "curation",
    ROOT.parent / "TranslationReport",
)
INPUT_FILES = (
    ROOT / "README.md",
    ROOT / "MatrixConcentration" / "HUMAN_VERIFICATION_LOG.md",
)
EXCLUDED_PARTS = {"__pycache__"}
EXCLUDED_SUFFIXES = {".pyc", ".pyo"}
EXCLUDED_NAMES = {".DS_Store"}
# TranslationReport is a sibling directory shared with other formalization
# workspaces. This record identifies HighDimensionalProbability throughout and
# is therefore not an input to the MatrixConcentration verification lifecycle.
EXCLUDED_TRANSLATION_RECORDS = {"Appendix_checkpoint.md"}


def file_sha256(path: Path) -> str:
    digest = hashlib.sha256()
    with path.open("rb") as stream:
        for block in iter(lambda: stream.read(1024 * 1024), b""):
            digest.update(block)
    return digest.hexdigest()


def inventory() -> tuple[list[tuple[str, int, str]], list[str]]:
    rows: list[tuple[str, int, str]] = []
    problems: list[str] = []
    for path in INPUT_FILES:
        relative = Path(os.path.relpath(path, ROOT)).as_posix()
        if path.is_symlink() or not path.is_file():
            problems.append(
                f"verification input is missing, nonregular, or a symlink: "
                f"{relative}"
            )
        else:
            rows.append((relative, path.stat().st_size, file_sha256(path)))
    for input_root in INPUT_ROOTS:
        if not input_root.is_dir() or input_root.is_symlink():
            problems.append(
                f"input root is missing, not a directory, or a symlink: "
                f"{Path(os.path.relpath(input_root, ROOT)).as_posix()}"
            )
            continue
        for path in sorted(input_root.rglob("*"), key=lambda item: item.as_posix()):
            relative = Path(os.path.relpath(path, ROOT))
            if (
                any(part in EXCLUDED_PARTS for part in relative.parts)
                or path.name in EXCLUDED_NAMES
                or (
                    input_root == ROOT.parent / "TranslationReport"
                    and path.name in EXCLUDED_TRANSLATION_RECORDS
                )
                or path.name.startswith("Icon")
                or path.suffix in EXCLUDED_SUFFIXES
            ):
                continue
            if path.is_symlink():
                problems.append(f"verification input is a symlink: {relative}")
            elif path.is_file():
                rows.append((relative.as_posix(), path.stat().st_size, file_sha256(path)))
            elif not path.is_dir():
                problems.append(f"verification input has unsupported type: {relative}")
    return sorted(rows), problems


def render(rows: list[tuple[str, int, str]]) -> bytes:
    lines = ["path\tbytes\tsha256"]
    lines.extend(f"{path}\t{size}\t{digest}" for path, size, digest in rows)
    return ("\n".join(lines) + "\n").encode("utf-8")


def top_digest(payload: bytes) -> str:
    return hashlib.sha256(payload).hexdigest()


def summary_text(count: int, digest: str) -> str:
    return (
        "VERIFICATION INPUT MANIFEST: PASS\n"
        f"FILES {count}\n"
        f"TOP_LEVEL_SHA256 {digest}\n"
    )


def atomic_write(path: Path, payload: bytes) -> None:
    temporary = path.with_name(f"{path.name}.tmp.{os.getpid()}")
    temporary.write_bytes(payload)
    os.replace(temporary, path)


def main() -> int:
    if len(sys.argv) != 2 or sys.argv[1] not in {"write", "check"}:
        print(f"usage: {SCRIPT.name} write|check", file=sys.stderr)
        return 2
    if LOGS.is_symlink() or (LOGS.exists() and not LOGS.is_dir()):
        print(
            "PROBLEM verification logs path is not a real directory",
            file=sys.stderr,
        )
        print("VERIFICATION INPUT MANIFEST: FAIL", file=sys.stderr)
        return 1
    rows, problems = inventory()
    payload = render(rows)
    digest = top_digest(payload)
    summary = summary_text(len(rows), digest)
    if problems:
        for problem in problems:
            print(f"PROBLEM {problem}", file=sys.stderr)
        print("VERIFICATION INPUT MANIFEST: FAIL", file=sys.stderr)
        return 1

    if sys.argv[1] == "write":
        LOGS.mkdir(parents=True, exist_ok=True)
        atomic_write(MANIFEST, payload)
        atomic_write(SUMMARY, summary.encode("utf-8"))
    else:
        if not MANIFEST.is_file() or MANIFEST.is_symlink():
            print("PROBLEM missing or symlinked verification input manifest")
            print("VERIFICATION INPUT MANIFEST: FAIL")
            return 1
        if not SUMMARY.is_file() or SUMMARY.is_symlink():
            print("PROBLEM missing or symlinked verification input summary")
            print("VERIFICATION INPUT MANIFEST: FAIL")
            return 1
        if MANIFEST.read_bytes() != payload:
            print("PROBLEM verification inputs differ from the pinned manifest")
            print("VERIFICATION INPUT MANIFEST: FAIL")
            return 1
        if SUMMARY.read_text(encoding="utf-8") != summary:
            print("PROBLEM verification input summary differs from measurement")
            print("VERIFICATION INPUT MANIFEST: FAIL")
            return 1

    print(summary, end="")
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
