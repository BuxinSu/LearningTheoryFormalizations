#!/usr/bin/env python3
"""Create or verify the immutable source-state manifest for this audit."""

from __future__ import annotations

import argparse
import hashlib
from pathlib import Path
import sys


SCRIPT = Path(__file__).resolve()
VERIFY = SCRIPT.parent.parent
ROOT = VERIFY.parent.parent
MANIFEST = VERIFY / "logs" / "source_manifest.txt"

EXCLUDED_PREFIXES = (
    Path(".lake"),
    Path("MatrixConcentration/Verification"),
    Path(".audit_work"),
)
CONTROL_FILES = (
    Path("lakefile.toml"),
    Path("lake-manifest.json"),
    Path("lean-toolchain"),
    Path("MatrixConcentration/README.md"),
    Path("MatrixConcentration/APPENDIX_SUMMARY.md"),
)


def is_excluded(relative: Path) -> bool:
    return any(relative == prefix or prefix in relative.parents for prefix in EXCLUDED_PREFIXES)


def has_symlink_component(relative: Path) -> bool:
    current = ROOT
    for part in relative.parts:
        current = current / part
        if current.is_symlink():
            return True
    return False


def selected_files() -> list[Path]:
    universe: list[Path] = []
    for path in ROOT.rglob("*.lean"):
        relative = path.relative_to(ROOT)
        if not is_excluded(relative):
            universe.append(relative)
    selected = sorted(set(universe).union(CONTROL_FILES), key=lambda p: p.as_posix())
    invalid = [
        path
        for path in selected
        if not (ROOT / path).is_file() or has_symlink_component(path)
    ]
    if invalid:
        raise SystemExit(
            "missing, nonregular, or symlinked manifest inputs: "
            + ", ".join(map(str, invalid))
        )
    return selected


def digest(path: Path) -> str:
    h = hashlib.sha256()
    with path.open("rb") as handle:
        for block in iter(lambda: handle.read(1024 * 1024), b""):
            h.update(block)
    return h.hexdigest()


def data_lines() -> list[str]:
    return [f"{digest(ROOT / path)}  {path.as_posix()}" for path in selected_files()]


def top_digest(lines: list[str]) -> str:
    payload = "".join(f"{line}\n" for line in lines).encode()
    return hashlib.sha256(payload).hexdigest()


def write_manifest() -> int:
    lines = data_lines()
    manifest_text = "\n".join(
        [
            "# SHA-256 source-state manifest",
            "# Universe: every project-root .lean file excluding .lake/**,",
            "# MatrixConcentration/Verification/**, and .audit_work/**;",
            "# plus toolchain/build metadata and the two source-dir claims documents.",
            *lines,
            f"TOP_LEVEL_SHA256  {top_digest(lines)}",
            "",
        ]
    )
    MANIFEST.parent.mkdir(parents=True, exist_ok=True)
    MANIFEST.write_text(manifest_text, encoding="utf-8")
    print(f"WROTE {MANIFEST.relative_to(ROOT)}")
    print(f"FILES {len(lines)}")
    print(f"TOP_LEVEL_SHA256 {top_digest(lines)}")
    return 0


def read_recorded() -> tuple[list[str], str]:
    if not MANIFEST.is_file() or MANIFEST.is_symlink():
        raise SystemExit(f"manifest is missing, nonregular, or symlinked: {MANIFEST}")
    lines = MANIFEST.read_text(encoding="utf-8").splitlines()
    data = [line for line in lines if line and not line.startswith("#") and not line.startswith("TOP_LEVEL_")]
    top = next(
        (line.split(maxsplit=1)[1] for line in lines if line.startswith("TOP_LEVEL_SHA256 ")),
        "",
    )
    return data, top


def check_manifest() -> int:
    recorded, recorded_top = read_recorded()
    current = data_lines()
    current_top = top_digest(current)
    if recorded != current or recorded_top != current_top:
        print("SOURCE MANIFEST DRIFT: FAIL")
        old = set(recorded)
        new = set(current)
        for line in sorted(old - new):
            print(f"- {line}")
        for line in sorted(new - old):
            print(f"+ {line}")
        if recorded_top != current_top:
            print(f"RECORDED_TOP {recorded_top}")
            print(f"CURRENT_TOP  {current_top}")
        return 1
    print("SOURCE MANIFEST: PASS")
    print(f"FILES {len(current)}")
    print(f"TOP_LEVEL_SHA256 {current_top}")
    return 0


def main() -> int:
    parser = argparse.ArgumentParser()
    parser.add_argument("mode", choices=("write", "check"))
    args = parser.parse_args()
    return write_manifest() if args.mode == "write" else check_manifest()


if __name__ == "__main__":
    sys.exit(main())
