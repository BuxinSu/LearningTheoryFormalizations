#!/usr/bin/env python3
"""Create or verify the source-state SHA-256 manifest used by this pass."""

from __future__ import annotations

import argparse
import hashlib
import sys
from pathlib import Path

from file_universe import ROOT, enumerate_universe


EXTRA_FILES = (
    "HighDimensionalProbability.lean",
    "lakefile.toml",
    "lake-manifest.json",
    "lean-toolchain",
)


def sha256_file(path: Path) -> str:
    digest = hashlib.sha256()
    with path.open("rb") as handle:
        for chunk in iter(lambda: handle.read(1024 * 1024), b""):
            digest.update(chunk)
    return digest.hexdigest()


def build_manifest() -> tuple[str, str]:
    universe = enumerate_universe()
    library = universe["file_walk_universe"]
    assert isinstance(library, list)
    paths = sorted(set(str(path) for path in library).union(EXTRA_FILES))
    missing = [path for path in paths if not (ROOT / path).is_file()]
    if missing:
        raise RuntimeError("manifest inputs missing: " + ", ".join(missing))
    body = "".join(f"{sha256_file(ROOT / path)}  {path}\n" for path in paths)
    top = hashlib.sha256(body.encode("utf-8")).hexdigest()
    rendered = (
        "# SHA-256 source-state manifest\n"
        f"# project_root: {ROOT}\n"
        "# universe: HDP/**/*.lean excluding Verification/**, "
        "MatrixConcentration/**/*.lean via the real directory, plus the HDP root module "
        "and Lake/toolchain pins\n"
        f"# entries: {len(paths)}\n"
        f"# digest_of_digests: {top}\n"
        f"{body}"
    )
    return rendered, top


def main() -> int:
    parser = argparse.ArgumentParser()
    group = parser.add_mutually_exclusive_group(required=True)
    group.add_argument("--write", type=Path, metavar="PATH")
    group.add_argument("--check", type=Path, metavar="PATH")
    group.add_argument("--print", action="store_true", dest="print_manifest")
    args = parser.parse_args()

    rendered, top = build_manifest()
    if args.write is not None:
        destination = args.write
        if not destination.is_absolute():
            destination = ROOT / destination
        destination.parent.mkdir(parents=True, exist_ok=True)
        destination.write_text(rendered, encoding="utf-8")
        print(f"wrote {destination}")
        print(f"digest_of_digests: {top}")
        return 0
    if args.check is not None:
        expected_path = args.check
        if not expected_path.is_absolute():
            expected_path = ROOT / expected_path
        if not expected_path.is_file():
            print(f"manifest missing: {expected_path}", file=sys.stderr)
            return 2
        expected = expected_path.read_text(encoding="utf-8")
        if expected != rendered:
            print("SOURCE MANIFEST DRIFT", file=sys.stderr)
            print(f"expected manifest: {expected_path}", file=sys.stderr)
            print(f"current digest_of_digests: {top}", file=sys.stderr)
            return 1
        print("SOURCE MANIFEST OK")
        print(f"digest_of_digests: {top}")
        return 0
    print(rendered, end="")
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
