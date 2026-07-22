#!/usr/bin/env python3
"""Emit a deterministic content manifest for one filesystem tree."""

from __future__ import annotations

import hashlib
import os
import sys
from pathlib import Path


def digest_file(path: Path) -> str:
    digest = hashlib.sha256()
    with path.open("rb") as stream:
        for block in iter(lambda: stream.read(1024 * 1024), b""):
            digest.update(block)
    return digest.hexdigest()


def main() -> int:
    if len(sys.argv) != 2:
        print(f"usage: {Path(sys.argv[0]).name} TREE", file=sys.stderr)
        return 2

    root = Path(sys.argv[1]).resolve()
    if not root.is_dir():
        print(f"not a directory: {root}", file=sys.stderr)
        return 1

    print(f"ROOT\t{root}")
    for path in sorted(root.rglob("*"), key=lambda item: item.as_posix()):
        relative = path.relative_to(root).as_posix()
        if path.is_symlink():
            print(f"SYMLINK\t{relative}\t{os.readlink(path)}")
        elif path.is_file():
            print(f"FILE\t{relative}\t{path.stat().st_size}\t{digest_file(path)}")
        elif path.is_dir():
            print(f"DIR\t{relative}")
        else:
            print(f"OTHER\t{relative}")
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
