from __future__ import annotations

import json
import re
from pathlib import Path
from typing import Any

SECRET_PATTERN = re.compile(r"(?i)(api[_-]?key|authorization|bearer)([\s\"':=]+)([^\s\"']+)")


def redact(value: str) -> str:
    return SECRET_PATTERN.sub(r"\1\2<redacted>", value)


def append_jsonl(path: Path, value: Any) -> None:
    path.parent.mkdir(parents=True, exist_ok=True)
    with path.open("a", encoding="utf-8") as handle:
        handle.write(redact(json.dumps(value, default=str)) + "\n")

