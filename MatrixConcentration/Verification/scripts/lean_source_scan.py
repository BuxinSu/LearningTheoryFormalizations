#!/usr/bin/env python3
"""Shared file-universe and lexical-context support for V3 and V5.

The scanner deliberately works from source text instead of stripping comments:
every hit remains visible in evidence, while each byte is classified as Lean
code, a line comment, an ordinary block comment, a documentation comment, or a
string literal.  This makes a clean code-level result auditable without losing
mentions that a plain grep would either hide or misclassify.
"""

from __future__ import annotations

from dataclasses import dataclass
from pathlib import Path
import re
from typing import Iterable, Iterator, Pattern


SCRIPT = Path(__file__).resolve()
VERIFY = SCRIPT.parent.parent
ROOT = VERIFY.parent.parent
WORK = ROOT / ".audit_work"
LOGS = VERIFY / "logs"

CONTEXT_NAMES = {
    0: "code",
    1: "line_comment",
    2: "block_comment",
    3: "doc_comment",
    4: "string",
}


@dataclass(frozen=True)
class Hit:
    path: Path
    line: int
    column: int
    pattern: str
    matched: str
    context: str
    snippet: str


def relative(path: Path) -> str:
    """Return a stable project-root-relative POSIX path."""

    try:
        return path.resolve().relative_to(ROOT.resolve()).as_posix()
    except ValueError:
        return path.resolve().as_posix()


def is_excluded(relative_path: Path) -> bool:
    """Apply the reference's FILE-WALK UNIVERSE exclusions verbatim."""

    parts = relative_path.parts
    if not parts:
        return False
    if parts[0] in {".lake", ".audit_work"}:
        return True
    return (
        len(parts) >= 2
        and parts[0] == "MatrixConcentration"
        and parts[1] == "Verification"
    )


def lean_universe() -> list[Path]:
    """Enumerate every in-scope Lean file, with no expected-count shortcut."""

    files: list[Path] = []
    for path in ROOT.rglob("*.lean"):
        rel = path.relative_to(ROOT)
        if not is_excluded(rel):
            files.append(path)
    return sorted(files, key=relative)


def lexical_contexts(text: str) -> bytearray:
    """Classify source bytes while respecting nested Lean block comments.

    The result uses the integer keys in ``CONTEXT_NAMES``.  Block comments can
    nest in Lean; the outer comment determines whether a span is recorded as a
    documentation comment.  Strings inside comments are comment text, and
    comment markers inside strings are string text.
    """

    contexts = bytearray(len(text))
    i = 0
    n = len(text)
    while i < n:
        if text.startswith("--", i):
            end = text.find("\n", i + 2)
            if end < 0:
                end = n
            contexts[i:end] = bytes([1]) * (end - i)
            i = end
            continue

        if text.startswith("/-", i):
            outer_kind = 3 if text.startswith(("/--", "/-!"), i) else 2
            start = i
            depth = 1
            i += 2
            while i < n and depth:
                if text.startswith("/-", i):
                    depth += 1
                    i += 2
                elif text.startswith("-/", i):
                    depth -= 1
                    i += 2
                else:
                    i += 1
            contexts[start:i] = bytes([outer_kind]) * (i - start)
            continue

        if text[i] == '"':
            start = i
            i += 1
            while i < n:
                if text[i] == "\\":
                    i = min(n, i + 2)
                elif text[i] == '"':
                    i += 1
                    break
                else:
                    i += 1
            contexts[start:i] = bytes([4]) * (i - start)
            continue

        i += 1
    return contexts


def line_column(text: str, offset: int) -> tuple[int, int]:
    line = text.count("\n", 0, offset) + 1
    line_start = text.rfind("\n", 0, offset) + 1
    return line, offset - line_start + 1


def line_snippet(text: str, offset: int) -> str:
    start = text.rfind("\n", 0, offset) + 1
    end = text.find("\n", offset)
    if end < 0:
        end = len(text)
    return text[start:end].strip().replace("\t", " ")


def find_hits(
    paths: Iterable[Path],
    patterns: Iterable[tuple[str, Pattern[str]]],
) -> Iterator[Hit]:
    """Yield all regex hits, retaining lexical context and source location."""

    for path in paths:
        text = path.read_text(encoding="utf-8")
        contexts = lexical_contexts(text)
        for pattern_name, regex in patterns:
            for match in regex.finditer(text):
                offset = match.start()
                line, column = line_column(text, offset)
                context = CONTEXT_NAMES[contexts[offset]] if contexts else "code"
                yield Hit(
                    path=path,
                    line=line,
                    column=column,
                    pattern=pattern_name,
                    matched=match.group(0),
                    context=context,
                    snippet=line_snippet(text, offset),
                )


def compile_pattern(expression: str, *, ignore_case: bool = False) -> Pattern[str]:
    flags = re.MULTILINE | (re.IGNORECASE if ignore_case else 0)
    return re.compile(expression, flags)


def tsv_safe(value: object) -> str:
    return str(value).replace("\t", " ").replace("\r", " ").replace("\n", " ")

