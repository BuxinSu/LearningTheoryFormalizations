from __future__ import annotations

import re
from pathlib import Path

from ...domain import ChapterRecord, ValidationCheck


def _without_comments(text: str) -> str:
    output: list[str] = []
    for line in text.splitlines():
        kept: list[str] = []
        for index, char in enumerate(line):
            if char == "%":
                preceding = 0
                cursor = index - 1
                while cursor >= 0 and line[cursor] == "\\":
                    preceding += 1
                    cursor -= 1
                if preceding % 2 == 0:
                    break
            kept.append(char)
        output.append("".join(kept))
    return "\n".join(output)


def _brace_counts(text: str) -> tuple[int, int]:
    opens = closes = 0
    cleaned = _without_comments(text)
    for index, char in enumerate(cleaned):
        if char not in "{}":
            continue
        preceding = 0
        cursor = index - 1
        while cursor >= 0 and cleaned[cursor] == "\\":
            preceding += 1
            cursor -= 1
        if preceding % 2 == 1:
            continue
        if char == "{":
            opens += 1
        else:
            closes += 1
    return opens, closes


def validate_tex_tree(tex_root: Path, chapters: list[ChapterRecord]) -> list[ValidationCheck]:
    files = sorted(tex_root.rglob("*.tex"))
    combined = "\n".join(path.read_text(encoding="utf-8", errors="replace") for path in files)
    opens, closes = _brace_counts(combined)
    checks = [
        ValidationCheck(name="tex_files_present", passed=bool(files), details=f"found {len(files)} TeX files"),
        ValidationCheck(name="chapters_detected", passed=bool(chapters), details=f"detected {len(chapters)} numbered chapters"),
        ValidationCheck(
            name="brace_balance", passed=opens == closes,
            details=f"unescaped, uncommented open={opens} close={closes}",
        ),
    ]
    labels = set(re.findall(r"\\label\{([^}]+)\}", combined))
    references = set(re.findall(r"\\(?:eqref|ref|autoref)\{([^}]+)\}", combined))
    missing = sorted(references - labels)
    checks.append(ValidationCheck(
        name="reference_integrity", passed=not missing,
        details="all references resolved" if not missing else f"unresolved labels: {', '.join(missing[:50])}",
    ))
    uncertainties = combined.count("\\AutoFormalUncertain{")
    checks.append(ValidationCheck(
        name="uncertainties_absent", passed=uncertainties == 0,
        details=f"found {uncertainties} explicit conversion uncertainties",
    ))
    return checks
