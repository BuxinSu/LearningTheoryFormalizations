from __future__ import annotations

import re
from pathlib import Path

PATTERNS = {
    "sorry": re.compile(r"\bsorry\b"),
    "admit": re.compile(r"\badmit\b"),
    "axiom": re.compile(r"^\s*axiom\s+", re.MULTILINE),
    "constant": re.compile(r"^\s*constant\s+", re.MULTILINE),
    "todo": re.compile(r"\b(?:TODO|FIXME)\b"),
}


def _mask_comments_and_strings(text: str) -> str:
    """Preserve offsets/newlines while masking Lean comments and string literals."""
    chars = list(text)
    index = 0
    block_depth = 0
    in_line = False
    in_string = False
    while index < len(text):
        if in_line:
            if text[index] == "\n":
                in_line = False
            else:
                chars[index] = " "
            index += 1
            continue
        if block_depth:
            if text.startswith("/-", index):
                chars[index:index + 2] = [" ", " "]
                block_depth += 1
                index += 2
            elif text.startswith("-/", index):
                chars[index:index + 2] = [" ", " "]
                block_depth -= 1
                index += 2
            else:
                if text[index] != "\n":
                    chars[index] = " "
                index += 1
            continue
        if in_string:
            if text[index] == "\\" and index + 1 < len(text):
                chars[index:index + 2] = [" ", " "]
                index += 2
            elif text[index] == '"':
                chars[index] = " "
                in_string = False
                index += 1
            else:
                if text[index] != "\n":
                    chars[index] = " "
                index += 1
            continue
        if text.startswith("--", index):
            chars[index:index + 2] = [" ", " "]
            in_line = True
            index += 2
        elif text.startswith("/-", index):
            chars[index:index + 2] = [" ", " "]
            block_depth = 1
            index += 2
        elif text[index] == '"':
            chars[index] = " "
            in_string = True
            index += 1
        else:
            index += 1
    return "".join(chars)


def scan_placeholders(root: Path) -> list[dict[str, object]]:
    findings: list[dict[str, object]] = []
    for path in sorted(root.rglob("*.lean")):
        if any(part in {".lake", ".git"} for part in path.parts):
            continue
        text = path.read_text(encoding="utf-8", errors="replace")
        code = _mask_comments_and_strings(text)
        lines = text.splitlines()
        for kind, pattern in PATTERNS.items():
            for match in pattern.finditer(code):
                line = text.count("\n", 0, match.start()) + 1
                excerpt = lines[line - 1].strip()
                context = "\n".join(lines[max(0, line - 9):line])
                findings.append({
                    "kind": kind, "path": str(path), "line": line,
                    "excerpt": excerpt, "context": context,
                })
    return findings


def unregistered_placeholders(findings: list[dict[str, object]]) -> list[dict[str, object]]:
    allowed_tags = (
        "EXERCISE-SORRY", "EXTERNAL-SORRY", "FORWARD-SORRY-", "UNRESOLVED-PROOF-",
    )
    return [
        finding for finding in findings
        if (
            finding["kind"] in {"admit", "axiom", "constant"}
            or (
                finding["kind"] == "sorry"
                and not any(
                    tag in str(finding.get("context", finding["excerpt"]))
                    for tag in allowed_tags
                )
            )
        )
    ]

PROP_SPEC_RE = re.compile(
    r"^[ \t]*(?:def|abbrev)[ \t]+([A-Za-z0-9_'.]+)(?:[ \t]+[^:\n]+)?[ \t]*:[ \t]*Prop[ \t]*:=",
    re.MULTILINE,
)


def scan_theorem_shaped_propositions(root: Path) -> list[dict[str, object]]:
    """Find proposition specifications that look like unproved theorem coverage."""
    results: list[dict[str, object]] = []
    for path in sorted(root.rglob("*.lean")):
        if any(part in {".lake", ".git"} for part in path.parts):
            continue
        text = path.read_text(encoding="utf-8", errors="replace")
        code = _mask_comments_and_strings(text)
        lines = text.splitlines()
        for match in PROP_SPEC_RE.finditer(code):
            line = text.count("\n", 0, match.start()) + 1
            context = "\n".join(lines[max(0, line - 9):line])
            linked = any(tag in context for tag in (
                "SPEC-OBLIGATION-", "UNRESOLVED-PROOF-", "FORWARD-SORRY-",
                "EXERCISE-SORRY", "EXTERNAL-SORRY",
            ))
            results.append({
                "kind": "proposition_specification", "name": match.group(1),
                "path": str(path), "line": line, "excerpt": lines[line - 1].strip(),
                "context": context, "registered": linked,
            })
    return results


def unregistered_proposition_specifications(findings: list[dict[str, object]]) -> list[dict[str, object]]:
    return [finding for finding in findings if not finding.get("registered")]
