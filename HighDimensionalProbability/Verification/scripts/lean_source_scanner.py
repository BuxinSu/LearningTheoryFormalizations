#!/usr/bin/env python3
"""Shared lexer-aware source scanner for the V3 and V5 verification passes.

The scanner always records raw textual matches with their source context.  It
also masks Lean line comments, nested block comments, and string literals
without changing offsets, allowing every hit to be labelled ``in_code``.
Reports can therefore retain prose/ledger evidence without confusing it with
an executable occurrence.
"""

from __future__ import annotations

import argparse
import bisect
import json
import re
import sys
from dataclasses import asdict, dataclass
from pathlib import Path
from typing import Iterable, Sequence

from file_universe import ROOT, enumerate_universe


@dataclass(frozen=True)
class ScanPattern:
    """One named scanner detector."""

    pattern_id: str
    category: str
    expression: str
    description: str
    flags: int = re.MULTILINE

    def compile(self) -> re.Pattern[str]:
        return re.compile(self.expression, self.flags)


@dataclass(frozen=True)
class LexDiagnostic:
    path: str
    kind: str
    line: int
    column: int
    message: str


@dataclass(frozen=True)
class ScanHit:
    profile: str
    pattern_id: str
    category: str
    path: str
    line: int
    column: int
    in_code: bool
    matched_text: str
    context: str


def _mask_character(buffer: list[str], index: int) -> None:
    if buffer[index] not in "\r\n":
        buffer[index] = " "


def mask_lean_noncode(text: str) -> tuple[str, list[tuple[str, int]]]:
    """Mask comments and strings while preserving every source offset.

    Lean block comments nest.  String escapes are handled so comment markers
    inside strings and quote characters after a backslash do not change lexer
    state.  Character literals need no special treatment for these scanners:
    none of the searched tokens can fit in a single Lean character literal.
    """

    masked = list(text)
    diagnostics: list[tuple[str, int]] = []
    index = 0
    state = "code"
    block_depth = 0
    state_start = 0

    while index < len(text):
        if state == "code":
            if text.startswith("--", index):
                state = "line_comment"
                state_start = index
                _mask_character(masked, index)
                if index + 1 < len(text):
                    _mask_character(masked, index + 1)
                index += 2
            elif text.startswith("/-", index):
                state = "block_comment"
                block_depth = 1
                state_start = index
                _mask_character(masked, index)
                if index + 1 < len(text):
                    _mask_character(masked, index + 1)
                index += 2
            elif text[index] == '"':
                state = "string"
                state_start = index
                _mask_character(masked, index)
                index += 1
            else:
                index += 1
        elif state == "line_comment":
            if text[index] in "\r\n":
                state = "code"
            else:
                _mask_character(masked, index)
            index += 1
        elif state == "block_comment":
            if text.startswith("/-", index):
                block_depth += 1
                _mask_character(masked, index)
                if index + 1 < len(text):
                    _mask_character(masked, index + 1)
                index += 2
            elif text.startswith("-/", index):
                block_depth -= 1
                _mask_character(masked, index)
                if index + 1 < len(text):
                    _mask_character(masked, index + 1)
                index += 2
                if block_depth == 0:
                    state = "code"
            else:
                _mask_character(masked, index)
                index += 1
        else:
            assert state == "string"
            if text[index] == "\\":
                _mask_character(masked, index)
                index += 1
                if index < len(text):
                    _mask_character(masked, index)
                    index += 1
            elif text[index] == '"':
                _mask_character(masked, index)
                index += 1
                state = "code"
            else:
                _mask_character(masked, index)
                index += 1

    if state == "block_comment":
        diagnostics.append(("unterminated_block_comment", state_start))
    elif state == "string":
        diagnostics.append(("unterminated_string", state_start))
    return "".join(masked), diagnostics


def _line_starts(text: str) -> list[int]:
    starts = [0]
    starts.extend(match.end() for match in re.finditer(r"\n", text))
    return starts


def _location(starts: Sequence[int], offset: int) -> tuple[int, int]:
    line_index = bisect.bisect_right(starts, offset) - 1
    return line_index + 1, offset - starts[line_index] + 1


def _context_line(text: str, starts: Sequence[int], line: int) -> str:
    start = starts[line - 1]
    end = text.find("\n", start)
    if end < 0:
        end = len(text)
    return text[start:end].rstrip("\r")


def scan_text(
    *,
    profile: str,
    relative_path: str,
    text: str,
    patterns: Sequence[ScanPattern],
) -> tuple[list[ScanHit], list[LexDiagnostic]]:
    """Scan one source string and return raw hits labelled by lexer state."""

    code_text, raw_diagnostics = mask_lean_noncode(text)
    starts = _line_starts(text)
    hits: list[ScanHit] = []

    for pattern in patterns:
        compiled = pattern.compile()
        code_spans = {
            (match.start(), match.end()) for match in compiled.finditer(code_text)
        }
        for match in compiled.finditer(text):
            line, column = _location(starts, match.start())
            hits.append(
                ScanHit(
                    profile=profile,
                    pattern_id=pattern.pattern_id,
                    category=pattern.category,
                    path=relative_path,
                    line=line,
                    column=column,
                    in_code=(match.start(), match.end()) in code_spans,
                    matched_text=match.group(0),
                    context=_context_line(text, starts, line),
                )
            )

    diagnostics = []
    for kind, offset in raw_diagnostics:
        line, column = _location(starts, offset)
        diagnostics.append(
            LexDiagnostic(
                path=relative_path,
                kind=kind,
                line=line,
                column=column,
                message=f"{kind.replace('_', ' ')} beginning here",
            )
        )
    hits.sort(
        key=lambda hit: (
            hit.path,
            hit.line,
            hit.column,
            hit.pattern_id,
            not hit.in_code,
        )
    )
    return hits, diagnostics


def scan_paths(
    *,
    profile: str,
    paths: Iterable[Path],
    patterns: Sequence[ScanPattern],
) -> tuple[list[ScanHit], list[LexDiagnostic]]:
    all_hits: list[ScanHit] = []
    all_diagnostics: list[LexDiagnostic] = []
    selected = sorted({item.absolute() for item in paths})
    for path in selected:
        if (
            path.is_symlink()
            or path.resolve() != path
            or not path.is_file()
        ):
            raise ValueError(f"scanner input is not a physical regular file: {path}")
        try:
            relative = path.relative_to(ROOT).as_posix()
        except ValueError:
            relative = path.as_posix()
        text = path.read_text(encoding="utf-8")
        hits, diagnostics = scan_text(
            profile=profile,
            relative_path=relative,
            text=text,
            patterns=patterns,
        )
        all_hits.extend(hits)
        all_diagnostics.extend(diagnostics)
    all_hits.sort(
        key=lambda hit: (
            hit.path,
            hit.line,
            hit.column,
            hit.pattern_id,
            not hit.in_code,
        )
    )
    all_diagnostics.sort(
        key=lambda diagnostic: (
            diagnostic.path,
            diagnostic.line,
            diagnostic.column,
            diagnostic.kind,
        )
    )
    return all_hits, all_diagnostics


def paths_for_scope(scope: str) -> list[Path]:
    universe = enumerate_universe()
    if scope == "library":
        selected = universe["file_walk_universe"]
    elif scope == "scratch":
        selected = list(universe["tmp_scratch"]) + list(
            universe["audit_work_scratch"]
        )
    elif scope == "all":
        selected = (
            list(universe["file_walk_universe"])
            + list(universe["tmp_scratch"])
            + list(universe["audit_work_scratch"])
        )
    else:
        raise ValueError(f"unknown scanner scope: {scope}")
    assert isinstance(selected, list)
    return [ROOT / str(path) for path in selected]


def _summary(
    *,
    profile: str,
    scope: str,
    paths: Sequence[Path],
    patterns: Sequence[ScanPattern],
    hits: Sequence[ScanHit],
    diagnostics: Sequence[LexDiagnostic],
) -> dict[str, object]:
    by_pattern: dict[str, dict[str, int]] = {}
    for pattern in patterns:
        raw = sum(hit.pattern_id == pattern.pattern_id for hit in hits)
        code = sum(
            hit.pattern_id == pattern.pattern_id and hit.in_code for hit in hits
        )
        by_pattern[pattern.pattern_id] = {"raw": raw, "code": code}
    return {
        "profile": profile,
        "scope": scope,
        "file_walk_rules": enumerate_universe()["rules"],
        "scanned_file_count": len(paths),
        "raw_hit_count": len(hits),
        "code_hit_count": sum(hit.in_code for hit in hits),
        "lex_diagnostic_count": len(diagnostics),
        "by_pattern": by_pattern,
    }


def render_json(
    *,
    summary: dict[str, object],
    hits: Sequence[ScanHit],
    diagnostics: Sequence[LexDiagnostic],
) -> str:
    return (
        json.dumps(
            {
                "summary": summary,
                "hits": [asdict(hit) for hit in hits],
                "lex_diagnostics": [
                    asdict(diagnostic) for diagnostic in diagnostics
                ],
            },
            indent=2,
            sort_keys=True,
        )
        + "\n"
    )


def _clean_tsv(value: object) -> str:
    return str(value).replace("\\", "\\\\").replace("\t", "\\t").replace(
        "\n", "\\n"
    )


def render_tsv(
    hits: Sequence[ScanHit], diagnostics: Sequence[LexDiagnostic]
) -> str:
    lines = [
        "record\tprofile\tpattern_id\tcategory\tin_code\tpath\tline\tcolumn\tmatch\tcontext"
    ]
    for hit in hits:
        fields = (
            "hit",
            hit.profile,
            hit.pattern_id,
            hit.category,
            str(hit.in_code).lower(),
            hit.path,
            hit.line,
            hit.column,
            hit.matched_text,
            hit.context,
        )
        lines.append("\t".join(_clean_tsv(field) for field in fields))
    for diagnostic in diagnostics:
        fields = (
            "lex_diagnostic",
            "",
            diagnostic.kind,
            "lexer",
            "",
            diagnostic.path,
            diagnostic.line,
            diagnostic.column,
            "",
            diagnostic.message,
        )
        lines.append("\t".join(_clean_tsv(field) for field in fields))
    return "\n".join(lines) + "\n"


def render_text(
    *,
    summary: dict[str, object],
    hits: Sequence[ScanHit],
    diagnostics: Sequence[LexDiagnostic],
) -> str:
    lines = [
        f"profile: {summary['profile']}",
        f"scope: {summary['scope']}",
        f"scanned_file_count: {summary['scanned_file_count']}",
        f"raw_hit_count: {summary['raw_hit_count']}",
        f"code_hit_count: {summary['code_hit_count']}",
        f"lex_diagnostic_count: {summary['lex_diagnostic_count']}",
        "",
    ]
    for hit in hits:
        state = "CODE" if hit.in_code else "NONCODE"
        lines.append(
            f"{hit.path}:{hit.line}:{hit.column}: "
            f"[{hit.pattern_id} {state}] {hit.context}"
        )
    for diagnostic in diagnostics:
        lines.append(
            f"{diagnostic.path}:{diagnostic.line}:{diagnostic.column}: "
            f"[LEXER {diagnostic.kind}] {diagnostic.message}"
        )
    return "\n".join(lines) + "\n"


def scanner_main(
    *,
    profile: str,
    patterns: Sequence[ScanPattern],
    argv: Sequence[str] | None = None,
) -> int:
    parser = argparse.ArgumentParser(
        description=f"Lexer-aware Lean source scanner for {profile}"
    )
    parser.add_argument(
        "--scope",
        choices=("library", "scratch", "all"),
        default="library",
        help="use the exact FILE-WALK library universe or separately enumerated scratch",
    )
    parser.add_argument(
        "--path",
        action="append",
        type=Path,
        help="scan only this explicit path (repeatable); overrides --scope",
    )
    parser.add_argument(
        "--format", choices=("json", "tsv", "text"), default="json"
    )
    parser.add_argument(
        "--code-only",
        action="store_true",
        help="emit executable-code hits only (raw counts remain in JSON summary)",
    )
    parser.add_argument(
        "--output",
        type=Path,
        help="write output here instead of stdout",
    )
    parser.add_argument(
        "--fail-on-lex-diagnostic",
        action="store_true",
        help="return nonzero for an unterminated comment or string",
    )
    args = parser.parse_args(argv)

    if args.path:
        selected = [
            path if path.is_absolute() else ROOT / path for path in args.path
        ]
        scope = "explicit-paths"
    else:
        selected = paths_for_scope(args.scope)
        scope = args.scope

    hits, diagnostics = scan_paths(
        profile=profile, paths=selected, patterns=patterns
    )
    summary = _summary(
        profile=profile,
        scope=scope,
        paths=selected,
        patterns=patterns,
        hits=hits,
        diagnostics=diagnostics,
    )
    emitted_hits = [hit for hit in hits if hit.in_code] if args.code_only else hits
    if args.format == "json":
        output = render_json(
            summary=summary, hits=emitted_hits, diagnostics=diagnostics
        )
    elif args.format == "tsv":
        output = render_tsv(emitted_hits, diagnostics)
    else:
        output = render_text(
            summary=summary, hits=emitted_hits, diagnostics=diagnostics
        )

    if args.output:
        output_path = args.output if args.output.is_absolute() else ROOT / args.output
        output_path.parent.mkdir(parents=True, exist_ok=True)
        output_path.write_text(output, encoding="utf-8")
    else:
        sys.stdout.write(output)
    return 1 if args.fail_on_lex_diagnostic and diagnostics else 0
