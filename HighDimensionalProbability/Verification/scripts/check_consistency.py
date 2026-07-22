#!/usr/bin/env python3
"""Cross-check the ten final Verification reports against ``README.md``.

This checker is intentionally static: it reads Markdown only and never invokes
Lean or Lake.  Report finding counts are recomputed from each report's
``## Findings`` table rather than trusted from a separately declared count.

The checked contract is:

* exactly the ten specification-named reports ``01_*.md`` through
  ``10_*.md`` exist, with no additional numbered report;
* every report has exactly one final ``**Verdict: ...**`` line;
* every report has one Findings table whose IDs are unique, report-local, and
  contiguous from ``Vn-F1``;
* severities are exactly CRITICAL, MAJOR, MINOR, or INFO, and every completed
  verdict obeys the fixed severity-to-verdict mapping;
* the README index has exactly one V1--V10 row and agrees with each report on
  verdict and C/M/m/I counts;
* every report finding occurs exactly once in the README findings summary
  with the same severity;
* index and findings-summary report links resolve to the corresponding final
  report; and
* no ``PENDING``, ``TBD``, or ``*_TO_FILL`` placeholder remains in the
  README or a final report.

Use ``--self-test`` for a self-contained synthetic positive/negative
calibration.  It writes only to temporary directories.
"""

from __future__ import annotations

import argparse
import re
import sys
import tempfile
from collections import Counter
from dataclasses import dataclass
from pathlib import Path
from typing import Callable, Iterable, Sequence
from urllib.parse import unquote, urlsplit


SCRIPT = Path(__file__).resolve()
VERIFY = SCRIPT.parent.parent
README_NAME = "README.md"
DEFAULT_LOG = Path("logs/consistency_check.txt")

EXPECTED_REPORTS = {
    1: "01_build_integrity.md",
    2: "02_import_graph.md",
    3: "03_sorry_audit.md",
    4: "04_axiom_audit.md",
    5: "05_escape_hatches.md",
    6: "06_vacuity_triviality.md",
    7: "07_definition_sanity.md",
    8: "08_linter_report.md",
    9: "09_readme_claims.md",
    10: "10_conditional_interfaces.md",
}
SEVERITIES = ("CRITICAL", "MAJOR", "MINOR", "INFO")
SEVERITY_INDEX = {name: index for index, name in enumerate(SEVERITIES)}
ALLOWED_VERDICTS = {
    "PASS",
    "PASS-WITH-NOTES",
    "ISSUES-FOUND",
    "INCOMPLETE",
}
VERDICT_LINE = re.compile(
    r"^\*\*Verdict:\s*([A-Z][A-Z-]*)\*\*\s*$", re.MULTILINE
)
FINDING_ID = re.compile(r"^V(10|[1-9])-F([1-9][0-9]*)$")
PLACEHOLDER = re.compile(
    r"\b(?:PENDING|TBD|[A-Z0-9_]*TO_FILL)\b",
    re.IGNORECASE,
)
HEADING = re.compile(r"^(#{1,6})\s+(.+?)\s*$")
MARKDOWN_LINK = re.compile(
    r"\[[^\]\n]+\]\(\s*(<[^>\n]+>|[^)\s]+)"
    r"(?:\s+(?:\"[^\"]*\"|'[^']*'|\([^)]*\)))?\s*\)"
)
EMPTY_FINDING_CELLS = {
    "",
    "-",
    "—",
    "none",
    "no finding",
    "no findings",
    "n/a",
}


@dataclass(frozen=True)
class Finding:
    finding_id: str
    severity: str
    line: int


@dataclass(frozen=True)
class Report:
    number: int
    path: Path
    verdict: str
    findings: tuple[Finding, ...]

    @property
    def counts(self) -> tuple[int, int, int, int]:
        measured = Counter(finding.severity for finding in self.findings)
        return tuple(measured[name] for name in SEVERITIES)  # type: ignore[return-value]


@dataclass(frozen=True)
class MarkdownTable:
    header: tuple[str, ...]
    header_line: int
    rows: tuple[tuple[int, tuple[str, ...]], ...]


@dataclass(frozen=True)
class IndexRow:
    number: int
    verdict: str
    counts: tuple[int, int, int, int]
    report_target: str
    line: int


@dataclass(frozen=True)
class ConsistencyResult:
    verification_dir: Path
    reports: dict[int, Report]
    index_rows: dict[int, IndexRow]
    summary_findings: dict[str, Finding]
    problems: tuple[str, ...]

    @property
    def passed(self) -> bool:
        return not self.problems


def _split_markdown_row(line: str) -> list[str] | None:
    """Split a GFM-style table row, respecting escapes and code spans."""

    stripped = line.strip()
    if "|" not in stripped:
        return None
    if stripped.startswith("|"):
        stripped = stripped[1:]
    if stripped.endswith("|") and not stripped.endswith(r"\|"):
        stripped = stripped[:-1]

    cells: list[str] = []
    current: list[str] = []
    code_ticks = 0
    index = 0
    while index < len(stripped):
        char = stripped[index]
        if char == "\\" and index + 1 < len(stripped):
            current.append(char)
            current.append(stripped[index + 1])
            index += 2
            continue
        if char == "`":
            end = index
            while end < len(stripped) and stripped[end] == "`":
                end += 1
            tick_count = end - index
            current.extend(stripped[index:end])
            if code_ticks == 0:
                code_ticks = tick_count
            elif code_ticks == tick_count:
                code_ticks = 0
            index = end
            continue
        if char == "|" and code_ticks == 0:
            cells.append("".join(current).strip())
            current = []
        else:
            current.append(char)
        index += 1
    cells.append("".join(current).strip())
    return cells


def _is_separator_row(cells: Sequence[str]) -> bool:
    return bool(cells) and all(
        re.fullmatch(r":?-{3,}:?", cell.replace(" ", "")) is not None
        for cell in cells
    )


def _find_tables(
    lines: Sequence[str], *, first_line_number: int = 1
) -> list[MarkdownTable]:
    tables: list[MarkdownTable] = []
    index = 0
    while index + 1 < len(lines):
        header = _split_markdown_row(lines[index])
        separator = _split_markdown_row(lines[index + 1])
        if (
            header is None
            or separator is None
            or len(header) != len(separator)
            or not _is_separator_row(separator)
        ):
            index += 1
            continue

        rows: list[tuple[int, tuple[str, ...]]] = []
        cursor = index + 2
        while cursor < len(lines):
            cells = _split_markdown_row(lines[cursor])
            if cells is None:
                break
            rows.append(
                (
                    first_line_number + cursor,
                    tuple(cells),
                )
            )
            cursor += 1
        tables.append(
            MarkdownTable(
                header=tuple(header),
                header_line=first_line_number + index,
                rows=tuple(rows),
            )
        )
        index = max(cursor, index + 2)
    return tables


def _plain_cell(cell: str) -> str:
    """Remove harmless Markdown wrappers used around IDs/severities."""

    value = cell.strip().replace(r"\|", "|")
    link = re.fullmatch(r"\[([^\]]+)\]\([^)]+\)", value)
    if link is not None:
        value = link.group(1).strip()
    previous = None
    while value != previous:
        previous = value
        value = re.sub(r"^(?:\*\*|__|`|~~)(.*)(?:\*\*|__|`|~~)$", r"\1", value)
        value = value.strip()
    return value


def _header(cell: str) -> str:
    value = _plain_cell(cell)
    value = re.sub(r"<[^>]+>", " ", value)
    return re.sub(r"\s+", " ", value).strip().casefold()


def _findings_section(
    text: str, path: Path, problems: list[str]
) -> tuple[list[str], int] | None:
    lines = text.splitlines()
    matches: list[tuple[int, int]] = []
    for index, line in enumerate(lines):
        heading = HEADING.match(line)
        if heading is None:
            continue
        title = re.sub(r"\s+#+\s*$", "", heading.group(2)).strip()
        if title.casefold() == "findings":
            matches.append((index, len(heading.group(1))))
    if len(matches) != 1:
        problems.append(
            f"{path.name}: expected exactly one 'Findings' section, "
            f"found {len(matches)}"
        )
        return None

    start, level = matches[0]
    end = len(lines)
    for index in range(start + 1, len(lines)):
        heading = HEADING.match(lines[index])
        if heading is not None and len(heading.group(1)) <= level:
            end = index
            break
    return lines[start + 1 : end], start + 2


def _finding_table(
    text: str, path: Path, problems: list[str]
) -> MarkdownTable | None:
    section = _findings_section(text, path, problems)
    if section is None:
        return None
    lines, first_line = section
    candidates: list[MarkdownTable] = []
    for table in _find_tables(lines, first_line_number=first_line):
        headers = [_header(cell) for cell in table.header]
        if "id" in headers and "severity" in headers:
            candidates.append(table)
    if len(candidates) != 1:
        problems.append(
            f"{path.name}: expected exactly one Findings table with ID and "
            f"Severity columns, found {len(candidates)}"
        )
        return None
    return candidates[0]


def _parse_report(
    number: int, path: Path, text: str, problems: list[str]
) -> Report | None:
    verdict_matches = list(VERDICT_LINE.finditer(text))
    if len(verdict_matches) != 1:
        problems.append(
            f"{path.name}: expected exactly one '**Verdict: ...**' line, "
            f"found {len(verdict_matches)}"
        )
        verdict = ""
    else:
        verdict = verdict_matches[0].group(1)
        if verdict not in ALLOWED_VERDICTS:
            problems.append(
                f"{path.name}: unsupported verdict {verdict!r}; expected one "
                f"of {sorted(ALLOWED_VERDICTS)}"
            )

    table = _finding_table(text, path, problems)
    findings: list[Finding] = []
    if table is not None:
        headers = [_header(cell) for cell in table.header]
        id_column = headers.index("id")
        severity_column = headers.index("severity")
        saw_empty_sentinel = False
        for line_number, cells in table.rows:
            if len(cells) != len(table.header):
                problems.append(
                    f"{path.name}:{line_number}: Findings row has "
                    f"{len(cells)} cells; header has {len(table.header)}"
                )
                continue
            finding_id = _plain_cell(cells[id_column])
            severity = _plain_cell(cells[severity_column]).upper()
            id_empty = finding_id.casefold() in EMPTY_FINDING_CELLS
            severity_empty = severity.casefold() in EMPTY_FINDING_CELLS
            if id_empty or severity_empty:
                if not (id_empty and severity_empty):
                    problems.append(
                        f"{path.name}:{line_number}: empty-finding sentinel "
                        "must occupy both ID and Severity cells"
                    )
                elif saw_empty_sentinel:
                    problems.append(
                        f"{path.name}:{line_number}: duplicate empty-finding "
                        "sentinel row"
                    )
                elif findings:
                    problems.append(
                        f"{path.name}:{line_number}: empty-finding sentinel "
                        "cannot coexist with numbered findings"
                    )
                saw_empty_sentinel = True
                continue

            match = FINDING_ID.fullmatch(finding_id)
            if match is None:
                problems.append(
                    f"{path.name}:{line_number}: malformed finding ID "
                    f"{finding_id!r}"
                )
                continue
            if int(match.group(1)) != number:
                problems.append(
                    f"{path.name}:{line_number}: finding {finding_id} belongs "
                    f"to V{match.group(1)}, not V{number}"
                )
            if severity not in SEVERITIES:
                problems.append(
                    f"{path.name}:{line_number}: unsupported severity "
                    f"{severity!r}"
                )
                continue
            if saw_empty_sentinel:
                problems.append(
                    f"{path.name}:{line_number}: numbered finding cannot "
                    "coexist with empty-finding sentinel"
                )
            findings.append(Finding(finding_id, severity, line_number))

    id_counts = Counter(finding.finding_id for finding in findings)
    for finding_id, count in sorted(id_counts.items()):
        if count > 1:
            problems.append(
                f"{path.name}: duplicate finding ID {finding_id} ({count} rows)"
            )
    suffixes = sorted(
        {
            int(match.group(2))
            for finding in findings
            if (match := FINDING_ID.fullmatch(finding.finding_id)) is not None
            and int(match.group(1)) == number
        }
    )
    if suffixes:
        expected_suffixes = set(range(1, max(suffixes) + 1))
        missing = sorted(expected_suffixes - set(suffixes))
        if missing:
            missing_ids = ", ".join(f"V{number}-F{suffix}" for suffix in missing)
            problems.append(
                f"{path.name}: missing finding IDs in contiguous sequence: "
                f"{missing_ids}"
            )

    report = Report(number, path, verdict, tuple(findings))
    if verdict in ALLOWED_VERDICTS and verdict != "INCOMPLETE":
        mapped = _verdict_for_counts(report.counts)
        if verdict != mapped:
            problems.append(
                f"{path.name}: verdict {verdict} violates severity mapping "
                f"{mapped} for counts {_format_counts(report.counts)}"
            )
    return report


def _verdict_for_counts(counts: Sequence[int]) -> str:
    critical, major, minor, info = counts
    if critical or major:
        return "ISSUES-FOUND"
    if minor or info:
        return "PASS-WITH-NOTES"
    return "PASS"


def _format_counts(counts: Sequence[int]) -> str:
    return "/".join(str(value) for value in counts)


def _extract_links(cells: Iterable[str]) -> list[str]:
    links: list[str] = []
    for cell in cells:
        for match in MARKDOWN_LINK.finditer(cell):
            target = match.group(1)
            if target.startswith("<") and target.endswith(">"):
                target = target[1:-1]
            links.append(target)
    return links


def _link_problem(
    target: str, *, readme_path: Path, expected_report: Path
) -> str | None:
    parsed = urlsplit(target)
    if parsed.scheme or parsed.netloc or parsed.query:
        return f"uses a non-local or query-bearing target {target!r}"
    raw_path = unquote(parsed.path)
    if not raw_path:
        return f"uses an anchor-only target {target!r}"
    path = Path(raw_path)
    if path.is_absolute():
        return f"uses an absolute target {target!r}"
    try:
        resolved = (readme_path.parent / path).resolve()
        expected = expected_report.resolve()
    except (OSError, RuntimeError) as error:
        return f"cannot be resolved ({error})"
    try:
        resolved.relative_to(readme_path.parent.resolve())
    except ValueError:
        return f"escapes the Verification directory via {target!r}"
    if resolved != expected:
        return (
            f"does not resolve to {expected_report.name}: {target!r} "
            f"resolves to {resolved.name!r}"
        )
    if not resolved.is_file():
        return f"targets missing report {target!r}"
    return None


def _index_header(table: MarkdownTable) -> bool:
    headers = [_header(cell) for cell in table.header]
    compact = [re.sub(r"\s+", "", item) for item in headers]
    return (
        "#" in headers
        and "verdict" in headers
        and "report" in headers
        and "findings(c/m/m/i)" in compact
    )


def _parse_index(
    readme_text: str,
    readme_path: Path,
    reports: dict[int, Report],
    problems: list[str],
) -> dict[int, IndexRow]:
    tables = _find_tables(readme_text.splitlines())
    candidates = [table for table in tables if _index_header(table)]
    if len(candidates) != 1:
        problems.append(
            "README.md: expected exactly one verification index table, "
            f"found {len(candidates)}"
        )
        return {}
    table = candidates[0]
    headers = [_header(cell) for cell in table.header]
    compact = [re.sub(r"\s+", "", item) for item in headers]
    expected_headers = [
        "#",
        "verification",
        "what it guarantees",
        "tier",
        "verdict",
        "findings(c/m/m/i)",
        "report",
    ]
    actual_headers = [
        compact[index] if item.startswith("findings") else item
        for index, item in enumerate(headers)
    ]
    if actual_headers != expected_headers:
        problems.append(
            "README.md: verification index headers must be exactly "
            "'# | Verification | What it guarantees | Tier | Verdict | "
            "Findings (C/M/m/I) | Report'"
        )

    number_column = headers.index("#")
    verdict_column = headers.index("verdict")
    report_column = headers.index("report")
    count_column = compact.index("findings(c/m/m/i)")
    rows: dict[int, IndexRow] = {}
    seen_numbers: Counter[int] = Counter()
    for line_number, cells in table.rows:
        if len(cells) != len(table.header):
            problems.append(
                f"README.md:{line_number}: index row has {len(cells)} cells; "
                f"header has {len(table.header)}"
            )
            continue
        number_text = _plain_cell(cells[number_column]).upper()
        number_match = re.fullmatch(r"V(10|[1-9])", number_text)
        if number_match is None:
            problems.append(
                f"README.md:{line_number}: malformed verification index ID "
                f"{number_text!r}"
            )
            continue
        number = int(number_match.group(1))
        seen_numbers[number] += 1
        if seen_numbers[number] > 1:
            problems.append(
                f"README.md:{line_number}: duplicate verification index row V{number}"
            )
            continue

        verdict = _plain_cell(cells[verdict_column]).upper()
        if verdict not in ALLOWED_VERDICTS:
            problems.append(
                f"README.md:{line_number}: unsupported index verdict "
                f"{verdict!r}"
            )
        count_match = re.fullmatch(
            r"(\d+)\s*/\s*(\d+)\s*/\s*(\d+)\s*/\s*(\d+)",
            _plain_cell(cells[count_column]),
        )
        if count_match is None:
            problems.append(
                f"README.md:{line_number}: malformed C/M/m/I counts "
                f"{cells[count_column]!r}"
            )
            counts = (-1, -1, -1, -1)
        else:
            counts = tuple(int(value) for value in count_match.groups())

        links = _extract_links([cells[report_column]])
        if len(links) != 1:
            problems.append(
                f"README.md:{line_number}: index Report cell must contain "
                f"exactly one Markdown link, found {len(links)}"
            )
            target = ""
        else:
            target = links[0]
            expected_path = Path(EXPECTED_REPORTS[number])
            link_error = _link_problem(
                target,
                readme_path=readme_path,
                expected_report=readme_path.parent / expected_path,
            )
            if link_error is not None:
                problems.append(
                    f"README.md:{line_number}: V{number} report link {link_error}"
                )
        rows[number] = IndexRow(
            number=number,
            verdict=verdict,
            counts=counts,  # type: ignore[arg-type]
            report_target=target,
            line=line_number,
        )

    missing = sorted(set(EXPECTED_REPORTS) - set(rows))
    if missing:
        problems.append(
            "README.md: verification index missing rows "
            + ", ".join(f"V{number}" for number in missing)
        )
    for number, report in sorted(reports.items()):
        row = rows.get(number)
        if row is None:
            continue
        if row.verdict != report.verdict:
            problems.append(
                f"V{number}: README verdict {row.verdict!r} differs from "
                f"report verdict {report.verdict!r}"
            )
        if row.counts != report.counts:
            problems.append(
                f"V{number}: README counts {_format_counts(row.counts)} differ "
                f"from report Findings counts {_format_counts(report.counts)}"
            )
    return rows


def _summary_header(table: MarkdownTable) -> bool:
    headers = [_header(cell) for cell in table.header]
    return (
        any(item in {"finding", "finding id", "id"} for item in headers)
        and "severity" in headers
        and any(item in {"one-line summary", "summary"} for item in headers)
    )


def _parse_summary(
    readme_text: str,
    readme_path: Path,
    reports: dict[int, Report],
    problems: list[str],
) -> dict[str, Finding]:
    candidates = [
        table
        for table in _find_tables(readme_text.splitlines())
        if _summary_header(table)
    ]
    if len(candidates) != 1:
        problems.append(
            "README.md: expected exactly one findings summary table, "
            f"found {len(candidates)}"
        )
        return {}
    table = candidates[0]
    headers = [_header(cell) for cell in table.header]
    id_column = next(
        index
        for index, item in enumerate(headers)
        if item in {"finding", "finding id", "id"}
    )
    severity_column = headers.index("severity")
    rows: dict[str, Finding] = {}
    seen_empty = False
    for line_number, cells in table.rows:
        if len(cells) != len(table.header):
            problems.append(
                f"README.md:{line_number}: findings-summary row has "
                f"{len(cells)} cells; header has {len(table.header)}"
            )
            continue
        finding_id = _plain_cell(cells[id_column])
        severity = _plain_cell(cells[severity_column]).upper()
        id_empty = finding_id.casefold() in EMPTY_FINDING_CELLS
        severity_empty = severity.casefold() in EMPTY_FINDING_CELLS
        if id_empty or severity_empty:
            if not (id_empty and severity_empty):
                problems.append(
                    f"README.md:{line_number}: empty summary sentinel must "
                    "occupy both Finding and Severity cells"
                )
            elif seen_empty:
                problems.append(
                    f"README.md:{line_number}: duplicate empty summary sentinel"
                )
            elif rows:
                problems.append(
                    f"README.md:{line_number}: empty summary sentinel cannot "
                    "coexist with numbered findings"
                )
            seen_empty = True
            continue

        match = FINDING_ID.fullmatch(finding_id)
        if match is None:
            problems.append(
                f"README.md:{line_number}: malformed summary finding ID "
                f"{finding_id!r}"
            )
            continue
        if severity not in SEVERITIES:
            problems.append(
                f"README.md:{line_number}: unsupported summary severity "
                f"{severity!r}"
            )
            continue
        if finding_id in rows:
            problems.append(
                f"README.md:{line_number}: duplicate summary finding "
                f"{finding_id}"
            )
            continue
        if seen_empty:
            problems.append(
                f"README.md:{line_number}: numbered summary finding cannot "
                "coexist with empty sentinel"
            )

        report_number = int(match.group(1))
        expected_path = readme_path.parent / EXPECTED_REPORTS[report_number]
        links = _extract_links(cells)
        matching_links = []
        link_errors = []
        for target in links:
            error = _link_problem(
                target,
                readme_path=readme_path,
                expected_report=expected_path,
            )
            if error is None:
                matching_links.append(target)
            else:
                link_errors.append(error)
        if len(matching_links) != 1:
            detail = (
                "; ".join(link_errors)
                if link_errors
                else "no Markdown report link was present"
            )
            problems.append(
                f"README.md:{line_number}: summary {finding_id} must contain "
                f"exactly one link to {expected_path.name}; {detail}"
            )
        rows[finding_id] = Finding(finding_id, severity, line_number)

    report_findings: dict[str, Finding] = {}
    for report in reports.values():
        for finding in report.findings:
            if finding.finding_id in report_findings:
                problems.append(
                    f"reports: duplicate global finding ID {finding.finding_id}"
                )
            else:
                report_findings[finding.finding_id] = finding

    missing = sorted(set(report_findings) - set(rows))
    extra = sorted(set(rows) - set(report_findings))
    for finding_id in missing:
        problems.append(f"README findings summary missing {finding_id}")
    for finding_id in extra:
        problems.append(f"README findings summary has extra {finding_id}")
    for finding_id in sorted(set(rows) & set(report_findings)):
        if rows[finding_id].severity != report_findings[finding_id].severity:
            problems.append(
                f"{finding_id}: README severity {rows[finding_id].severity} "
                f"differs from report severity "
                f"{report_findings[finding_id].severity}"
            )

    severity_order = [
        SEVERITY_INDEX[finding.severity]
        for finding in rows.values()
        if finding.severity in SEVERITY_INDEX
    ]
    if severity_order != sorted(severity_order):
        problems.append(
            "README.md: findings summary is not sorted by severity "
            "(CRITICAL, MAJOR, MINOR, INFO)"
        )
    return rows


def _scan_placeholders(
    path: Path, text: str, problems: list[str]
) -> None:
    for match in PLACEHOLDER.finditer(text):
        line = text.count("\n", 0, match.start()) + 1
        last_newline = text.rfind("\n", 0, match.start())
        column = match.start() - last_newline
        problems.append(
            f"{path.name}:{line}:{column}: unresolved placeholder "
            f"{match.group(0)!r}"
        )


def _read_markdown(path: Path, problems: list[str]) -> str | None:
    try:
        return path.read_text(encoding="utf-8")
    except (OSError, UnicodeError) as error:
        problems.append(f"{path.name}: cannot read UTF-8 Markdown ({error})")
        return None


def check_consistency(verification_dir: Path | str = VERIFY) -> ConsistencyResult:
    verification_dir = Path(verification_dir).resolve()
    problems: list[str] = []
    reports: dict[int, Report] = {}

    numbered = sorted(verification_dir.glob("[0-9][0-9]_*.md"))
    expected_names = set(EXPECTED_REPORTS.values())
    for path in numbered:
        if path.name not in expected_names:
            problems.append(f"unexpected numbered report {path.name}")

    for number, name in EXPECTED_REPORTS.items():
        path = verification_dir / name
        if not path.is_file():
            problems.append(f"missing final report {name}")
            continue
        text = _read_markdown(path, problems)
        if text is None:
            continue
        _scan_placeholders(path, text, problems)
        report = _parse_report(number, path, text, problems)
        if report is not None:
            reports[number] = report

    readme_path = verification_dir / README_NAME
    if not readme_path.is_file():
        problems.append(f"missing {README_NAME}")
        readme_text = ""
        index_rows: dict[int, IndexRow] = {}
        summary_findings: dict[str, Finding] = {}
    else:
        loaded_readme = _read_markdown(readme_path, problems)
        if loaded_readme is None:
            readme_text = ""
            index_rows = {}
            summary_findings = {}
        else:
            readme_text = loaded_readme
            _scan_placeholders(readme_path, readme_text, problems)
            index_rows = _parse_index(
                readme_text, readme_path, reports, problems
            )
            summary_findings = _parse_summary(
                readme_text, readme_path, reports, problems
            )

    if sorted(reports) != list(EXPECTED_REPORTS):
        problems.append(
            "parsed reports must be exactly V1..V10; found "
            + ", ".join(f"V{number}" for number in sorted(reports))
        )

    return ConsistencyResult(
        verification_dir=verification_dir,
        reports=reports,
        index_rows=index_rows,
        summary_findings=summary_findings,
        problems=tuple(problems),
    )


def render_result(result: ConsistencyResult) -> str:
    report_findings = sum(
        len(report.findings) for report in result.reports.values()
    )
    lines = [
        "VERIFICATION README CONSISTENCY CHECK",
        f"verification_dir={result.verification_dir}",
        f"reports={len(result.reports)}",
        f"index_rows={len(result.index_rows)}",
        f"report_findings={report_findings}",
        f"summary_findings={len(result.summary_findings)}",
        f"problems={len(result.problems)}",
        *(f"PROBLEM {problem}" for problem in result.problems),
        f"result={'PASS' if result.passed else 'FAIL'}",
        "",
    ]
    return "\n".join(lines)


SYNTHETIC_FINDINGS = {
    1: (("V1-F1", "MAJOR"),),
    2: (("V2-F1", "MINOR"),),
    3: (("V3-F1", "INFO"),),
    4: (),
    5: (("V5-F1", "CRITICAL"),),
    6: (),
    7: (),
    8: (),
    9: (),
    10: (),
}


def _write_synthetic_bundle(root: Path) -> None:
    """Create a complete synthetic bundle for tests/calibration."""

    root.mkdir(parents=True, exist_ok=True)
    index_rows: list[str] = []
    summary_rows: list[tuple[int, str]] = []
    for number, name in EXPECTED_REPORTS.items():
        findings = SYNTHETIC_FINDINGS[number]
        counts = tuple(
            sum(severity == expected for _, severity in findings)
            for expected in SEVERITIES
        )
        verdict = _verdict_for_counts(counts)
        finding_rows = [
            f"| {finding_id} | {severity} | Synthetic finding. | evidence |"
            for finding_id, severity in findings
        ]
        if not finding_rows:
            finding_rows = ["| — | — | No findings. | — |"]
        report = "\n".join(
            (
                f"# V{number} — Synthetic report",
                "",
                f"**Verdict: {verdict}**",
                "",
                "## Findings",
                "",
                "| ID | Severity | Finding | Evidence |",
                "|---|---|---|---|",
                *finding_rows,
                "",
                "## Limitations",
                "",
                "Synthetic fixture only.",
                "",
            )
        )
        (root / name).write_text(report, encoding="utf-8")
        index_rows.append(
            f"| V{number} | Check {number} | Synthetic guarantee. | machine | "
            f"{verdict} | {_format_counts(counts)} | [{name}]({name}) |"
        )
        for finding_id, severity in findings:
            summary_rows.append((SEVERITY_INDEX[severity], finding_id))

    rendered_summary: list[str] = []
    for _, finding_id in sorted(summary_rows):
        number = int(FINDING_ID.fullmatch(finding_id).group(1))  # type: ignore[union-attr]
        severity = next(
            severity
            for candidate, severity in SYNTHETIC_FINDINGS[number]
            if candidate == finding_id
        )
        report_name = EXPECTED_REPORTS[number]
        rendered_summary.append(
            f"| {finding_id} | {severity} | "
            f"[Synthetic summary.]({report_name}#{finding_id.casefold()}) |"
        )

    readme = "\n".join(
        (
            "# Synthetic verification bundle",
            "",
            "## Verification index",
            "",
            "| # | Verification | What it guarantees | Tier | Verdict | "
            "Findings (C/M/m/I) | Report |",
            "|---|---|---|---|---|---|---|",
            *index_rows,
            "",
            "## Findings summary",
            "",
            "| Finding | Severity | One-line summary |",
            "|---|---|---|",
            *rendered_summary,
            "",
        )
    )
    (root / README_NAME).write_text(readme, encoding="utf-8")


def _mutate_text(path: Path, transform: Callable[[str], str]) -> None:
    before = path.read_text(encoding="utf-8")
    after = transform(before)
    if before == after:
        raise AssertionError(f"synthetic mutation made no change: {path}")
    path.write_text(after, encoding="utf-8")


def run_self_test(*, verbose: bool = True) -> list[str]:
    """Run isolated positive and negative synthetic calibrations."""

    failures: list[str] = []

    def run_case(
        name: str,
        mutate: Callable[[Path], None] | None,
        expected_problem: str | None,
    ) -> None:
        with tempfile.TemporaryDirectory(
            prefix="hdp-consistency-calibration-"
        ) as temporary:
            root = Path(temporary)
            _write_synthetic_bundle(root)
            if mutate is not None:
                mutate(root)
            result = check_consistency(root)
            if expected_problem is None:
                passed = result.passed
                detail = (
                    "valid bundle accepted"
                    if passed
                    else "; ".join(result.problems)
                )
            else:
                passed = (
                    not result.passed
                    and any(
                        expected_problem in problem
                        for problem in result.problems
                    )
                )
                detail = (
                    f"rejected with {expected_problem!r}"
                    if passed
                    else "; ".join(result.problems)
                )
            if not passed:
                failures.append(f"{name}: {detail}")
            if verbose:
                print(f"{'PASS' if passed else 'FAIL'}\t{name}\t{detail}")

    def duplicate_report_finding(root: Path) -> None:
        path = root / EXPECTED_REPORTS[1]
        needle = "| V1-F1 | MAJOR | Synthetic finding. | evidence |"
        _mutate_text(path, lambda text: text.replace(needle, f"{needle}\n{needle}", 1))

    def gap_report_finding(root: Path) -> None:
        path = root / EXPECTED_REPORTS[1]
        _mutate_text(path, lambda text: text.replace("V1-F1", "V1-F2", 1))

    def wrong_index_count(root: Path) -> None:
        path = root / README_NAME
        _mutate_text(
            path,
            lambda text: re.sub(
                r"(?m)^(\| V1 \|.*\| )0/1/0/0( \| \[)",
                r"\g<1>0/0/0/0\2",
                text,
                count=1,
            ),
        )

    def wrong_verdict(root: Path) -> None:
        path = root / EXPECTED_REPORTS[4]
        _mutate_text(
            path,
            lambda text: text.replace(
                "**Verdict: PASS**", "**Verdict: PASS-WITH-NOTES**", 1
            ),
        )

    def broken_link(root: Path) -> None:
        path = root / README_NAME
        _mutate_text(
            path,
            lambda text: text.replace(
                "(01_build_integrity.md)",
                "(does_not_exist.md)",
                1,
            ),
        )

    def placeholder(root: Path) -> None:
        path = root / EXPECTED_REPORTS[9]
        _mutate_text(path, lambda text: text + "\nTBD\n")

    def to_fill_placeholder(root: Path) -> None:
        path = root / EXPECTED_REPORTS[8]
        _mutate_text(
            path,
            lambda text: text + "\n`V8_FINAL_SECTION_TO_FILL`\n",
        )

    def missing_summary(root: Path) -> None:
        path = root / README_NAME
        _mutate_text(
            path,
            lambda text: re.sub(
                r"(?m)^\| V2-F1 \| MINOR \|.*\|\n", "", text, count=1
            ),
        )

    def wrong_summary_severity(root: Path) -> None:
        path = root / README_NAME
        _mutate_text(
            path,
            lambda text: text.replace(
                "| V2-F1 | MINOR |", "| V2-F1 | MAJOR |", 1
            ),
        )

    def unexpected_report(root: Path) -> None:
        (root / "10_extra.md").write_text(
            "# Unexpected numbered report\n", encoding="utf-8"
        )

    def missing_report(root: Path) -> None:
        (root / EXPECTED_REPORTS[8]).unlink()

    def duplicate_index_row(root: Path) -> None:
        path = root / README_NAME
        text = path.read_text(encoding="utf-8")
        line = next(
            candidate
            for candidate in text.splitlines()
            if candidate.startswith("| V3 |")
        )
        _mutate_text(path, lambda value: value.replace(line, f"{line}\n{line}", 1))

    cases = (
        ("valid bundle", None, None),
        (
            "duplicate report finding ID",
            duplicate_report_finding,
            "duplicate finding ID V1-F1",
        ),
        (
            "missing contiguous report finding ID",
            gap_report_finding,
            "missing finding IDs in contiguous sequence: V1-F1",
        ),
        (
            "README count mismatch",
            wrong_index_count,
            "README counts 0/0/0/0 differ",
        ),
        (
            "report verdict mapping mismatch",
            wrong_verdict,
            "violates severity mapping",
        ),
        (
            "broken report link",
            broken_link,
            "does not resolve to 01_build_integrity.md",
        ),
        (
            "unresolved placeholder",
            placeholder,
            "unresolved placeholder",
        ),
        (
            "unresolved TO_FILL placeholder",
            to_fill_placeholder,
            "unresolved placeholder",
        ),
        (
            "missing README summary finding",
            missing_summary,
            "README findings summary missing V2-F1",
        ),
        (
            "README summary severity mismatch",
            wrong_summary_severity,
            "V2-F1: README severity MAJOR differs",
        ),
        (
            "unexpected tenth report",
            unexpected_report,
            "unexpected numbered report 10_extra.md",
        ),
        (
            "missing final report",
            missing_report,
            "missing final report 08_linter_report.md",
        ),
        (
            "duplicate README index row",
            duplicate_index_row,
            "duplicate verification index row V3",
        ),
    )
    for name, mutate, expected_problem in cases:
        run_case(name, mutate, expected_problem)
    if verbose:
        print(
            f"calibrations={len(cases)} "
            f"passed={len(cases) - len(failures)} "
            f"failed={len(failures)}"
        )
    return failures


def _parse_args(argv: Sequence[str]) -> argparse.Namespace:
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument(
        "--verification-dir",
        type=Path,
        default=VERIFY,
        help="Verification directory (default: directory containing this script)",
    )
    parser.add_argument(
        "--log",
        type=Path,
        default=None,
        help=(
            "output log path; relative paths are resolved below the selected "
            "Verification directory (default: logs/consistency_check.txt)"
        ),
    )
    parser.add_argument(
        "--no-log",
        action="store_true",
        help="print the check only; do not write a log",
    )
    parser.add_argument(
        "--self-test",
        action="store_true",
        help="run synthetic positive/negative calibrations and exit",
    )
    return parser.parse_args(argv)


def main(argv: Sequence[str] | None = None) -> int:
    args = _parse_args(sys.argv[1:] if argv is None else argv)
    if args.self_test:
        return 1 if run_self_test() else 0

    result = check_consistency(args.verification_dir)
    output = render_result(result)
    print(output, end="")
    if not args.no_log:
        log_path = args.log or DEFAULT_LOG
        if not log_path.is_absolute():
            log_path = result.verification_dir / log_path
        log_path.parent.mkdir(parents=True, exist_ok=True)
        log_path.write_text(output, encoding="utf-8")
    return 0 if result.passed else 1


if __name__ == "__main__":
    raise SystemExit(main())
