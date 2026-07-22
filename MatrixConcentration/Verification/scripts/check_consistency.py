#!/usr/bin/env python3
"""Cross-check report verdicts/findings against the Verification README."""

from __future__ import annotations

import re
from collections import Counter
from pathlib import Path


SCRIPT = Path(__file__).resolve()
VERIFY = SCRIPT.parent.parent
README = VERIFY / "README.md"
LOG = VERIFY / "logs" / "consistency_check.txt"
SEVERITY_CODE = {"CRITICAL": "C", "MAJOR": "M", "MINOR": "m", "INFO": "I"}


def cells(line: str) -> list[str]:
    return [cell.strip() for cell in line.strip().strip("|").split("|")]


def main() -> int:
    problems: list[str] = []
    if LOG.parent.is_symlink() or not LOG.parent.is_dir():
        print("VERIFICATION README CONSISTENCY CHECK")
        print("PROBLEM verification logs path is not a real directory")
        print("result=FAIL")
        return 1
    reports: dict[int, dict[str, object]] = {}
    for path in sorted(VERIFY.glob("[0-9][0-9]_*.md")):
        number = int(path.name[:2])
        text = path.read_text(encoding="utf-8")
        verdict_match = re.search(r"^\*\*Verdict: ([A-Z-]+)\*\*$", text, re.MULTILINE)
        count_match = re.search(
            r"^\*\*Finding count: C=(\d+) M=(\d+) m=(\d+) I=(\d+)\*\*$",
            text,
            re.MULTILINE,
        )
        if not verdict_match or not count_match:
            problems.append(f"{path.name}: missing verdict or finding-count line")
            continue
        findings = re.findall(
            rf"^### (V{number}-F\d+) — (CRITICAL|MAJOR|MINOR|INFO) — (.+)$",
            text,
            re.MULTILINE,
        )
        measured = Counter(severity for _, severity, _ in findings)
        declared = tuple(map(int, count_match.groups()))
        measured_tuple = tuple(measured[name] for name in SEVERITY_CODE)
        if measured_tuple != declared:
            problems.append(
                f"{path.name}: declared counts {declared}, numbered findings {measured_tuple}"
            )
        if declared[0] or declared[1]:
            mapped_verdict = "ISSUES-FOUND"
        elif declared[2] or declared[3]:
            mapped_verdict = "PASS-WITH-NOTES"
        else:
            mapped_verdict = "PASS"
        if (
            verdict_match.group(1) != "INCOMPLETE"
            and verdict_match.group(1) != mapped_verdict
        ):
            problems.append(
                f"{path.name}: verdict {verdict_match.group(1)} violates "
                f"severity mapping {mapped_verdict}"
            )
        reports[number] = {
            "path": path,
            "verdict": verdict_match.group(1),
            "counts": declared,
            "findings": findings,
        }

    expected_numbers = list(range(1, 11))
    if sorted(reports) != expected_numbers:
        problems.append(f"expected reports 1..10, found {sorted(reports)}")

    readme = README.read_text(encoding="utf-8") if README.is_file() else ""
    index: dict[int, tuple[str, tuple[int, ...], str]] = {}
    for line in readme.splitlines():
        match = re.match(r"^\| V(\d+) \|", line)
        if not match:
            continue
        row = cells(line)
        if len(row) != 7:
            problems.append(f"README index V{match.group(1)} has {len(row)} cells, expected 7")
            continue
        number = int(match.group(1))
        count_match = re.fullmatch(r"(\d+)/(\d+)/(\d+)/(\d+)", row[5])
        if count_match is None:
            problems.append(f"README index V{number} has malformed finding counts {row[5]!r}")
            continue
        index[number] = (row[4], tuple(map(int, count_match.groups())), row[6])

    if sorted(index) != expected_numbers:
        problems.append(f"README index expected V1..V10, found {sorted(index)}")
    for number, report in reports.items():
        if number not in index:
            continue
        verdict, counts, link = index[number]
        if verdict != report["verdict"]:
            problems.append(
                f"V{number}: README verdict {verdict}, report verdict {report['verdict']}"
            )
        if counts != report["counts"]:
            problems.append(
                f"V{number}: README counts {counts}, report counts {report['counts']}"
            )
        if str(report["path"].name) not in link:
            problems.append(f"V{number}: README report link does not name {report['path'].name}")

    summary_findings: dict[str, str] = {}
    for line in readme.splitlines():
        match = re.match(r"^\| (V\d+-F\d+) \| (CRITICAL|MAJOR|MINOR|INFO) \|", line)
        if match:
            if match.group(1) in summary_findings:
                problems.append(f"README duplicate finding {match.group(1)}")
            summary_findings[match.group(1)] = match.group(2)
    report_findings = {
        finding_id: severity
        for report in reports.values()
        for finding_id, severity, _ in report["findings"]
    }
    if summary_findings != report_findings:
        for finding_id in sorted(report_findings.keys() - summary_findings.keys()):
            problems.append(f"README findings summary missing {finding_id}")
        for finding_id in sorted(summary_findings.keys() - report_findings.keys()):
            problems.append(f"README findings summary has extra {finding_id}")
        for finding_id in sorted(summary_findings.keys() & report_findings.keys()):
            if summary_findings[finding_id] != report_findings[finding_id]:
                problems.append(
                    f"{finding_id}: README severity {summary_findings[finding_id]}, "
                    f"report severity {report_findings[finding_id]}"
                )

    lines = [
        "VERIFICATION README CONSISTENCY CHECK",
        f"reports={len(reports)}",
        f"index_rows={len(index)}",
        f"report_findings={len(report_findings)}",
        f"summary_findings={len(summary_findings)}",
        f"problems={len(problems)}",
        *(f"PROBLEM {problem}" for problem in problems),
        f"result={'PASS' if not problems else 'FAIL'}",
        "",
    ]
    LOG.write_text("\n".join(lines), encoding="utf-8")
    print("\n".join(lines), end="")
    return 0 if not problems else 1


if __name__ == "__main__":
    raise SystemExit(main())
