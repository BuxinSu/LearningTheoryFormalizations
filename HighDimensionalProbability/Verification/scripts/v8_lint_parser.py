#!/usr/bin/env python3
"""Parse and validate the V8 package-scope ``#lint`` evidence log.

The ordinary Batteries ``#lint in Package`` frontend reports a declaration
count even when no linter fires.  When a linter does fire, Lean records the
command as an error and exits nonzero.  This parser treats that nonzero exit as
expected evidence when (and only when) both package summaries are present and
the reported linter messages reconcile with the formatted ``#check`` hits.

The parser never invokes Lean.  The separate runner calls it after preserving
the complete merged subprocess log.
"""

from __future__ import annotations

import argparse
import collections
import json
import re
import sys
from dataclasses import asdict, dataclass, field
from pathlib import Path
from typing import Iterator, Sequence

from file_universe import ROOT


EXPECTED_PACKAGES = (
    "HighDimensionalProbability",
    "MatrixConcentration",
)
MAXIMAL_HARNESS_REL = (
    ".audit_work/verification/V8PackageLintRecertification.lean"
)
FULL_SURFACE_HARNESS_REL = MAXIMAL_HARNESS_REL
FAILED_ORPHAN_MODULES: tuple[str, ...] = ()
REQUIRED_D_FLAGS = (
    "-DmaxHeartbeats=0",
    "-Dtrace.Batteries.Lint=true",
    "-DwarningAsError=false",
)
DEFAULT_MIN_DECLARATIONS = 1000

ANSI_ESCAPE = re.compile(r"\x1b(?:\[[0-?]*[ -/]*[@-~]|\][^\x07]*(?:\x07|\x1b\\))")
SUMMARY = re.compile(
    r"""(?x)
    --\s*Found\s+
    (?P<errors>\d[\d,]*)\s+errors?\s+in\s+
    (?P<declarations>\d[\d,]*)\s+declarations\s+
    \(plus\s+(?P<automatic>\d[\d,]*)\s+automatically\s+generated\s+ones\)\s+
    in\s+(?P<package>HighDimensionalProbability|MatrixConcentration)\s+
    with\s+(?P<linters>\d[\d,]*)\s+linters
    """
)
LINTER_HEADER = re.compile(
    r"^\s*/-\s+The\s+`(?P<linter>[^`]+)`\s+linter\s+reports:\s*$"
)
MODULE_HEADER = re.compile(
    r"^\s*--\s+(?P<module>[A-Za-z_][A-Za-z0-9_'.]*(?:\.[A-Za-z0-9_'.]+)*)\s*$"
)
CHECK_HEADER = re.compile(r"^\s*#check\s+(?P<declaration>.*?)(?:\s+/-|$)")
COMMAND_HEADER = re.compile(r"(?m)^command:\s*(?P<command>.+?)\s*$")
EXIT_HEADER = re.compile(r"(?m)^exit_code:\s*(?P<exit_code>-?\d+)\s*$")
ERROR_HEADER = re.compile(r"(?m)^(?P<header>.*(?:^|:) error:\s+.*)$")


@dataclass(frozen=True)
class LintHit:
    package: str
    linter: str
    module: str
    declaration: str
    log_line: int


@dataclass
class PackageLint:
    package: str
    found_errors: int
    declarations_examined: int
    automatically_generated: int
    linter_count: int
    summary_line: int
    hits: list[LintHit] = field(default_factory=list)

    def linter_hit_counts(self) -> dict[str, int]:
        counts = collections.Counter(hit.linter for hit in self.hits)
        return dict(sorted(counts.items()))

    def module_hit_counts(self) -> dict[str, int]:
        counts = collections.Counter(hit.module for hit in self.hits)
        return dict(sorted(counts.items()))

    def linter_module_hit_counts(self) -> dict[str, dict[str, int]]:
        rows: dict[str, collections.Counter[str]] = {}
        for hit in self.hits:
            rows.setdefault(hit.linter, collections.Counter())[hit.module] += 1
        return {
            linter: dict(sorted(module_counts.items()))
            for linter, module_counts in sorted(rows.items())
        }


@dataclass
class LintReport:
    log_path: str
    command: str
    exit_code: int | None
    packages: list[PackageLint]
    diagnostics: list[str]
    minimum_declarations_per_package: int

    @property
    def total_errors(self) -> int:
        return sum(package.found_errors for package in self.packages)

    @property
    def total_hits(self) -> int:
        return sum(len(package.hits) for package in self.packages)

    @property
    def gate_passed(self) -> bool:
        return not self.diagnostics

    @property
    def surface_profile(self) -> str:
        tokens = self.command.split()
        if FULL_SURFACE_HARNESS_REL in tokens:
            return "full-physical-surface"
        return "unknown"

    @property
    def coverage_complete(self) -> bool:
        return self.surface_profile == "full-physical-surface" and self.gate_passed

    @property
    def coverage_status(self) -> str:
        if self.surface_profile == "full-physical-surface":
            return "COMPLETE" if self.gate_passed else "FULL_SURFACE_GATE_FAILED"
        return "UNKNOWN_SURFACE"

    @property
    def overall_status(self) -> str:
        if not self.gate_passed:
            return "FAIL"
        return "PASS" if self.coverage_complete else "INCOMPLETE"

    @property
    def excluded_modules(self) -> tuple[str, ...]:
        return ()


def _number(text: str) -> int:
    return int(text.replace(",", ""))


def _line_number(text: str, offset: int) -> int:
    return text.count("\n", 0, offset) + 1


def _advance_comment_depth(line: str, depth: int) -> int:
    """Advance Lean nested-block-comment depth across one output line.

    Linter results are formatted as Lean code.  Looking only at top-level
    lines prevents fake ``#check`` or module-looking text inside a diagnostic
    comment from being counted as a separate lint hit.
    """

    index = 0
    while index < len(line):
        if depth == 0 and line.startswith("--", index):
            break
        if line.startswith("/-", index):
            depth += 1
            index += 2
            continue
        if depth > 0 and line.startswith("-/", index):
            depth -= 1
            index += 2
            continue
        index += 1
    return depth


def _lines_with_offsets(text: str) -> Iterator[tuple[int, int, str]]:
    offset = 0
    for line_number, line_with_ending in enumerate(
        text.splitlines(keepends=True), start=1
    ):
        line = line_with_ending.rstrip("\r\n")
        yield line_number, offset, line
        offset += len(line_with_ending)
    if text and not text.endswith(("\n", "\r")):
        return


def _parse_hits(
    segment: str,
    *,
    package: str,
    first_log_line: int,
) -> tuple[list[LintHit], list[str]]:
    hits: list[LintHit] = []
    diagnostics: list[str] = []
    depth = 0
    current_linter = ""
    current_module = ""

    for relative_line, _offset, line in _lines_with_offsets(segment):
        before = depth
        if before == 0:
            linter_match = LINTER_HEADER.match(line)
            module_match = MODULE_HEADER.match(line)
            check_match = CHECK_HEADER.match(line)
            if linter_match is not None:
                current_linter = linter_match.group("linter")
                current_module = ""
            elif module_match is not None:
                current_module = module_match.group("module")
            elif check_match is not None:
                declaration = check_match.group("declaration").strip()
                absolute_line = first_log_line + relative_line - 1
                if not current_linter:
                    diagnostics.append(
                        f"{package}: top-level #check at log line "
                        f"{absolute_line} has no linter header"
                    )
                elif not current_module:
                    diagnostics.append(
                        f"{package}: linter {current_linter} #check at log "
                        f"line {absolute_line} has no module header"
                    )
                elif not declaration:
                    diagnostics.append(
                        f"{package}: empty #check declaration at log line "
                        f"{absolute_line}"
                    )
                else:
                    hits.append(
                        LintHit(
                            package=package,
                            linter=current_linter,
                            module=current_module,
                            declaration=declaration,
                            log_line=absolute_line,
                        )
                    )
        depth = _advance_comment_depth(line, depth)
        if depth < 0:
            diagnostics.append(
                f"{package}: negative Lean comment depth at log line "
                f"{first_log_line + relative_line - 1}"
            )
            depth = 0

    if depth:
        diagnostics.append(
            f"{package}: unterminated formatted Lean comment in lint output"
        )
    return hits, diagnostics


def _package_dict(package: PackageLint) -> dict[str, object]:
    return {
        "package": package.package,
        "found_errors": package.found_errors,
        "declarations_examined": package.declarations_examined,
        "automatically_generated": package.automatically_generated,
        "linter_count": package.linter_count,
        "summary_line": package.summary_line,
        "parsed_hit_count": len(package.hits),
        "linter_hit_counts": package.linter_hit_counts(),
        "module_hit_counts": package.module_hit_counts(),
        "linter_module_hit_counts": package.linter_module_hit_counts(),
        "hits": [asdict(hit) for hit in package.hits],
    }


def parse_lint_log(
    text: str,
    *,
    log_path: str = "<memory>",
    minimum_declarations_per_package: int = DEFAULT_MIN_DECLARATIONS,
    require_run_metadata: bool = True,
) -> LintReport:
    if minimum_declarations_per_package < 0:
        raise ValueError("minimum declaration gate cannot be negative")

    clean = ANSI_ESCAPE.sub("", text).replace("\r\n", "\n")
    diagnostics: list[str] = []
    command_matches = list(COMMAND_HEADER.finditer(clean))
    exit_matches = list(EXIT_HEADER.finditer(clean))
    command = command_matches[-1].group("command") if command_matches else ""
    exit_code = (
        int(exit_matches[-1].group("exit_code")) if exit_matches else None
    )

    if require_run_metadata:
        if len(command_matches) != 1:
            diagnostics.append(
                f"expected exactly one run_logged command header, found "
                f"{len(command_matches)}"
            )
        if len(exit_matches) != 1:
            diagnostics.append(
                f"expected exactly one run_logged exit_code footer, found "
                f"{len(exit_matches)}"
            )
        for flag in REQUIRED_D_FLAGS:
            if flag not in command.split():
                diagnostics.append(f"logged command is missing required flag {flag}")
        harnesses = {
            MAXIMAL_HARNESS_REL,
            FULL_SURFACE_HARNESS_REL,
        }
        if not harnesses.intersection(command.split()):
            diagnostics.append(
                "logged command names neither the maximal-buildable nor the "
                "full-surface V8 harness"
            )

    summary_matches = list(SUMMARY.finditer(clean))
    packages: list[PackageLint] = []
    for index, match in enumerate(summary_matches):
        package_name = match.group("package")
        segment_end = (
            summary_matches[index + 1].start()
            if index + 1 < len(summary_matches)
            else len(clean)
        )
        segment = clean[match.end() : segment_end]
        first_log_line = _line_number(clean, match.end())
        hits, hit_diagnostics = _parse_hits(
            segment,
            package=package_name,
            first_log_line=first_log_line,
        )
        diagnostics.extend(hit_diagnostics)
        packages.append(
            PackageLint(
                package=package_name,
                found_errors=_number(match.group("errors")),
                declarations_examined=_number(match.group("declarations")),
                automatically_generated=_number(match.group("automatic")),
                linter_count=_number(match.group("linters")),
                summary_line=_line_number(clean, match.start()),
                hits=hits,
            )
        )

    observed = collections.Counter(package.package for package in packages)
    for package in EXPECTED_PACKAGES:
        count = observed[package]
        if count != 1:
            diagnostics.append(
                f"expected exactly one {package} summary, found {count}"
            )
    unexpected = sorted(set(observed) - set(EXPECTED_PACKAGES))
    if unexpected:
        diagnostics.append(f"unexpected package summaries: {unexpected}")
    if [package.package for package in packages] != list(EXPECTED_PACKAGES):
        diagnostics.append(
            "package summaries are missing or not in harness command order"
        )

    for package in packages:
        if package.declarations_examined < minimum_declarations_per_package:
            diagnostics.append(
                f"{package.package}: examined only "
                f"{package.declarations_examined} declarations; expected at "
                f"least {minimum_declarations_per_package}"
            )
        if package.found_errors != len(package.hits):
            diagnostics.append(
                f"{package.package}: summary reports "
                f"{package.found_errors} errors but parser found "
                f"{len(package.hits)} top-level #check hits"
            )
        for hit in package.hits:
            if hit.module.split(".", maxsplit=1)[0] != package.package:
                diagnostics.append(
                    f"{package.package}: hit {hit.declaration} was grouped "
                    f"under out-of-package module {hit.module}"
                )

    total_errors = sum(package.found_errors for package in packages)
    if exit_code is not None:
        if total_errors > 0 and exit_code != 1:
            diagnostics.append(
                "lint hits were reported but the logged Lean exit code was "
                f"{exit_code}, not the expected linter-error code 1"
            )
        if total_errors == 0 and exit_code != 0:
            diagnostics.append(
                "no lint hits were reported but the logged Lean exit code was "
                f"{exit_code}"
            )

    non_lint_error_headers: list[str] = []
    for error_match in ERROR_HEADER.finditer(clean):
        header = error_match.group("header")
        if "-- Found" not in header:
            non_lint_error_headers.append(header.strip())
    if non_lint_error_headers:
        diagnostics.append(
            "non-lint Lean error headers were present: "
            + " | ".join(non_lint_error_headers[:10])
        )

    return LintReport(
        log_path=log_path,
        command=command,
        exit_code=exit_code,
        packages=packages,
        diagnostics=diagnostics,
        minimum_declarations_per_package=minimum_declarations_per_package,
    )


def report_dict(report: LintReport) -> dict[str, object]:
    return {
        "profile": "V8-package-lint",
        "overall_status": report.overall_status,
        "surface_profile": report.surface_profile,
        "coverage_status": report.coverage_status,
        "coverage_complete": report.coverage_complete,
        "excluded_failed_orphan_modules": list(report.excluded_modules),
        "full_surface_gate_harness": FULL_SURFACE_HARNESS_REL,
        "log_path": report.log_path,
        "command": report.command,
        "required_d_flags": list(REQUIRED_D_FLAGS),
        "exit_code": report.exit_code,
        "raw_nonzero_expected_from_lint_hits": report.total_errors > 0,
        "minimum_declarations_per_package": (
            report.minimum_declarations_per_package
        ),
        "package_count": len(report.packages),
        "total_reported_errors": report.total_errors,
        "total_parsed_hits": report.total_hits,
        "gate_passed": report.gate_passed,
        "diagnostics": report.diagnostics,
        "packages": [_package_dict(package) for package in report.packages],
    }


def render_json(report: LintReport) -> str:
    return json.dumps(report_dict(report), indent=2, sort_keys=True) + "\n"


def render_text(report: LintReport) -> str:
    lines = [
        "V8 PACKAGE LINT",
        "===============",
        f"log: {report.log_path}",
        f"command: {report.command}",
        f"exit_code: {report.exit_code}",
        f"overall_status: {report.overall_status}",
        f"surface_profile: {report.surface_profile}",
        f"coverage_status: {report.coverage_status}",
        f"coverage_complete: {str(report.coverage_complete).lower()}",
        "excluded_failed_orphan_modules: "
        + (
            ", ".join(report.excluded_modules)
            if report.excluded_modules
            else "(none)"
        ),
        f"minimum_declarations_per_package: "
        f"{report.minimum_declarations_per_package}",
        f"total_reported_errors: {report.total_errors}",
        f"total_parsed_hits: {report.total_hits}",
        f"gate_passed: {str(report.gate_passed).lower()}",
        "",
    ]
    for package in report.packages:
        lines.extend(
            (
                f"[{package.package}]",
                f"declarations_examined: {package.declarations_examined}",
                f"automatically_generated: {package.automatically_generated}",
                f"linter_count: {package.linter_count}",
                f"reported_errors: {package.found_errors}",
                f"parsed_hits: {len(package.hits)}",
                f"linter_hit_counts: {package.linter_hit_counts()}",
                f"module_hit_counts: {package.module_hit_counts()}",
                "",
            )
        )
    lines.append("[diagnostics]")
    lines.extend(report.diagnostics or ["none"])
    return "\n".join(lines) + "\n"


def render_tsv(report: LintReport) -> str:
    lines = ["package\tlinter\tmodule\tdeclaration\tlog_line"]
    for package in report.packages:
        for hit in package.hits:
            values = (
                hit.package,
                hit.linter,
                hit.module,
                hit.declaration,
                str(hit.log_line),
            )
            lines.append(
                "\t".join(
                    value.replace("\\", "\\\\")
                    .replace("\t", "\\t")
                    .replace("\n", "\\n")
                    for value in values
                )
            )
    return "\n".join(lines) + "\n"


def main(argv: Sequence[str] | None = None) -> int:
    parser = argparse.ArgumentParser(
        description="Parse and gate a logged V8 package-scope #lint run"
    )
    parser.add_argument("log", type=Path)
    parser.add_argument(
        "--minimum-declarations-per-package",
        type=int,
        default=DEFAULT_MIN_DECLARATIONS,
    )
    parser.add_argument("--format", choices=("json", "text", "tsv"), default="json")
    parser.add_argument("--output", type=Path)
    parser.add_argument(
        "--allow-missing-run-metadata",
        action="store_true",
        help="permit raw Lean output without run_logged command/exit metadata",
    )
    args = parser.parse_args(argv)

    log = args.log if args.log.is_absolute() else ROOT / args.log
    report = parse_lint_log(
        log.read_text(encoding="utf-8", errors="replace"),
        log_path=log.relative_to(ROOT).as_posix()
        if log.is_relative_to(ROOT)
        else str(log),
        minimum_declarations_per_package=(
            args.minimum_declarations_per_package
        ),
        require_run_metadata=not args.allow_missing_run_metadata,
    )
    if args.format == "json":
        rendered = render_json(report)
    elif args.format == "text":
        rendered = render_text(report)
    else:
        rendered = render_tsv(report)

    if args.output is None:
        sys.stdout.write(rendered)
    else:
        output = (
            args.output
            if args.output.is_absolute()
            else ROOT / args.output
        )
        output.parent.mkdir(parents=True, exist_ok=True)
        output.write_text(rendered, encoding="utf-8")
    return 0 if report.overall_status == "PASS" else 2


if __name__ == "__main__":
    raise SystemExit(main())
