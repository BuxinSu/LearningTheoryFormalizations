#!/usr/bin/env python3
"""Resolve and axiom-check every endpoint published in the main README.

This is a source-bound reimplementation of the pre-existing project helper.
It writes a fresh harness only under ``.audit_work/verification`` and fresh
evidence only under ``Verification/logs``.  Project-local results are also
joined to V4's exhaustive ``Lean.collectAxioms`` output; external Mathlib
endpoints remain covered by the independent ``#print axioms`` harness.
"""

from __future__ import annotations

import argparse
import collections
import csv
import datetime as dt
import io
import re
import shlex
import subprocess
import sys
import tempfile
from pathlib import Path


ROOT = Path(__file__).resolve().parents[3]
README = ROOT / "HighDimensionalProbability" / "README.md"
HARNESS = (
    ROOT / ".audit_work" / "verification" / "V9READMEProvedAxiomsRecertification.lean"
)
LOGS = ROOT / "HighDimensionalProbability" / "Verification" / "logs"
RAW_LOG = LOGS / "recert_v9_readme_axioms_build.log"
RESULTS = LOGS / "recert_v9_readme_axioms.tsv"
SUMMARY = LOGS / "recert_v9_readme_axioms_summary.txt"
DEFAULT_V4 = LOGS / "recert_axiom_audit.tsv"

ALLOWED = frozenset({"propext", "Classical.choice", "Quot.sound"})
EXPECTED_ROWS = 611
EXPECTED_UNIQUE_NAMES = 540
PROJECT_PREFIXES = (
    "HDP.",
    "HighDimensionalProbability.",
    "MatrixConcentration.",
)


def expected_lean_command() -> list[str]:
    """Return the one exact argv accepted for the preserved endpoint run."""

    return [
        str(Path.home() / ".elan" / "bin" / "lake"),
        "env",
        "lean",
        "-DmaxSynthPendingDepth=3",
        "-DrelaxedAutoImplicit=false",
        str(HARNESS),
    ]


def split_markdown_row(line: str) -> list[str]:
    """Split one pipe-table row while ignoring pipes inside inline code."""
    cells: list[str] = []
    current: list[str] = []
    in_code = False
    for character in line.strip().strip("|"):
        if character == "`":
            in_code = not in_code
            current.append(character)
        elif character == "|" and not in_code:
            cells.append("".join(current).strip())
            current = []
        else:
            current.append(character)
    cells.append("".join(current).strip())
    return cells


def table_rows(readme: Path = README) -> list[list[str]]:
    rows: list[list[str]] = []
    in_correspondence = False
    for line in readme.read_text(encoding="utf-8").splitlines():
        if line == "## Book → Lean correspondence":
            in_correspondence = True
            continue
        if not in_correspondence:
            continue
        if not line.startswith("| ") or line.startswith("|---"):
            continue
        cells = split_markdown_row(line)
        if len(cells) == 4 and cells[0] != "Book source":
            rows.append(cells)
    if not rows:
        raise RuntimeError("no Book → Lean correspondence rows found")
    return rows


def proved_names(rows: list[list[str]]) -> list[str]:
    names: set[str] = set()
    for _, _, name_cell, _ in rows:
        found = re.findall(r"`([^`]+)`", name_cell)
        if not found:
            raise RuntimeError(
                f"published correspondence row has no Lean endpoint: {name_cell!r}"
            )
        inherited_namespace: str | None = None
        if found[0].startswith("HDP.") and "." in found[0]:
            inherited_namespace = found[0].rsplit(".", 1)[0]
        for name in found:
            if inherited_namespace is not None and "." not in name:
                names.add(f"{inherited_namespace}.{name}")
            else:
                names.add(name)
    return sorted(names)


def render_harness(names: list[str]) -> str:
    lines = [
        "import HighDimensionalProbability",
        "",
        "/-!",
        "# V9 README endpoint axiom harness",
        "",
        "Generated deterministically by",
        "`Verification/scripts/verify_readme_axioms.py`.",
        "-/",
        "",
        "set_option autoImplicit false",
        "set_option maxHeartbeats 0",
        "",
    ]
    lines.extend(f"#print axioms {name}" for name in names)
    lines.append("")
    return "\n".join(lines)


def write_harness(names: list[str], path: Path = HARNESS) -> None:
    path.parent.mkdir(parents=True, exist_ok=True)
    path.write_text(render_harness(names), encoding="utf-8")


def parse_axioms(
    output: str, names: list[str]
) -> tuple[dict[str, frozenset[str]], list[str], list[str]]:
    found: dict[str, frozenset[str]] = {}
    duplicates: list[str] = []
    lines = output.splitlines()
    header = re.compile(
        r"^'(.+)' (?:depends on axioms:|does not depend on any axioms)"
    )
    for index, line in enumerate(lines):
        match = header.match(line.strip())
        if match is None:
            continue
        name = match.group(1)
        if name not in names:
            continue
        if name in found:
            duplicates.append(name)
            continue
        if "does not depend" in line:
            found[name] = frozenset()
            continue
        payload = line.split("axioms:", 1)[1].strip()
        cursor = index + 1
        while "]" not in payload and cursor < len(lines):
            payload += " " + lines[cursor].strip()
            cursor += 1
        bracket = re.search(r"\[(.*)\]", payload)
        if bracket is not None:
            found[name] = frozenset(
                item.strip()
                for item in bracket.group(1).split(",")
                if item.strip()
            )
    missing = sorted(set(names) - set(found))
    return found, missing, sorted(set(duplicates))


def read_v4(path: Path) -> dict[str, frozenset[str]]:
    with path.open(encoding="utf-8", newline="") as handle:
        reader = csv.DictReader(handle, delimiter="\t")
        required = {"name", "axioms"}
        if not required <= set(reader.fieldnames or []):
            raise ValueError(f"{path}: V4 TSV lacks {sorted(required)}")
        result: dict[str, frozenset[str]] = {}
        for row in reader:
            name = row["name"]
            if name in result:
                raise ValueError(f"{path}: duplicate V4 declaration {name}")
            result[name] = frozenset(
                filter(None, row["axioms"].split(";"))
            )
    if not result:
        raise ValueError(f"{path}: V4 audit is empty")
    return result


def write_raw_log(
    command: list[str],
    *,
    stdout: str,
    returncode: int,
    started: dt.datetime,
    finished: dt.datetime,
) -> None:
    RAW_LOG.parent.mkdir(parents=True, exist_ok=True)
    RAW_LOG.write_text(
        "\n".join(
            [
                f"started: {started.isoformat()}",
                f"cwd: {ROOT}",
                f"command: {shlex.join(command)}",
                "",
                stdout.rstrip("\n"),
                "",
                f"finished: {finished.isoformat()}",
                f"elapsed_seconds: {(finished - started).total_seconds():.3f}",
                f"exit_code: {returncode}",
                "",
            ]
        ),
        encoding="utf-8",
    )


def artifact_texts(
    *,
    rows: list[list[str]],
    names: list[str],
    found: dict[str, frozenset[str]],
    missing: list[str],
    duplicates: list[str],
    v4_path: Path,
) -> tuple[str, str, list[str]]:
    errors: list[str] = []
    if len(rows) != EXPECTED_ROWS:
        errors.append(
            f"README row count: expected {EXPECTED_ROWS}, observed {len(rows)}"
        )
    if len(names) != EXPECTED_UNIQUE_NAMES:
        errors.append(
            "README unique endpoint count: expected "
            f"{EXPECTED_UNIQUE_NAMES}, observed {len(names)}"
        )
    if missing:
        errors.append(f"{len(missing)} #print-axioms results are missing")
    if duplicates:
        errors.append(f"{len(duplicates)} #print-axioms results are duplicated")
    unexpected = {
        name: axioms - ALLOWED
        for name, axioms in found.items()
        if axioms - ALLOWED
    }
    if unexpected:
        errors.append(
            f"{len(unexpected)} README endpoints use nonstandard axioms"
        )

    v4 = read_v4(v4_path)
    project_names = {
        name for name in names if name.startswith(PROJECT_PREFIXES)
    }
    project_missing_v4 = project_names - set(v4)
    if project_missing_v4:
        errors.append(
            f"{len(project_missing_v4)} project README endpoints are absent from V4"
        )
    v4_mismatches = {
        name: (found[name], v4[name])
        for name in project_names & set(found) & set(v4)
        if found[name] != v4[name]
    }
    if v4_mismatches:
        errors.append(
            f"{len(v4_mismatches)} README/V4 axiom sets differ"
        )

    result_buffer = io.StringIO(newline="")
    writer = csv.writer(result_buffer, delimiter="\t", lineterminator="\n")
    writer.writerow(
        [
            "name",
            "classification",
            "axioms",
            "allowed",
            "present_in_v4",
            "v4_axioms",
            "v4_match",
        ]
    )
    for name in names:
        axioms = found.get(name, frozenset())
        is_project = name in project_names
        v4_axioms = v4.get(name)
        writer.writerow(
            [
                name,
                "PROJECT" if is_project else "EXTERNAL_DEPENDENCY",
                ";".join(sorted(axioms)),
                str(not (axioms - ALLOWED)).lower()
                if name in found
                else "false",
                str(name in v4).lower(),
                ";".join(sorted(v4_axioms or ())),
                (
                    str(axioms == v4_axioms).lower()
                    if is_project and name in found and v4_axioms is not None
                    else ""
                ),
            ]
        )

    distribution = collections.Counter(
        tuple(sorted(axioms)) for axioms in found.values()
    )
    lines = [
        "V9 README-PUBLISHED ENDPOINT AXIOM CHECK",
        "========================================",
        f"verdict: {'PASS' if not errors else 'FAIL'}",
        f"readme_correspondence_rows: {len(rows)}",
        f"unique_published_endpoints: {len(names)}",
        f"parsed_axiom_results: {len(found)}",
        f"project_endpoints: {len(project_names)}",
        f"external_dependency_endpoints: {len(names) - len(project_names)}",
        f"project_endpoints_missing_from_v4: {len(project_missing_v4)}",
        f"readme_v4_axiom_set_mismatches: {len(v4_mismatches)}",
        f"nonstandard_axiom_endpoints: {len(unexpected)}",
        "",
        "[axiom_set_distribution]",
    ]
    for axioms, count in sorted(
        distribution.items(), key=lambda item: (len(item[0]), item[0])
    ):
        lines.append(
            f"{count}\t{';'.join(axioms) if axioms else '(none)'}"
        )
    lines.extend(("", "[errors]", *(errors or ["(none)"])))
    lines.extend(("", "[missing]", *(missing or ["(none)"])))
    lines.extend(
        (
            "",
            "[project_endpoints_missing_from_v4]",
            *(sorted(project_missing_v4) or ["(none)"]),
        )
    )
    lines.extend(
        (
            "",
            "[nonstandard_axiom_endpoints]",
            *(
                f"{name}\t{';'.join(sorted(axioms))}"
                for name, axioms in sorted(unexpected.items())
            ),
        )
    )
    if not unexpected:
        lines.append("(none)")
    return result_buffer.getvalue(), "\n".join(lines) + "\n", errors


def analyze(
    *,
    rows: list[list[str]],
    names: list[str],
    found: dict[str, frozenset[str]],
    missing: list[str],
    duplicates: list[str],
    v4_path: Path,
) -> int:
    results_text, summary_text, errors = artifact_texts(
        rows=rows,
        names=names,
        found=found,
        missing=missing,
        duplicates=duplicates,
        v4_path=v4_path,
    )
    RESULTS.write_text(results_text, encoding="utf-8")
    SUMMARY.write_text(summary_text, encoding="utf-8")
    lines = summary_text.splitlines()
    print("\n".join(lines[:12]))
    return 1 if errors else 0


def _validated_raw_log(path: Path) -> str:
    if path.is_symlink() or not path.is_file() or path.stat().st_size == 0:
        raise ValueError(f"raw axiom log is missing, empty, or a symlink: {path}")
    text = path.read_text(encoding="utf-8", errors="replace")
    commands = re.findall(r"(?m)^command:\s*(.+?)\s*$", text)
    exits = re.findall(r"(?m)^exit_code:\s*(-?\d+)\s*$", text)
    cwd_rows = re.findall(r"(?m)^cwd:\s*(.+?)\s*$", text)
    finished = re.findall(r"(?m)^finished:\s*(\S.*?)\s*$", text)
    if len(commands) != 1 or len(exits) != 1 or len(cwd_rows) != 1 or len(finished) != 1:
        raise ValueError(
            "raw axiom log metadata is not unique: "
            f"commands={len(commands)}, exits={len(exits)}, "
            f"cwd={len(cwd_rows)}, finished={len(finished)}"
        )
    if exits != ["0"]:
        raise ValueError(f"raw axiom log exit is not zero: {exits[0]}")
    if Path(cwd_rows[0]).resolve() != ROOT:
        raise ValueError(f"raw axiom log cwd differs from project root: {cwd_rows[0]}")
    try:
        command = shlex.split(commands[0])
    except ValueError as error:
        raise ValueError(f"cannot parse raw axiom command: {error}") from error
    expected = expected_lean_command()
    if command != expected:
        raise ValueError(
            "raw axiom command is not the expected Lake/Lean harness command: "
            f"expected={expected!r}, observed={command!r}"
        )
    return text


def validate_preserved_artifacts(
    *,
    raw_log: Path = RAW_LOG,
    results_path: Path = RESULTS,
    summary_path: Path = SUMMARY,
    v4_path: Path = DEFAULT_V4,
) -> tuple[int, int]:
    """Fail unless all preserved V9 endpoint artifacts equal a fresh rebuild."""

    rows = table_rows()
    names = proved_names(rows)
    if (
        HARNESS.is_symlink()
        or not HARNESS.is_file()
        or HARNESS.read_text(encoding="utf-8") != render_harness(names)
    ):
        raise ValueError("preserved V9 axiom harness differs from current README")
    raw = _validated_raw_log(raw_log)
    found, missing, duplicates = parse_axioms(raw, names)
    expected_results, expected_summary, errors = artifact_texts(
        rows=rows,
        names=names,
        found=found,
        missing=missing,
        duplicates=duplicates,
        v4_path=v4_path,
    )
    if errors:
        raise ValueError("preserved V9 endpoint audit is not PASS: " + "; ".join(errors))
    expected = {
        results_path: expected_results,
        summary_path: expected_summary,
    }

    mismatches = _content_mismatches(expected)
    if mismatches:
        raise ValueError(
            "preserved V9 endpoint artifacts differ from raw/current evidence: "
            + ", ".join(mismatches)
        )
    return len(rows), len(names)


def _content_mismatches(expected: dict[Path, str]) -> list[str]:
    return [
        str(path)
        for path, content in expected.items()
        if path.is_symlink()
        or not path.is_file()
        or path.read_text(encoding="utf-8") != content
    ]


def check_only(
    v4_path: Path,
    *,
    raw_log: Path,
    results_path: Path,
    summary_path: Path,
) -> int:
    try:
        rows, names = validate_preserved_artifacts(
            raw_log=raw_log,
            results_path=results_path,
            summary_path=summary_path,
            v4_path=v4_path,
        )
    except (OSError, RuntimeError, ValueError) as error:
        print(f"FAIL: {error}", file=sys.stderr)
        return 1
    print(
        "PASS: V9 README endpoint artifacts are current "
        f"({rows} correspondence rows; {names} unique endpoints)"
    )
    return 0


def run(v4_path: Path, *, generate_only: bool) -> int:
    rows = table_rows()
    names = proved_names(rows)
    write_harness(names)
    if generate_only:
        print(
            f"generated {HARNESS.relative_to(ROOT)} for "
            f"{len(names)} unique endpoints / {len(rows)} rows"
        )
        return 0

    command = expected_lean_command()
    started = dt.datetime.now(dt.timezone.utc).astimezone()
    completed = subprocess.run(
        command,
        cwd=ROOT,
        text=True,
        stdout=subprocess.PIPE,
        stderr=subprocess.STDOUT,
        check=False,
    )
    finished = dt.datetime.now(dt.timezone.utc).astimezone()
    write_raw_log(
        command,
        stdout=completed.stdout,
        returncode=completed.returncode,
        started=started,
        finished=finished,
    )
    if completed.returncode != 0:
        print(
            f"Lean endpoint harness failed; see {RAW_LOG.relative_to(ROOT)}",
            file=sys.stderr,
        )
        return completed.returncode
    found, missing, duplicates = parse_axioms(completed.stdout, names)
    return analyze(
        rows=rows,
        names=names,
        found=found,
        missing=missing,
        duplicates=duplicates,
        v4_path=v4_path,
    )


def self_test() -> int:
    sample = "\n".join(
        [
            "'A' depends on axioms: [propext, Classical.choice, Quot.sound]",
            "'B' does not depend on any axioms",
            "'C' depends on axioms: [propext,",
            " Classical.choice]",
        ]
    )
    found, missing, duplicates = parse_axioms(sample, ["A", "B", "C"])
    assert not missing and not duplicates
    assert found["A"] == ALLOWED
    assert found["B"] == frozenset()
    assert found["C"] == frozenset({"propext", "Classical.choice"})
    assert split_markdown_row("| a | `x | y` | c |") == [
        "a",
        "`x | y`",
        "c",
    ]
    with tempfile.TemporaryDirectory(prefix="v9-readme-axioms-selftest-") as temporary:
        artifact = Path(temporary) / "artifact.tsv"
        artifact.write_text("expected\n", encoding="utf-8")
        assert not _content_mismatches({artifact: "expected\n"})
        artifact.write_text("tampered\n", encoding="utf-8")
        assert _content_mismatches({artifact: "expected\n"}) == [str(artifact)]
        raw_log = Path(temporary) / "raw.log"

        def write_test_log(command: list[str]) -> None:
            raw_log.write_text(
                "\n".join(
                    (
                        "started: 2026-01-01T00:00:00+00:00",
                        f"cwd: {ROOT}",
                        f"command: {shlex.join(command)}",
                        "",
                        "finished: 2026-01-01T00:00:01+00:00",
                        "elapsed_seconds: 1.000",
                        "exit_code: 0",
                        "",
                    )
                ),
                encoding="utf-8",
            )

        expected = expected_lean_command()
        write_test_log(expected)
        assert _validated_raw_log(raw_log) == raw_log.read_text(encoding="utf-8")
        wrong_path = [str(Path(temporary) / "lake"), *expected[1:]]
        wrong_order = [expected[0], expected[2], expected[1], *expected[3:]]
        extra_argument = [*expected, "--unexpected"]
        for rejected in (wrong_path, wrong_order, extra_argument):
            write_test_log(rejected)
            try:
                _validated_raw_log(raw_log)
            except ValueError:
                pass
            else:
                raise AssertionError(f"accepted noncanonical command: {rejected!r}")
    print("PASS: V9 README axiom-parser/artifact self-test")
    return 0


def _resolve(path: Path) -> Path:
    return path if path.is_absolute() else ROOT / path


def main() -> int:
    parser = argparse.ArgumentParser()
    parser.add_argument("--self-test", action="store_true")
    parser.add_argument("--generate-only", action="store_true")
    parser.add_argument(
        "--check-only",
        action="store_true",
        help=(
            "do not invoke Lean; reconstruct and validate the preserved "
            "harness, TSV, and summary from the raw log/current README/V4"
        ),
    )
    parser.add_argument(
        "--v4-audit",
        type=Path,
        default=DEFAULT_V4.relative_to(ROOT),
    )
    parser.add_argument("--raw-log", type=Path, default=RAW_LOG.relative_to(ROOT))
    parser.add_argument("--results", type=Path, default=RESULTS.relative_to(ROOT))
    parser.add_argument("--summary", type=Path, default=SUMMARY.relative_to(ROOT))
    args = parser.parse_args()
    if args.self_test:
        return self_test()
    if args.check_only:
        return check_only(
            _resolve(args.v4_audit),
            raw_log=_resolve(args.raw_log),
            results_path=_resolve(args.results),
            summary_path=_resolve(args.summary),
        )
    return run(
        _resolve(args.v4_audit),
        generate_only=args.generate_only,
    )


if __name__ == "__main__":
    raise SystemExit(main())
