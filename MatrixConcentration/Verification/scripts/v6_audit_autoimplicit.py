#!/usr/bin/env python3
"""Audit endpoint type/Prop binders against explicit source declarations.

Lean's environment records the final telescope but not whether an implicit
binder came from a section ``variable`` command or auto-bound identifier.  This
script joins the environment telescope dump to source locations and tracks
active namespace/section variable commands.  Every single-codepoint Type/Prop
variable binder on a correspondence theorem endpoint receives explicit source
evidence or is emitted as a suspect auto-bound binder.
"""

from __future__ import annotations

import csv
import json
import re
from dataclasses import dataclass
from pathlib import Path

from lean_source_scan import ROOT, LOGS, relative, tsv_safe
from v6_scan_vacuity import Statement, extract, mask_noncode


VERIFY = Path(__file__).resolve().parent.parent
ROWS = LOGS / "v6_correspondence_rows.tsv"
BINDERS = LOGS / "v6_endpoint_binders.tsv"
CALIBRATION_PLANT = ROOT / ".audit_work" / "V6AutoImplicitPlant.lean"
CALIBRATION_BINDERS = LOGS / "v6_autoimplicit_calibration_binders.tsv"


@dataclass(frozen=True)
class ExplicitEvidence:
    line: int
    command: str


def read_tsv(path: Path) -> list[dict[str, str]]:
    with path.open(encoding="utf-8", newline="") as handle:
        return list(csv.DictReader(handle, delimiter="\t"))


def sort_names(command: str) -> set[str]:
    """Extract explicitly bound names whose declared domain is Type*/Type/Prop."""

    names: set[str] = set()
    binder = re.compile(
        r"[\{\(]\s*([^:{}()\[\]]+?)\s*:\s*"
        r"(?:Type(?:\s*(?:\*|[0-9A-Za-z_+.-]+))?|Prop)\s*[\}\)]"
    )
    for match in binder.finditer(command):
        for name in re.split(r"\s+", match.group(1).strip()):
            name = name.lstrip("⦃").rstrip("⦄,")
            if name and re.fullmatch(r"[\w\u0370-\u03ff\u1f00-\u1fff]+", name):
                names.add(name)
    return names


def source_declarations(
    path: Path,
) -> dict[tuple[int, str], tuple[Statement, dict[str, ExplicitEvidence]]]:
    """Map source statements to the active explicit Type/Prop variable evidence."""

    text = path.read_text(encoding="utf-8")
    masked = mask_noncode(text)
    statements = {(statement.line, statement.name): statement for statement in extract(path)}
    scopes: list[dict[str, ExplicitEvidence]] = [{}]
    result: dict[
        tuple[int, str], tuple[Statement, dict[str, ExplicitEvidence]]
    ] = {}
    for line_number, (raw_line, code_line) in enumerate(
        zip(text.splitlines(), masked.splitlines()), start=1
    ):
        stripped = code_line.strip()
        if re.match(r"^(?:namespace|section)(?:\s|$)", stripped):
            scopes.append({})
        elif re.match(r"^end(?:\s|$)", stripped):
            if len(scopes) > 1:
                scopes.pop()
        elif re.match(r"^variables?(?:\s|$)", stripped):
            for name in sort_names(stripped):
                scopes[-1][name] = ExplicitEvidence(line_number, raw_line.strip())

        for (statement_line, name), statement in statements.items():
            if statement_line != line_number:
                continue
            active: dict[str, ExplicitEvidence] = {}
            for scope in scopes:
                active.update(scope)
            for explicit_name in sort_names(statement.header):
                active[explicit_name] = ExplicitEvidence(
                    statement.line, "declaration binder: " + statement.header.strip()
                )
            result[(statement_line, name)] = (statement, active)
    missing = sorted(set(statements) - set(result))
    if missing:
        raise RuntimeError(f"failed to assign scope evidence in {path}: {missing[:5]}")
    return result


def main() -> int:
    calibration_errors: list[str] = []
    calibration_output: list[dict[str, str]] = []
    if not CALIBRATION_PLANT.is_file():
        calibration_errors.append(
            f"missing calibration plant: {CALIBRATION_PLANT}"
        )
    if not CALIBRATION_BINDERS.is_file():
        calibration_errors.append(
            f"missing calibration environment dump: {CALIBRATION_BINDERS}"
        )
    if not calibration_errors:
        calibration_sources = source_declarations(CALIBRATION_PLANT)
        sources_by_name = {
            name: value for (_line, name), value in calibration_sources.items()
        }
        for binder in read_tsv(CALIBRATION_BINDERS):
            if (
                binder["domain_class"] not in {"Type-variable", "Prop-variable"}
                or len(binder["binder_name"]) != 1
                or binder["binder_info"] not in {"implicit", "strictImplicit"}
            ):
                continue
            source = sources_by_name.get(binder["readme_name"])
            if source is None:
                status = "SOURCE-MISSING"
                evidence = "calibration declaration absent from source index"
            else:
                _statement, active = source
                explicit = active.get(binder["binder_name"])
                if explicit is None:
                    status = "SUSPECT-AUTO-BOUND"
                    evidence = (
                        "no active variable command or declaration binder found"
                    )
                else:
                    status = "EXPLICIT"
                    evidence = f"line {explicit.line}: {explicit.command}"
            calibration_output.append(
                {
                    **binder,
                    "audit_status": status,
                    "explicit_evidence": evidence,
                }
            )
        expected_calibration = {
            (
                "verificationAutoBoundTypePlant",
                "α",
                "Type-variable",
            ),
            (
                "verificationAutoBoundPropPlant",
                "P",
                "Prop-variable",
            ),
        }
        actual_calibration = {
            (
                row["readme_name"],
                row["binder_name"],
                row["domain_class"],
            )
            for row in calibration_output
            if row["audit_status"] == "SUSPECT-AUTO-BOUND"
        }
        if actual_calibration != expected_calibration:
            calibration_errors.append(
                "auto-bound calibration mismatch: "
                f"actual={sorted(actual_calibration)!r}, "
                f"expected={sorted(expected_calibration)!r}"
            )
    calibration_fields = (
        list(calibration_output[0])
        if calibration_output
        else [
            "readme_name",
            "resolved_name",
            "binder_index",
            "binder_name",
            "binder_info",
            "domain_class",
            "binder_type",
            "audit_status",
            "explicit_evidence",
        ]
    )
    with (LOGS / "v6_autoimplicit_calibration.tsv").open(
        "w", encoding="utf-8", newline=""
    ) as handle:
        writer = csv.DictWriter(
            handle, delimiter="\t", fieldnames=calibration_fields
        )
        writer.writeheader()
        writer.writerows(calibration_output)

    correspondence = read_tsv(ROWS)
    binder_rows = read_tsv(BINDERS)
    row_by_global = {row["global_row"]: row for row in correspondence}
    paths = {
        ROOT / "MatrixConcentration" / row["final_module"] for row in correspondence
    }
    source_index: dict[tuple[Path, str], tuple[Statement, dict[str, ExplicitEvidence]]] = {}
    duplicate_source_names: list[str] = []
    for path in sorted(paths):
        if not path.is_file():
            raise RuntimeError(f"correspondence module does not exist: {path}")
        for (_line, name), value in source_declarations(path).items():
            key = (path, name)
            if key in source_index:
                duplicate_source_names.append(f"{relative(path)}:{name}")
            source_index[key] = value

    candidates = [
        row
        for row in binder_rows
        if row["domain_class"] in {"Type-variable", "Prop-variable"}
        and len(row["binder_name"]) == 1
        and row["binder_info"] in {"implicit", "strictImplicit"}
        and row_by_global[row["global_row"]]["role"].endswith(
            ("thm", "lem")
        )
    ]
    # The environment kind, not the README role spelling, determines theorem
    # coverage.  Role filtering above merely excludes definition rows; assert
    # against the endpoint dump below so a future role change cannot narrow it.
    endpoint_rows = read_tsv(LOGS / "v6_endpoint_telescopes.tsv")
    theorem_globals = {
        row["global_row"] for row in endpoint_rows if row["kind"] == "theorem"
    }
    candidates = [
        row
        for row in binder_rows
        if row["global_row"] in theorem_globals
        and row["domain_class"] in {"Type-variable", "Prop-variable"}
        and len(row["binder_name"]) == 1
        and row["binder_info"] in {"implicit", "strictImplicit"}
    ]

    output_rows: list[dict[str, str]] = []
    missing_source: list[str] = []
    suspects: list[dict[str, str]] = []
    for binder in candidates:
        correspondence_row = row_by_global[binder["global_row"]]
        path = ROOT / "MatrixConcentration" / correspondence_row["final_module"]
        key = (path, binder["readme_name"])
        source = source_index.get(key)
        if source is None:
            missing_source.append(
                f"{binder['global_row']}:{relative(path)}:{binder['readme_name']}"
            )
            status = "SOURCE-MISSING"
            evidence = ""
            source_line = ""
            statement = ""
        else:
            source_statement, active = source
            explicit = active.get(binder["binder_name"])
            if explicit is None:
                status = "SUSPECT-AUTO-BOUND"
                evidence = "no active variable command or declaration binder found"
            else:
                status = "EXPLICIT"
                evidence = f"line {explicit.line}: {explicit.command}"
            source_line = str(source_statement.line)
            statement = source_statement.header
        result = {
            **binder,
            "source_path": relative(path),
            "source_line": source_line,
            "audit_status": status,
            "explicit_evidence": tsv_safe(evidence),
            "source_statement": tsv_safe(statement),
        }
        output_rows.append(result)
        if status == "SUSPECT-AUTO-BOUND":
            suspects.append(result)

    fields = list(output_rows[0]) if output_rows else [
        "global_row",
        "chapter",
        "chapter_row",
        "readme_name",
        "resolved_name",
        "binder_index",
        "binder_name",
        "binder_info",
        "domain_class",
        "binder_type",
        "source_path",
        "source_line",
        "audit_status",
        "explicit_evidence",
        "source_statement",
    ]
    with (LOGS / "v6_autoimplicit_audit.tsv").open(
        "w", encoding="utf-8", newline=""
    ) as handle:
        writer = csv.DictWriter(handle, delimiter="\t", fieldnames=fields)
        writer.writeheader()
        writer.writerows(output_rows)
    with (LOGS / "v6_autoimplicit_suspects.tsv").open(
        "w", encoding="utf-8", newline=""
    ) as handle:
        writer = csv.DictWriter(handle, delimiter="\t", fieldnames=fields)
        writer.writeheader()
        writer.writerows(suspects)

    summary = {
        "endpoint_theorems": len(theorem_globals),
        "all_endpoint_binders": len(binder_rows),
        "single_letter_implicit_type_or_prop_binders": len(candidates),
        "explicitly_accounted": sum(
            row["audit_status"] == "EXPLICIT" for row in output_rows
        ),
        "suspect_auto_bound": len(suspects),
        "missing_source": missing_source,
        "duplicate_source_names": duplicate_source_names,
        "rule": (
            "candidate = one-codepoint implicit/strictImplicit binder whose domain "
            "is a Lean Sort (Type/Prop) on an environment-confirmed theorem endpoint; "
            "explicit = same name appears in an active namespace/section variable "
            "command or in the declaration's own binder telescope"
        ),
        "calibration_expected_hits": 2,
        "calibration_actual_hits": sum(
            row["audit_status"] == "SUSPECT-AUTO-BOUND"
            for row in calibration_output
        ),
        "calibration_errors": calibration_errors,
    }
    (LOGS / "v6_autoimplicit_summary.json").write_text(
        json.dumps(summary, indent=2, sort_keys=True) + "\n", encoding="utf-8"
    )
    problems = (
        len(suspects)
        + len(missing_source)
        + len(duplicate_source_names)
        + len(calibration_errors)
        + (0 if len(theorem_globals) == 401 else 1)
    )
    lines = [
        "V6 AUTO-BOUND SINGLE-LETTER TYPE/PROP VARIABLE AUDIT",
        f"CALIBRATION_EXPECTED_HITS 2",
        f"CALIBRATION_ACTUAL_HITS {summary['calibration_actual_hits']}",
        f"CALIBRATION_ERRORS {len(calibration_errors)}",
        *[f"CALIBRATION_ERROR {item}" for item in calibration_errors],
        f"THEOREM_ENDPOINTS {len(theorem_globals)}",
        f"ALL_ENDPOINT_BINDER_ROWS {len(binder_rows)}",
        f"CANDIDATE_BINDERS {len(candidates)}",
        f"EXPLICITLY_ACCOUNTED {summary['explicitly_accounted']}",
        f"SUSPECT_AUTO_BOUND {len(suspects)}",
        f"MISSING_SOURCE {len(missing_source)}",
        *[f"MISSING_SOURCE_ROW {item}" for item in missing_source],
        f"DUPLICATE_SOURCE_NAMES {len(duplicate_source_names)}",
        *[f"DUPLICATE_SOURCE_NAME {item}" for item in duplicate_source_names],
        f"VERDICT {'PASS' if problems == 0 else 'FAIL'}",
    ]
    (LOGS / "v6_autoimplicit_run.log").write_text(
        "\n".join(lines) + "\n", encoding="utf-8"
    )
    print("\n".join(lines))
    return 0 if problems == 0 else 1


if __name__ == "__main__":
    raise SystemExit(main())
