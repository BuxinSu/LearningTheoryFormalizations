#!/usr/bin/env python3
"""Prepare and fail-closed validate the V7 manual definition review.

``definition_sanity.py`` produces two machine inventories:

* ``definition_load_bearing.tsv`` is the complete load-bearing row set; and
* ``definition_nontriviality_candidates.tsv`` contains theorem-statement
  references that may help a reviewer.

A candidate is discovery metadata, never evidence by itself.  This script
partitions the complete load-bearing set into module-coherent review shards.
Each row begins as ``UNREVIEWED``.  A row can be promoted only to:

* ``VERIFIED_CITATION`` after a reviewer records a semantic reason and the
  cited theorem is present in the candidate inventory and passes V4;
* ``VERIFIED_WITNESS`` after a named witness has independently bound physical
  source, exact declaration anchor, completed build and collector logs, direct
  theorem-type dependency, and allowed-axiom evidence; or
* ``UNVERIFIED_SANITY`` with a numbered finding and blocker.

No Lean or Lake command is run here.  ``prepare``, ``validate``, and
``--self-test`` are static operations.
"""

from __future__ import annotations

import argparse
import collections
import csv
import datetime as dt
import hashlib
import re
import shlex
import sys
import tempfile
from dataclasses import dataclass
from pathlib import Path
from typing import Iterable, Sequence

from definition_sanity import (
    CANDIDATE_COLUMNS,
    LOAD_BEARING_COLUMNS,
    LOGS,
    NONTRIVIALITY_CANDIDATES,
    LOAD_BEARING,
    ROOT,
    module_to_source_path,
)
from lean_source_scanner import mask_lean_noncode


REVIEW_DIR = ROOT / "HighDimensionalProbability" / "Verification" / "review"
DEFAULT_MANIFEST = REVIEW_DIR / "v7_definition_review_manifest.tsv"
DEFAULT_SUMMARY = REVIEW_DIR / "v7_definition_review_framework_summary.txt"
DEFAULT_V4 = LOGS / "axiom_audit.tsv"
DEFAULT_WITNESS_EVIDENCE = LOGS / "definition_witness_evidence.tsv"

CONTRACT_VERSION = "2"
CANDIDATE_DISPOSITION = "DISCOVERY_ONLY_NOT_EVIDENCE"
STATUSES = {
    "UNREVIEWED",
    "VERIFIED_CITATION",
    "VERIFIED_WITNESS",
    "UNVERIFIED_SANITY",
}
FINAL_STATUSES = STATUSES - {"UNREVIEWED"}
ALLOWED_AXIOMS = {"propext", "Classical.choice", "Quot.sound"}
FINDING_SEVERITIES = {"CRITICAL", "MAJOR", "MINOR"}
FINDING_ID = re.compile(r"^V7-F[1-9][0-9]*$")
DATE = re.compile(r"^\d{4}-\d{2}-\d{2}$")
FORBIDDEN_WITNESS_TEXT = re.compile(
    r"declaration uses ['`]?sorry|\bsorryAx\b|\badmit\b|"
    r"(?<![A-Za-z]): error(?::|\b)",
    re.IGNORECASE,
)
FORBIDDEN_WITNESS_CODE = re.compile(r"\b(?:sorry|admit|sorryAx)\b")
RUN_LOG_EXIT = re.compile(r"(?m)^exit_code:\s*(-?\d+)\s*$")
RUN_LOG_COMMAND = re.compile(r"(?m)^command:\s*(.+?)\s*$")
RUN_LOG_STARTED = re.compile(r"(?m)^started:\s*(\S.*?)\s*$")
RUN_LOG_CWD = re.compile(r"(?m)^cwd:\s*(.+?)\s*$")
RUN_LOG_FINISHED = re.compile(r"(?m)^finished:\s*(\S.*?)\s*$")
RUN_LOG_ELAPSED = re.compile(r"(?m)^elapsed_seconds:\s*([0-9.]+)\s*$")
COLLECTOR_PREFIX = "V7_WITNESS_COLLECTOR"
WITNESS_SOURCE_PREFIX = (
    "HighDimensionalProbability",
    "Verification",
    "scripts",
    "witnesses",
)
COLLECTOR_SOURCE_PREFIX = (".audit_work", "verification")

MANIFEST_COLUMNS = (
    "contract_version",
    "review_id",
    "shard",
    "module",
    "source_path",
    "name",
    "kind",
    "candidate_count",
)
REVIEW_COLUMNS = (
    "contract_version",
    "review_id",
    "shard",
    "module",
    "source_path",
    "name",
    "kind",
    "is_private",
    "private_user_name",
    "is_internal",
    "load_bearing_reason",
    "tier_b_endpoint_count",
    "tier_b_type_endpoint_count",
    "tier_b_value_endpoint_count",
    "candidate_count",
    "candidate_theorems",
    "candidate_details",
    "candidate_disposition",
    "review_status",
    "evidence_method",
    "evidence_name",
    "evidence_location",
    "evidence_axioms",
    "semantic_nontriviality_claim",
    "nondegenerate_model",
    "constant_or_zero_collapse_check",
    "junk_or_empty_boundary_check",
    "measure_or_typeclass_check",
    "review_rationale",
    "witness_evidence_key",
    "finding_id",
    "finding_severity",
    "blocker",
    "reviewer",
    "review_date",
)
WITNESS_EVIDENCE_COLUMNS = (
    "definition",
    "witness",
    "witness_module",
    "source_path",
    "build_log",
    "collector_source",
    "collector_log",
)
MACHINE_METADATA_COLUMNS = REVIEW_COLUMNS[:18]
REVIEW_JUDGMENT_COLUMNS = REVIEW_COLUMNS[18:]
REQUIRED_SEMANTIC_FIELDS = (
    "semantic_nontriviality_claim",
    "nondegenerate_model",
    "constant_or_zero_collapse_check",
    "junk_or_empty_boundary_check",
    "measure_or_typeclass_check",
    "review_rationale",
    "reviewer",
    "review_date",
)


@dataclass(frozen=True)
class Validation:
    rows: tuple[dict[str, str], ...]
    problems: tuple[str, ...]
    final_ready: bool

    @property
    def passed(self) -> bool:
        return not self.problems


def _read_tsv(
    path: Path, expected_columns: Sequence[str]
) -> list[dict[str, str]]:
    with path.open(encoding="utf-8", newline="") as handle:
        reader = csv.DictReader(handle, delimiter="\t")
        observed = tuple(reader.fieldnames or ())
        if observed != tuple(expected_columns):
            raise ValueError(
                f"{path}: columns {observed!r}; expected "
                f"{tuple(expected_columns)!r}"
            )
        rows = list(reader)
    return rows


def _write_tsv(
    path: Path, columns: Sequence[str], rows: Iterable[dict[str, str]]
) -> None:
    path.parent.mkdir(parents=True, exist_ok=True)
    with path.open("w", encoding="utf-8", newline="") as handle:
        writer = csv.DictWriter(
            handle,
            fieldnames=columns,
            delimiter="\t",
            lineterminator="\n",
            extrasaction="raise",
        )
        writer.writeheader()
        writer.writerows(rows)


def _parse_nonnegative(
    value: str, *, context: str, problems: list[str]
) -> int:
    try:
        parsed = int(value)
    except ValueError:
        problems.append(f"{context}: expected integer, got {value!r}")
        return -1
    if parsed < 0:
        problems.append(f"{context}: expected nonnegative integer, got {parsed}")
    return parsed


def _review_id(name: str) -> str:
    digest = hashlib.sha256(name.encode("utf-8")).hexdigest()[:16]
    return f"v7-def-{digest}"


def _validate_inputs(
    load_rows: Sequence[dict[str, str]],
    candidate_rows: Sequence[dict[str, str]],
) -> tuple[dict[str, dict[str, str]], dict[str, list[dict[str, str]]], list[str]]:
    problems: list[str] = []
    load_by_name: dict[str, dict[str, str]] = {}
    for index, row in enumerate(load_rows, start=2):
        context = f"load-bearing row {index}"
        name = row["name"]
        if not name:
            problems.append(f"{context}: empty name")
            continue
        if name in load_by_name:
            problems.append(f"{context}: duplicate definition {name}")
            continue
        if row["kind"] not in {"definition", "structure", "class"}:
            problems.append(f"{context}: unsupported kind {row['kind']!r}")
        for field in ("is_private", "is_internal"):
            if row[field] not in {"true", "false"}:
                problems.append(
                    f"{context}: {field} must be true/false, got {row[field]!r}"
                )
        try:
            expected_source = module_to_source_path(row["module"])
        except ValueError as error:
            problems.append(f"{context}: {error}")
            expected_source = ""
        if row["source_path"] != expected_source:
            problems.append(
                f"{context}: source_path {row['source_path']!r} does not match "
                f"module path {expected_source!r}"
            )
        any_count = _parse_nonnegative(
            row["tier_b_endpoint_count"],
            context=f"{context} tier_b_endpoint_count",
            problems=problems,
        )
        type_count = _parse_nonnegative(
            row["tier_b_type_endpoint_count"],
            context=f"{context} tier_b_type_endpoint_count",
            problems=problems,
        )
        value_count = _parse_nonnegative(
            row["tier_b_value_endpoint_count"],
            context=f"{context} tier_b_value_endpoint_count",
            problems=problems,
        )
        if max(type_count, value_count) > any_count:
            problems.append(
                f"{context}: type/value endpoint count exceeds union count"
            )
        if any_count > type_count + value_count:
            problems.append(
                f"{context}: union endpoint count exceeds type+value counts"
            )
        reasons = set(row["reason"].split(";")) if row["reason"] else set()
        allowed_reasons = {
            "all_prelude_defs_structures_classes",
            "directly_referenced_by_ge3_tier_b_endpoints",
        }
        if not reasons or reasons - allowed_reasons:
            problems.append(
                f"{context}: invalid load-bearing reason set {sorted(reasons)!r}"
            )
        if (
            "directly_referenced_by_ge3_tier_b_endpoints" in reasons
            and any_count < 3
        ):
            problems.append(
                f"{context}: >=3 threshold reason has count {any_count}"
            )
        load_by_name[name] = row

    if not load_by_name:
        problems.append("load-bearing input is empty")

    candidates: dict[str, list[dict[str, str]]] = collections.defaultdict(list)
    seen_candidates: set[tuple[str, str]] = set()
    for index, row in enumerate(candidate_rows, start=2):
        context = f"candidate row {index}"
        target = row["target"]
        definition = load_by_name.get(target)
        if definition is None:
            problems.append(
                f"{context}: target {target!r} is not load-bearing"
            )
            continue
        if (
            row["target_module"] != definition["module"]
            or row["target_kind"] != definition["kind"]
        ):
            problems.append(f"{context}: target metadata disagrees with load row")
        if row["origin"] != "type":
            problems.append(
                f"{context}: only theorem-statement/type candidates are allowed"
            )
        try:
            module_to_source_path(row["candidate_module"])
        except ValueError as error:
            problems.append(f"{context}: {error}")
        theorem = row["candidate_theorem"]
        key = (target, theorem)
        if not theorem:
            problems.append(f"{context}: empty candidate theorem")
        elif key in seen_candidates:
            problems.append(
                f"{context}: duplicate candidate {theorem} for {target}"
            )
        seen_candidates.add(key)
        score = _parse_nonnegative(
            row["score"], context=f"{context} score", problems=problems
        )
        if score <= 0:
            problems.append(f"{context}: candidate score must be positive")
        candidates[target].append(row)
    for rows in candidates.values():
        rows.sort(
            key=lambda row: (
                -int(row["score"]),
                row["candidate_theorem"],
            )
        )
    return load_by_name, dict(candidates), problems


def _assign_shards(
    load_by_name: dict[str, dict[str, str]], shard_count: int
) -> dict[str, int]:
    if shard_count <= 0:
        raise ValueError("shard_count must be positive")
    by_module: dict[str, list[str]] = collections.defaultdict(list)
    for name, row in load_by_name.items():
        by_module[row["module"]].append(name)
    loads = [0] * shard_count
    assignment: dict[str, int] = {}
    for module, names in sorted(
        by_module.items(), key=lambda item: (-len(item[1]), item[0])
    ):
        shard_index = min(range(shard_count), key=lambda index: (loads[index], index))
        shard = shard_index + 1
        for name in names:
            assignment[name] = shard
        loads[shard_index] += len(names)
    return assignment


def _candidate_cells(
    rows: Sequence[dict[str, str]],
) -> tuple[str, str]:
    names = ";".join(row["candidate_theorem"] for row in rows)
    details = ";".join(
        "|".join(
            (
                row["candidate_theorem"],
                f"module={row['candidate_module']}",
                f"score={row['score']}",
                row["reasons"],
            )
        )
        for row in rows
    )
    return names, details


def _scaffold_rows(
    load_by_name: dict[str, dict[str, str]],
    candidates: dict[str, list[dict[str, str]]],
    shard_count: int,
) -> list[dict[str, str]]:
    assignment = _assign_shards(load_by_name, shard_count)
    rows: list[dict[str, str]] = []
    for name in sorted(load_by_name):
        source = load_by_name[name]
        candidate_rows = candidates.get(name, [])
        candidate_names, candidate_details = _candidate_cells(candidate_rows)
        row = {
            "contract_version": CONTRACT_VERSION,
            "review_id": _review_id(name),
            "shard": str(assignment[name]),
            "module": source["module"],
            "source_path": source["source_path"],
            "name": name,
            "kind": source["kind"],
            "is_private": source["is_private"],
            "private_user_name": source["private_user_name"],
            "is_internal": source["is_internal"],
            "load_bearing_reason": source["reason"],
            "tier_b_endpoint_count": source["tier_b_endpoint_count"],
            "tier_b_type_endpoint_count": source[
                "tier_b_type_endpoint_count"
            ],
            "tier_b_value_endpoint_count": source[
                "tier_b_value_endpoint_count"
            ],
            "candidate_count": str(len(candidate_rows)),
            "candidate_theorems": candidate_names,
            "candidate_details": candidate_details,
            "candidate_disposition": CANDIDATE_DISPOSITION,
            "review_status": "UNREVIEWED",
            **{column: "" for column in REVIEW_JUDGMENT_COLUMNS[1:]},
        }
        rows.append(row)
    return rows


def _manifest_row(row: dict[str, str]) -> dict[str, str]:
    return {column: row[column] for column in MANIFEST_COLUMNS}


def prepare(
    *,
    load_path: Path,
    candidates_path: Path,
    output_dir: Path,
    shard_count: int,
    force: bool,
) -> list[Path]:
    load_rows = _read_tsv(load_path, LOAD_BEARING_COLUMNS)
    candidate_rows = _read_tsv(candidates_path, CANDIDATE_COLUMNS)
    load_by_name, candidates, problems = _validate_inputs(
        load_rows, candidate_rows
    )
    if problems:
        raise ValueError("invalid V7 inputs:\n" + "\n".join(problems))
    rows = _scaffold_rows(load_by_name, candidates, shard_count)
    manifest = output_dir / DEFAULT_MANIFEST.name
    summary = output_dir / DEFAULT_SUMMARY.name
    shard_paths = [
        output_dir / f"v7_definition_review_shard_{shard:02d}.tsv"
        for shard in range(1, shard_count + 1)
    ]
    targets = [manifest, summary, *shard_paths]
    existing = [path for path in targets if path.exists()]
    if existing and not force:
        raise FileExistsError(
            "refusing to overwrite review artifacts: "
            + ", ".join(str(path) for path in existing)
        )

    output_dir.mkdir(parents=True, exist_ok=True)
    _write_tsv(
        manifest,
        MANIFEST_COLUMNS,
        (_manifest_row(row) for row in rows),
    )
    for shard, path in enumerate(shard_paths, start=1):
        _write_tsv(
            path,
            REVIEW_COLUMNS,
            (row for row in rows if row["shard"] == str(shard)),
        )
    counts = collections.Counter(int(row["shard"]) for row in rows)
    candidate_count = sum(int(row["candidate_count"]) for row in rows)
    summary.write_text(
        "\n".join(
            (
                "V7 LOAD-BEARING DEFINITION MANUAL REVIEW FRAMEWORK",
                "===================================================",
                f"contract_version: {CONTRACT_VERSION}",
                f"load_bearing_rows: {len(rows)}",
                f"shard_count: {shard_count}",
                f"candidate_rows_discovery_only: {candidate_count}",
                "candidate_rows_promoted_to_evidence: 0",
                f"review_status_UNREVIEWED: {len(rows)}",
                "final_ready: false",
                (
                    "contract: citation candidates are not evidence; every row "
                    "requires reviewer promotion, compiled witness evidence, or "
                    "an UNVERIFIED_SANITY finding"
                ),
                "",
                "[shard_rows]",
                *(
                    f"shard_{shard:02d}: {counts[shard]}"
                    for shard in range(1, shard_count + 1)
                ),
                "",
            )
        ),
        encoding="utf-8",
    )
    return targets


def _axiom_set(text: str) -> set[str]:
    values = {value.strip() for value in re.split(r"[;,]", text)}
    empty_markers = {"", "(none)", "none", "∅", "[]"}
    return {value for value in values if value.lower() not in empty_markers}


def _read_v4(path: Path, problems: list[str]) -> dict[str, dict[str, str]]:
    if not path.is_file():
        problems.append(f"missing V4 evidence {path}")
        return {}
    with path.open(encoding="utf-8", newline="") as handle:
        reader = csv.DictReader(handle, delimiter="\t")
        required = {"module", "name", "kind", "axioms"}
        if not required <= set(reader.fieldnames or ()):
            problems.append(f"{path}: V4 evidence lacks {sorted(required)}")
            return {}
        rows = list(reader)
    result: dict[str, dict[str, str]] = {}
    for row in rows:
        name = row["name"]
        if name in result:
            problems.append(f"{path}: duplicate V4 declaration {name}")
        result[name] = row
    return result


def _read_witness_evidence(
    path: Path, problems: list[str]
) -> dict[tuple[str, str], dict[str, str]]:
    if not path.is_file():
        problems.append(f"missing witness evidence {path}")
        return {}
    try:
        rows = _read_tsv(path, WITNESS_EVIDENCE_COLUMNS)
    except ValueError as error:
        problems.append(str(error))
        return {}
    result: dict[tuple[str, str], dict[str, str]] = {}
    for row in rows:
        key = (row["definition"], row["witness"])
        if key in result:
            problems.append(f"{path}: duplicate witness evidence {key}")
        result[key] = row
    return result


def _safe_project_path(
    relative: str, *, context: str, problems: list[str]
) -> Path | None:
    relative_path = Path(relative)
    if (
        not relative
        or relative_path.is_absolute()
        or ".." in relative_path.parts
    ):
        problems.append(
            f"{context}: project evidence path must be a safe relative path: "
            f"{relative!r}"
        )
        return None
    root = ROOT.resolve()
    # Build below the canonical root so macOS's /var -> /private/var alias
    # does not make a TemporaryDirectory fixture look like a symlink escape.
    unresolved = root / relative_path
    path = unresolved.resolve()
    try:
        path.relative_to(root)
    except ValueError:
        problems.append(
            f"{context}: project evidence path escapes the project root: "
            f"{relative!r}"
        )
        return None
    if unresolved.is_symlink() or path != unresolved.absolute():
        problems.append(
            f"{context}: project evidence path resolves through a symlink: "
            f"{relative!r}"
        )
        return None
    return path


def _path_has_prefix(relative: str, prefix: tuple[str, ...]) -> bool:
    parts = Path(relative).parts
    return parts[: len(prefix)] == prefix


def _lean_module_from_source(relative: str) -> str:
    path = Path(relative)
    if path.suffix != ".lean":
        raise ValueError(f"witness source is not a .lean file: {relative!r}")
    return ".".join(path.with_suffix("").parts)


def _check_exact_location(
    location: str,
    *,
    expected_relative: str,
    expected_line: int,
    context: str,
    problems: list[str],
) -> None:
    relative, separator, line_text = location.rpartition(":")
    if not separator:
        problems.append(f"{context}: evidence_location must be path:line")
        return
    if relative != expected_relative:
        problems.append(
            f"{context}: evidence_location path {relative!r} does not match "
            f"the measured evidence module path {expected_relative!r}"
        )
    try:
        line = int(line_text)
    except ValueError:
        problems.append(f"{context}: invalid location line {line_text!r}")
        return
    path = _safe_project_path(
        relative, context=context, problems=problems
    )
    if path is None:
        return
    if not path.is_file():
        problems.append(f"{context}: evidence source does not exist: {relative}")
        return
    line_count = len(path.read_text(encoding="utf-8").splitlines())
    if not 1 <= line <= line_count:
        problems.append(f"{context}: evidence location is out of range")
    elif line != expected_line:
        problems.append(
            f"{context}: evidence location does not anchor the named "
            f"declaration: line {line}, expected {expected_line}"
        )


def _resolve_theorem_anchor(
    *,
    module: str,
    name: str,
    private_user_name: str,
    source_relative: str,
    context: str,
    problems: list[str],
) -> int | None:
    """Resolve a theorem to one exact lexer-checked physical source line."""

    source_path = _safe_project_path(
        source_relative, context=context, problems=problems
    )
    if source_path is None:
        return None
    if not source_path.is_file():
        problems.append(
            f"{context}: evidence source does not exist: {source_relative}"
        )
        return None
    # Import lazily: the packet renderer imports this module for the shared
    # review contract, while source resolution is needed only during final
    # validation after module initialization is complete.
    try:
        from v7_review_packet import (
            SOURCE_THEOREM_KEYWORDS,
            _resolve_source,
            _scan_source,
        )

        resolved = _resolve_source(
            row={
                "module": module,
                "name": name,
                "kind": "theorem",
                "private_user_name": private_user_name,
            },
            declarations=_scan_source(ROOT, source_relative),
            expected_keywords=SOURCE_THEOREM_KEYWORDS,
        )
    except (ImportError, OSError, UnicodeError, ValueError, RuntimeError) as error:
        problems.append(
            f"{context}: cannot resolve exact theorem source anchor: {error}"
        )
        return None
    if resolved.declaration.keyword not in SOURCE_THEOREM_KEYWORDS:
        problems.append(
            f"{context}: named witness/citation is not a theorem or lemma "
            f"at its source anchor"
        )
        return None
    return resolved.declaration.line


def _lean_code(
    path: Path, *, context: str, problems: list[str]
) -> str | None:
    try:
        text = path.read_text(encoding="utf-8")
    except (OSError, UnicodeError) as error:
        problems.append(f"{context}: cannot read Lean source: {error}")
        return None
    code, diagnostics = mask_lean_noncode(text)
    if diagnostics:
        problems.append(
            f"{context}: Lean lexical diagnostics: "
            + ", ".join(kind for kind, _offset in diagnostics)
        )
        return None
    return code


def _completed_lean_log(
    relative: str,
    *,
    expected_source: Path,
    context: str,
    problems: list[str],
) -> str | None:
    path = _safe_project_path(relative, context=context, problems=problems)
    if path is None:
        return None
    if not path.is_file():
        problems.append(f"{context}: completed-run log is missing: {relative}")
        return None
    text = path.read_text(encoding="utf-8", errors="replace")
    metadata_patterns = {
        "started": RUN_LOG_STARTED,
        "cwd": RUN_LOG_CWD,
        "finished": RUN_LOG_FINISHED,
        "elapsed_seconds": RUN_LOG_ELAPSED,
    }
    metadata = {
        label: pattern.findall(text)
        for label, pattern in metadata_patterns.items()
    }
    for label, values in metadata.items():
        if len(values) != 1:
            problems.append(
                f"{context}: expected exactly one run_logged {label} field"
            )
    if len(metadata["cwd"]) == 1:
        try:
            logged_cwd = Path(metadata["cwd"][0]).resolve()
        except OSError as error:
            problems.append(f"{context}: invalid logged cwd: {error}")
        else:
            if logged_cwd != ROOT.resolve():
                problems.append(
                    f"{context}: logged cwd {logged_cwd} does not match "
                    f"project root {ROOT.resolve()}"
                )
    exits = RUN_LOG_EXIT.findall(text)
    if exits != ["0"]:
        problems.append(
            f"{context}: expected exactly one terminal exit_code 0, got {exits}"
        )
    nonempty_lines = [line.strip() for line in text.splitlines() if line.strip()]
    if not nonempty_lines or nonempty_lines[-1] != "exit_code: 0":
        problems.append(
            f"{context}: exit_code 0 is not the terminal nonempty log line"
        )
    commands = RUN_LOG_COMMAND.findall(text)
    if len(commands) != 1:
        problems.append(
            f"{context}: expected exactly one run_logged command header"
        )
    else:
        try:
            tokens = shlex.split(commands[0])
        except ValueError as error:
            problems.append(f"{context}: malformed command header: {error}")
        else:
            if (
                len(tokens) < 4
                or Path(tokens[0]).name != "lake"
                or tokens[1:3] != ["env", "lean"]
            ):
                problems.append(
                    f"{context}: command is not an exact `lake env lean` run"
                )
            else:
                source_argument = Path(tokens[-1])
                command_source = (
                    source_argument.resolve()
                    if source_argument.is_absolute()
                    else (ROOT / source_argument).resolve()
                )
                if command_source != expected_source.resolve():
                    problems.append(
                        f"{context}: command source {command_source} does not "
                        f"match {expected_source.resolve()}"
                    )
    if FORBIDDEN_WITNESS_TEXT.search(text):
        problems.append(
            f"{context}: log contains sorry/admit/sorryAx or an error diagnostic"
        )
    return text


def _collector_row(
    text: str, *, expected_name: str, context: str, problems: list[str]
) -> dict[str, str] | None:
    rows = [
        line.split("\t")
        for line in text.splitlines()
        if line.startswith(COLLECTOR_PREFIX + "\t")
    ]
    malformed = [parts for parts in rows if len(parts) != 7]
    if malformed:
        problems.append(
            f"{context}: collector contains {len(malformed)} malformed "
            f"{COLLECTOR_PREFIX} row(s)"
        )
        return None
    names = [parts[2] for parts in rows]
    duplicate_names = sorted(
        name
        for name, count in collections.Counter(names).items()
        if count > 1
    )
    if duplicate_names:
        problems.append(
            f"{context}: collector contains duplicate witness rows "
            f"{duplicate_names}"
        )
        return None
    matches = [parts for parts in rows if parts[2] == expected_name]
    if len(matches) != 1:
        problems.append(
            f"{context}: expected exactly one {COLLECTOR_PREFIX} row for "
            f"{expected_name!r}, found {len(matches)}"
        )
        return None
    parts = matches[0]
    (
        _prefix,
        module,
        name,
        kind,
        private_user_name,
        axioms,
        type_dependencies,
    ) = parts
    return {
        "module": module,
        "name": name,
        "kind": kind,
        "private_user_name": private_user_name,
        "axioms": axioms,
        "type_dependencies": type_dependencies,
    }


def _require_fields(
    row: dict[str, str],
    fields: Sequence[str],
    *,
    context: str,
    problems: list[str],
) -> None:
    missing = [field for field in fields if not row[field].strip()]
    if missing:
        problems.append(
            f"{context}: required review fields are empty: {', '.join(missing)}"
        )


def _forbid_fields(
    row: dict[str, str],
    fields: Sequence[str],
    *,
    context: str,
    problems: list[str],
) -> None:
    stale = [field for field in fields if row[field].strip()]
    if stale:
        problems.append(
            f"{context}: status-inapplicable fields must be empty: "
            + ", ".join(stale)
        )


def _validate_citation(
    row: dict[str, str],
    *,
    candidate_rows: Sequence[dict[str, str]],
    v4: dict[str, dict[str, str]],
    context: str,
    problems: list[str],
) -> None:
    if row["evidence_method"] != "citation":
        problems.append(f"{context}: VERIFIED_CITATION needs evidence_method=citation")
    candidates = {
        name for name in row["candidate_theorems"].split(";") if name
    }
    evidence = row["evidence_name"]
    if evidence not in candidates:
        problems.append(
            f"{context}: citation {evidence!r} was not explicitly promoted "
            "from this row's theorem-statement candidates"
        )
    _require_fields(
        row,
        (*REQUIRED_SEMANTIC_FIELDS, "evidence_name", "evidence_location", "evidence_axioms"),
        context=context,
        problems=problems,
    )
    _forbid_fields(
        row,
        ("witness_evidence_key", "finding_id", "finding_severity", "blocker"),
        context=context,
        problems=problems,
    )
    evidence_row = v4.get(evidence)
    if evidence_row is None:
        problems.append(f"{context}: citation is absent from V4: {evidence}")
        return
    matching_candidates = [
        candidate
        for candidate in candidate_rows
        if candidate["candidate_theorem"] == evidence
    ]
    if (
        len(matching_candidates) == 1
        and evidence_row["module"]
        != matching_candidates[0]["candidate_module"]
    ):
        problems.append(
            f"{context}: V4 citation module {evidence_row['module']!r} differs "
            "from the candidate inventory module "
            f"{matching_candidates[0]['candidate_module']!r}"
        )
    if evidence_row["kind"] != "theorem":
        problems.append(
            f"{context}: citation is not a theorem in V4: {evidence}"
        )
    if len(matching_candidates) == 1 and row["evidence_location"]:
        try:
            expected_source = module_to_source_path(
                matching_candidates[0]["candidate_module"]
            )
        except ValueError as error:
            problems.append(f"{context}: {error}")
        else:
            anchor = _resolve_theorem_anchor(
                module=matching_candidates[0]["candidate_module"],
                name=evidence,
                private_user_name=evidence_row.get("private_user_name", ""),
                source_relative=expected_source,
                context=context,
                problems=problems,
            )
            if anchor is not None:
                _check_exact_location(
                    row["evidence_location"],
                    expected_relative=expected_source,
                    expected_line=anchor,
                    context=context,
                    problems=problems,
                )
    measured_axioms = _axiom_set(evidence_row["axioms"])
    recorded_axioms = _axiom_set(row["evidence_axioms"])
    if measured_axioms != recorded_axioms:
        problems.append(
            f"{context}: recorded citation axioms differ from V4 "
            f"{sorted(recorded_axioms)} != {sorted(measured_axioms)}"
        )
    extras = measured_axioms - ALLOWED_AXIOMS
    if extras:
        problems.append(
            f"{context}: citation has disallowed axioms {sorted(extras)}"
        )


def _validate_witness(
    row: dict[str, str],
    *,
    witness_evidence: dict[tuple[str, str], dict[str, str]],
    context: str,
    problems: list[str],
) -> None:
    if row["evidence_method"] != "compiled_named_witness":
        problems.append(
            f"{context}: VERIFIED_WITNESS needs "
            "evidence_method=compiled_named_witness"
        )
    _require_fields(
        row,
        (
            *REQUIRED_SEMANTIC_FIELDS,
            "evidence_name",
            "evidence_location",
            "evidence_axioms",
            "witness_evidence_key",
        ),
        context=context,
        problems=problems,
    )
    key = (row["name"], row["evidence_name"])
    evidence = witness_evidence.get(key)
    if evidence is None:
        problems.append(f"{context}: no independent witness evidence row for {key}")
        return
    if row["witness_evidence_key"] != "|".join(key):
        problems.append(f"{context}: witness_evidence_key must be definition|witness")
    _forbid_fields(
        row,
        ("finding_id", "finding_severity", "blocker"),
        context=context,
        problems=problems,
    )
    if evidence["definition"] != row["name"]:
        problems.append(f"{context}: witness evidence definition does not match row")
    if evidence["witness"] != row["evidence_name"]:
        problems.append(f"{context}: witness evidence name does not match row")
    if not _path_has_prefix(evidence["source_path"], WITNESS_SOURCE_PREFIX):
        problems.append(
            f"{context}: witness source must be under "
            "HighDimensionalProbability/Verification/scripts/witnesses/"
        )
    if not _path_has_prefix(
        evidence["collector_source"], COLLECTOR_SOURCE_PREFIX
    ):
        problems.append(
            f"{context}: witness collector source must be under "
            ".audit_work/verification/"
        )
    try:
        expected_witness_module = _lean_module_from_source(
            evidence["source_path"]
        )
    except ValueError as error:
        problems.append(f"{context}: {error}")
        expected_witness_module = ""
    if evidence["witness_module"] != expected_witness_module:
        problems.append(
            f"{context}: witness_module {evidence['witness_module']!r} does "
            f"not match source module {expected_witness_module!r}"
        )
    source_path = _safe_project_path(
        evidence["source_path"], context=context, problems=problems
    )
    collector_source = _safe_project_path(
        evidence["collector_source"], context=context, problems=problems
    )
    if evidence["build_log"] == evidence["collector_log"]:
        problems.append(f"{context}: build and collector logs must be distinct")
    source_code: str | None = None
    if source_path is None:
        pass
    elif not source_path.is_file():
        problems.append(f"{context}: witness source is missing")
    else:
        source_code = _lean_code(
            source_path, context=f"{context} witness source", problems=problems
        )
        if source_code is not None:
            if "set_option autoImplicit false" not in source_code:
                problems.append(
                    f"{context}: witness source lacks executable "
                    "set_option autoImplicit false"
                )
            if FORBIDDEN_WITNESS_CODE.search(source_code):
                problems.append(
                    f"{context}: witness source contains executable "
                    "sorry/admit/sorryAx"
                )
    collector_code: str | None = None
    if collector_source is None:
        pass
    elif not collector_source.is_file():
        problems.append(f"{context}: witness collector source is missing")
    else:
        collector_code = _lean_code(
            collector_source,
            context=f"{context} collector source",
            problems=problems,
        )
        if collector_code is not None:
            required_fragments = (
                f"import {expected_witness_module}",
                "set_option autoImplicit false",
                "collectAxioms",
                "getUsedConstants",
                "IO.println",
                "run_cmd",
            )
            missing = [
                fragment
                for fragment in required_fragments
                if fragment not in collector_code
            ]
            if missing:
                problems.append(
                    f"{context}: collector source lacks objective evidence "
                    f"operations/identities: {missing}"
                )
            collector_raw = collector_source.read_text(encoding="utf-8")
            raw_missing = [
                fragment
                for fragment in (COLLECTOR_PREFIX, row["evidence_name"])
                if fragment not in collector_raw
            ]
            if raw_missing:
                problems.append(
                    f"{context}: collector source lacks output identity "
                    f"literals: {raw_missing}"
                )
            if FORBIDDEN_WITNESS_CODE.search(collector_code):
                problems.append(
                    f"{context}: collector source contains executable "
                    "sorry/admit/sorryAx"
                )
            auto_position = collector_code.find(
                "set_option autoImplicit false"
            )
            run_position = collector_code.find("run_cmd")
            if (
                auto_position < 0
                or run_position < 0
                or auto_position > run_position
            ):
                problems.append(
                    f"{context}: collector autoImplicit false must precede "
                    "its run_cmd"
                )

    if source_path is not None:
        _completed_lean_log(
            evidence["build_log"],
            expected_source=source_path,
            context=f"{context} witness build",
            problems=problems,
        )
    collector_log_text: str | None = None
    if collector_source is not None:
        collector_log_text = _completed_lean_log(
            evidence["collector_log"],
            expected_source=collector_source,
            context=f"{context} witness collector",
            problems=problems,
        )
    measured: dict[str, str] | None = None
    if collector_log_text is not None:
        measured = _collector_row(
            collector_log_text,
            expected_name=row["evidence_name"],
            context=f"{context} witness collector",
            problems=problems,
        )
    if measured is not None:
        if measured["module"] != evidence["witness_module"]:
            problems.append(
                f"{context}: collector witness module differs from evidence"
            )
        if measured["name"] != row["evidence_name"]:
            problems.append(
                f"{context}: collector row is not for the named witness"
            )
        if measured["kind"] != "theorem":
            problems.append(f"{context}: collected witness is not a theorem")
        dependencies = {
            value
            for value in measured["type_dependencies"].split(";")
            if value
        }
        if row["name"] not in dependencies:
            problems.append(
                f"{context}: collected witness theorem type does not directly "
                f"mention the audited definition {row['name']}"
            )
        measured_axioms = _axiom_set(measured["axioms"])
        recorded_axioms = _axiom_set(row["evidence_axioms"])
        if measured_axioms != recorded_axioms:
            problems.append(
                f"{context}: recorded witness axioms differ from exact "
                "collector output"
            )
        extras = measured_axioms - ALLOWED_AXIOMS
        if extras:
            problems.append(
                f"{context}: witness has disallowed axioms {sorted(extras)}"
            )
        if source_path is not None and row["evidence_location"]:
            anchor = _resolve_theorem_anchor(
                module=measured["module"],
                name=measured["name"],
                private_user_name=measured["private_user_name"],
                source_relative=evidence["source_path"],
                context=context,
                problems=problems,
            )
            if anchor is not None:
                if source_code is not None:
                    before_declaration = "\n".join(
                        source_code.splitlines()[: anchor - 1]
                    )
                    if "set_option autoImplicit false" not in before_declaration:
                        problems.append(
                            f"{context}: witness autoImplicit false does not "
                            "precede the named declaration"
                        )
                _check_exact_location(
                    row["evidence_location"],
                    expected_relative=evidence["source_path"],
                    expected_line=anchor,
                    context=context,
                    problems=problems,
                )


def _validate_unverified(
    row: dict[str, str], *, context: str, problems: list[str]
) -> None:
    if row["evidence_method"] not in {"", "none"}:
        problems.append(
            f"{context}: UNVERIFIED_SANITY cannot claim an evidence method"
        )
    _require_fields(
        row,
        (
            "finding_id",
            "finding_severity",
            "blocker",
            "review_rationale",
            "reviewer",
            "review_date",
        ),
        context=context,
        problems=problems,
    )
    _forbid_fields(
        row,
        (
            "evidence_name",
            "evidence_location",
            "evidence_axioms",
            "semantic_nontriviality_claim",
            "nondegenerate_model",
            "constant_or_zero_collapse_check",
            "junk_or_empty_boundary_check",
            "measure_or_typeclass_check",
            "witness_evidence_key",
        ),
        context=context,
        problems=problems,
    )
    if row["finding_id"] and FINDING_ID.fullmatch(row["finding_id"]) is None:
        problems.append(f"{context}: malformed V7 finding ID")
    if (
        row["finding_severity"]
        and row["finding_severity"] not in FINDING_SEVERITIES
    ):
        problems.append(f"{context}: invalid finding severity")


def _load_review_rows(
    review_dir: Path, problems: list[str]
) -> tuple[list[dict[str, str]], list[dict[str, str]]]:
    manifest_path = review_dir / DEFAULT_MANIFEST.name
    if not manifest_path.is_file():
        problems.append(f"missing review manifest {manifest_path}")
        return [], []
    try:
        manifest = _read_tsv(manifest_path, MANIFEST_COLUMNS)
    except ValueError as error:
        problems.append(str(error))
        return [], []
    shard_numbers = sorted(
        {
            int(row["shard"])
            for row in manifest
            if row["shard"].isdigit() and int(row["shard"]) > 0
        }
    )
    if shard_numbers != list(range(1, max(shard_numbers, default=0) + 1)):
        problems.append(f"manifest shard IDs are not contiguous: {shard_numbers}")
    rows: list[dict[str, str]] = []
    expected_paths = {
        review_dir / f"v7_definition_review_shard_{shard:02d}.tsv"
        for shard in shard_numbers
    }
    actual_paths = set(review_dir.glob("v7_definition_review_shard_*.tsv"))
    if actual_paths != expected_paths:
        problems.append(
            "review shard file set mismatch: "
            f"missing={sorted(str(path) for path in expected_paths - actual_paths)}, "
            f"extra={sorted(str(path) for path in actual_paths - expected_paths)}"
        )
    module_files: dict[str, set[int]] = collections.defaultdict(set)
    for path in sorted(expected_paths):
        match = re.fullmatch(
            r"v7_definition_review_shard_([0-9]+)\.tsv", path.name
        )
        if match is None:
            problems.append(f"malformed review shard filename: {path}")
            continue
        physical_shard = int(match.group(1))
        try:
            shard_rows = _read_tsv(path, REVIEW_COLUMNS)
        except (OSError, ValueError) as error:
            problems.append(str(error))
            continue
        for row in shard_rows:
            if row["shard"] != str(physical_shard):
                problems.append(
                    f"{path.name}: row {row['review_id']} declares shard "
                    f"{row['shard']!r}, expected {physical_shard}"
                )
            module_files[row["module"]].add(physical_shard)
        rows.extend(shard_rows)
    for module, physical_shards in sorted(module_files.items()):
        if len(physical_shards) != 1:
            problems.append(
                f"module-coherent partition violated for {module}: "
                f"physical shards={sorted(physical_shards)}"
            )
    return manifest, rows


def validate(
    *,
    load_path: Path,
    candidates_path: Path,
    review_dir: Path,
    v4_path: Path,
    witness_evidence_path: Path,
    require_final: bool,
) -> Validation:
    problems: list[str] = []
    try:
        load_rows = _read_tsv(load_path, LOAD_BEARING_COLUMNS)
        candidate_rows = _read_tsv(candidates_path, CANDIDATE_COLUMNS)
    except (FileNotFoundError, ValueError) as error:
        return Validation((), (str(error),), False)
    load_by_name, candidates, input_problems = _validate_inputs(
        load_rows, candidate_rows
    )
    problems.extend(input_problems)
    manifest, rows = _load_review_rows(review_dir, problems)
    shard_count = max(
        (int(row["shard"]) for row in manifest if row["shard"].isdigit()),
        default=0,
    )
    expected_rows = _scaffold_rows(load_by_name, candidates, shard_count or 1)
    expected_by_id = {row["review_id"]: row for row in expected_rows}
    manifest_by_id: dict[str, dict[str, str]] = {}
    for row in manifest:
        review_id = row["review_id"]
        if review_id in manifest_by_id:
            problems.append(f"manifest duplicate review_id {review_id}")
        manifest_by_id[review_id] = row
    actual_by_id: dict[str, dict[str, str]] = {}
    for row in rows:
        review_id = row["review_id"]
        if review_id in actual_by_id:
            problems.append(f"review shards duplicate review_id {review_id}")
        actual_by_id[review_id] = row
        for field, value in row.items():
            if "\n" in value or "\t" in value:
                problems.append(
                    f"{review_id}: field {field} contains a tab/newline"
                )

    expected_ids = set(expected_by_id)
    if set(manifest_by_id) != expected_ids:
        problems.append(
            "manifest/load-bearing coverage mismatch: "
            f"missing={sorted(expected_ids - set(manifest_by_id))}, "
            f"extra={sorted(set(manifest_by_id) - expected_ids)}"
        )
    if set(actual_by_id) != expected_ids:
        problems.append(
            "shard/load-bearing coverage mismatch: "
            f"missing={sorted(expected_ids - set(actual_by_id))}, "
            f"extra={sorted(set(actual_by_id) - expected_ids)}"
        )
    for review_id in sorted(expected_ids & set(manifest_by_id)):
        expected_manifest = _manifest_row(expected_by_id[review_id])
        if manifest_by_id[review_id] != expected_manifest:
            problems.append(f"{review_id}: manifest metadata drift")
    for review_id in sorted(expected_ids & set(actual_by_id)):
        expected = expected_by_id[review_id]
        actual = actual_by_id[review_id]
        for field in MACHINE_METADATA_COLUMNS:
            if actual[field] != expected[field]:
                problems.append(
                    f"{review_id}: machine metadata field {field} drifted"
                )

    needs_v4 = any(
        row["review_status"] == "VERIFIED_CITATION" for row in rows
    )
    needs_witness = any(
        row["review_status"] == "VERIFIED_WITNESS" for row in rows
    )
    v4 = _read_v4(v4_path, problems) if needs_v4 else {}
    witness_evidence = (
        _read_witness_evidence(witness_evidence_path, problems)
        if needs_witness
        else {}
    )
    for row in rows:
        context = f"{row['review_id']} ({row['name']})"
        status = row["review_status"]
        if status not in STATUSES:
            problems.append(f"{context}: unsupported review_status {status!r}")
            continue
        if row["review_date"]:
            if DATE.fullmatch(row["review_date"]) is None:
                problems.append(f"{context}: review_date must be YYYY-MM-DD")
            else:
                try:
                    dt.date.fromisoformat(row["review_date"])
                except ValueError:
                    problems.append(
                        f"{context}: review_date is not a valid calendar date"
                    )
        if status == "UNREVIEWED":
            populated = [
                field
                for field in REVIEW_JUDGMENT_COLUMNS[1:]
                if row[field].strip()
            ]
            if populated:
                problems.append(
                    f"{context}: UNREVIEWED row has judgment fields populated: "
                    + ", ".join(populated)
                )
            if require_final:
                problems.append(f"{context}: final validation forbids UNREVIEWED")
        elif status == "VERIFIED_CITATION":
            _validate_citation(
                row,
                candidate_rows=candidates.get(row["name"], []),
                v4=v4,
                context=context,
                problems=problems,
            )
        elif status == "VERIFIED_WITNESS":
            _validate_witness(
                row,
                witness_evidence=witness_evidence,
                context=context,
                problems=problems,
            )
        else:
            _validate_unverified(row, context=context, problems=problems)

    finding_groups: dict[str, list[dict[str, str]]] = collections.defaultdict(list)
    for row in rows:
        if row["review_status"] == "UNVERIFIED_SANITY" and row["finding_id"]:
            finding_groups[row["finding_id"]].append(row)
    for finding_id, finding_rows in sorted(finding_groups.items()):
        severities = {row["finding_severity"] for row in finding_rows}
        blockers = {row["blocker"].strip() for row in finding_rows}
        if len(severities) != 1:
            problems.append(
                f"{finding_id}: grouped finding rows have inconsistent "
                f"severities {sorted(severities)}"
            )
        if len(blockers) != 1:
            problems.append(
                f"{finding_id}: grouped finding rows have inconsistent blockers"
            )

    final_ready = (
        bool(rows)
        and all(row["review_status"] in FINAL_STATUSES for row in rows)
        and not problems
    )
    return Validation(tuple(rows), tuple(problems), final_ready)


def render_validation(validation: Validation) -> str:
    counts = collections.Counter(
        row["review_status"] for row in validation.rows
    )
    lines = [
        "V7 DEFINITION REVIEW REGISTER VALIDATION",
        f"rows={len(validation.rows)}",
        *(f"status_{status}={counts[status]}" for status in sorted(STATUSES)),
        f"final_ready={str(validation.final_ready).lower()}",
        f"problems={len(validation.problems)}",
        *(f"PROBLEM {problem}" for problem in validation.problems),
        f"result={'PASS' if validation.passed else 'FAIL'}",
        "",
    ]
    return "\n".join(lines)


def _synthetic_inputs(directory: Path) -> tuple[Path, Path]:
    load = directory / "definition_load_bearing.tsv"
    candidates = directory / "definition_nontriviality_candidates.tsv"
    load_rows = [
        {
            "module": "HighDimensionalProbability.Prelude",
            "source_path": "HighDimensionalProbability/Prelude.lean",
            "name": "HDP.syntheticPreludeDef",
            "kind": "definition",
            "is_private": "false",
            "private_user_name": "",
            "is_internal": "false",
            "reason": "all_prelude_defs_structures_classes",
            "tier_b_endpoint_count": "1",
            "tier_b_type_endpoint_count": "1",
            "tier_b_value_endpoint_count": "0",
        },
        {
            "module": "HighDimensionalProbability.Chapter1_Test",
            "source_path": "HighDimensionalProbability/Chapter1_Test.lean",
            "name": "HDP.syntheticThresholdDef",
            "kind": "definition",
            "is_private": "false",
            "private_user_name": "",
            "is_internal": "false",
            "reason": "directly_referenced_by_ge3_tier_b_endpoints",
            "tier_b_endpoint_count": "3",
            "tier_b_type_endpoint_count": "3",
            "tier_b_value_endpoint_count": "0",
        },
        {
            "module": "MatrixConcentration.Prelude",
            "source_path": "MatrixConcentration/Prelude.lean",
            "name": "MatrixConcentration.syntheticPreludeDef",
            "kind": "definition",
            "is_private": "false",
            "private_user_name": "",
            "is_internal": "false",
            "reason": "all_prelude_defs_structures_classes",
            "tier_b_endpoint_count": "0",
            "tier_b_type_endpoint_count": "0",
            "tier_b_value_endpoint_count": "0",
        },
    ]
    candidate_rows = [
        {
            "target_module": "HighDimensionalProbability.Chapter1_Test",
            "target": "HDP.syntheticThresholdDef",
            "target_kind": "definition",
            "candidate_module": (
                "HighDimensionalProbability."
                "Chapter1_AnalysisAndProbabilityRefresher"
            ),
            "candidate_theorem": "HDP.syntheticThresholdDef_eq",
            "origin": "type",
            "score": "12",
            "reasons": "statement-direct,public-name,nontriviality-lexeme",
        }
    ]
    _write_tsv(load, LOAD_BEARING_COLUMNS, load_rows)
    _write_tsv(candidates, CANDIDATE_COLUMNS, candidate_rows)
    return load, candidates


def self_test() -> int:
    with tempfile.TemporaryDirectory(
        prefix="hdp-v7-definition-review-"
    ) as temporary:
        directory = Path(temporary)
        load, candidates = _synthetic_inputs(directory)
        review = directory / "review"
        prepare(
            load_path=load,
            candidates_path=candidates,
            output_dir=review,
            shard_count=2,
            force=False,
        )
        baseline = validate(
            load_path=load,
            candidates_path=candidates,
            review_dir=review,
            v4_path=directory / "absent-v4.tsv",
            witness_evidence_path=directory / "absent-witness.tsv",
            require_final=False,
        )
        if not baseline.passed or baseline.final_ready:
            raise AssertionError(baseline.problems)
        final = validate(
            load_path=load,
            candidates_path=candidates,
            review_dir=review,
            v4_path=directory / "absent-v4.tsv",
            witness_evidence_path=directory / "absent-witness.tsv",
            require_final=True,
        )
        if final.passed or not any(
            "final validation forbids UNREVIEWED" in problem
            for problem in final.problems
        ):
            raise AssertionError("final gate accepted an unreviewed scaffold")

        shard = next(review.glob("v7_definition_review_shard_*.tsv"))
        rows = _read_tsv(shard, REVIEW_COLUMNS)
        candidate_row = next(
            (
                row
                for row in rows
                if row["name"] == "HDP.syntheticThresholdDef"
            ),
            None,
        )
        if candidate_row is None:
            for other in review.glob("v7_definition_review_shard_*.tsv"):
                rows = _read_tsv(other, REVIEW_COLUMNS)
                candidate_row = next(
                    (
                        row
                        for row in rows
                        if row["name"] == "HDP.syntheticThresholdDef"
                    ),
                    None,
                )
                if candidate_row is not None:
                    shard = other
                    break
        assert candidate_row is not None
        candidate_row["review_status"] = "VERIFIED_CITATION"
        candidate_row["evidence_method"] = "citation"
        candidate_row["evidence_name"] = "HDP.syntheticThresholdDef_eq"
        _write_tsv(shard, REVIEW_COLUMNS, rows)
        promoted_without_review = validate(
            load_path=load,
            candidates_path=candidates,
            review_dir=review,
            v4_path=directory / "absent-v4.tsv",
            witness_evidence_path=directory / "absent-witness.tsv",
            require_final=False,
        )
        if promoted_without_review.passed or not any(
            "required review fields are empty" in problem
            for problem in promoted_without_review.problems
        ):
            raise AssertionError(
                "candidate was accepted as evidence without semantic review"
            )
    print(
        "PASS: V7 review framework synthetic calibration; complete scaffold "
        "coverage accepted, final gate rejects UNREVIEWED, and a candidate "
        "cannot self-promote to verified evidence"
    )
    return 0


def _resolve(path: Path) -> Path:
    return path if path.is_absolute() else ROOT / path


def _parse_args(argv: Sequence[str]) -> argparse.Namespace:
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--self-test", action="store_true")
    subparsers = parser.add_subparsers(dest="action")
    prepare_parser = subparsers.add_parser("prepare")
    prepare_parser.add_argument(
        "--load-bearing", type=Path, default=LOAD_BEARING.relative_to(ROOT)
    )
    prepare_parser.add_argument(
        "--candidates",
        type=Path,
        default=NONTRIVIALITY_CANDIDATES.relative_to(ROOT),
    )
    prepare_parser.add_argument(
        "--output-dir", type=Path, default=REVIEW_DIR.relative_to(ROOT)
    )
    prepare_parser.add_argument("--shards", type=int, default=4)
    prepare_parser.add_argument("--force", action="store_true")

    validate_parser = subparsers.add_parser("validate")
    validate_parser.add_argument(
        "--load-bearing", type=Path, default=LOAD_BEARING.relative_to(ROOT)
    )
    validate_parser.add_argument(
        "--candidates",
        type=Path,
        default=NONTRIVIALITY_CANDIDATES.relative_to(ROOT),
    )
    validate_parser.add_argument(
        "--review-dir", type=Path, default=REVIEW_DIR.relative_to(ROOT)
    )
    validate_parser.add_argument(
        "--v4-audit", type=Path, default=DEFAULT_V4.relative_to(ROOT)
    )
    validate_parser.add_argument(
        "--witness-evidence",
        type=Path,
        default=DEFAULT_WITNESS_EVIDENCE.relative_to(ROOT),
    )
    validate_parser.add_argument("--final", action="store_true")
    return parser.parse_args(argv)


def main(argv: Sequence[str] | None = None) -> int:
    args = _parse_args(sys.argv[1:] if argv is None else argv)
    if args.self_test:
        return self_test()
    if args.action == "prepare":
        paths = prepare(
            load_path=_resolve(args.load_bearing),
            candidates_path=_resolve(args.candidates),
            output_dir=_resolve(args.output_dir),
            shard_count=args.shards,
            force=args.force,
        )
        print("\n".join(str(path.relative_to(ROOT)) for path in paths))
        return 0
    if args.action == "validate":
        result = validate(
            load_path=_resolve(args.load_bearing),
            candidates_path=_resolve(args.candidates),
            review_dir=_resolve(args.review_dir),
            v4_path=_resolve(args.v4_audit),
            witness_evidence_path=_resolve(args.witness_evidence),
            require_final=args.final,
        )
        print(render_validation(result), end="")
        return 0 if result.passed else 1
    raise SystemExit("choose --self-test, prepare, or validate")


if __name__ == "__main__":
    raise SystemExit(main())
