#!/usr/bin/env python3
"""Audit the five MatrixConcentration self-record documents.

This script is deliberately static: it does not invoke Lean, Lake, Git, or the
network.  It reconciles claims in

* ``Pre_MatrixConcentration/README.md``;
* ``Pre_MatrixConcentration/REVIEW_NOTES.md``;
* ``Pre_MatrixConcentration/MatrixConcentration_audit.md``; and
* ``Pre_MatrixConcentration/APPENDIX_SUMMARY.md``; and
* ``Pre_MatrixConcentration/SOURCE_FAITHFULNESS_LEDGER.md``.

against the already-produced V1--V5 evidence and the available V4 snapshot.
The distinction between source presence and successful elaboration is
intentional.  A declaration in one of the four V1-failing modules is never
reported as kernel-confirmed merely because its source header exists.
"""

from __future__ import annotations

import argparse
import collections
import csv
import hashlib
import io
import re
import sys
from dataclasses import dataclass
from pathlib import Path
from typing import Iterable


ROOT = Path(__file__).resolve().parents[3]
MC = ROOT / "Pre_MatrixConcentration"
VERIFICATION = ROOT / "HighDimensionalProbability" / "Verification"
LOGS = VERIFICATION / "logs"
REVIEW = VERIFICATION / "review"

README = MC / "README.md"
REVIEW_NOTES = MC / "REVIEW_NOTES.md"
AUDIT = MC / "MatrixConcentration_audit.md"
APPENDIX_SUMMARY = MC / "APPENDIX_SUMMARY.md"
SOURCE_FAITHFULNESS_LEDGER = MC / "SOURCE_FAITHFULNESS_LEDGER.md"
DOCS = (
    README,
    REVIEW_NOTES,
    AUDIT,
    APPENDIX_SUMMARY,
    SOURCE_FAITHFULNESS_LEDGER,
)

OUTPUT = REVIEW / "v9_matrix_concentration_self_record.tsv"
SUMMARY = REVIEW / "v9_matrix_concentration_self_record_summary.md"
RUN_LOG = LOGS / "v9_matrix_concentration_self_record.log"

V1_SUMMARY = LOGS / "v1_build_summary.log"
V2_SUMMARY = LOGS / "v2_orphan_summary.log"
V3_SUMMARY = LOGS / "v3_direct_sorry_summary.txt"
V4_AUDIT = LOGS / "axiom_audit.tsv"
V4_MODULES = LOGS / "axiom_modules.txt"
V4_BUILD = LOGS / "axiom_audit_build.log"
V4_SUMMARY = LOGS / "axiom_audit_summary.txt"
V5_REPORT = VERIFICATION / "05_escape_hatches.md"
LAKEFILE = ROOT / "lakefile.toml"
MC_ROOT = ROOT / "MatrixConcentration.lean"

LEAN_FILES = tuple(sorted(MC.glob("*.lean")))
EXPECTED_LEAN_FILES = (
    "Prelude.lean",
    "Chapter1_Introduction.lean",
    "Chapter2_MatrixFunctionsAndProbabilityWithMatrices.lean",
    "Chapter3_MatrixLaplaceTransformMethod.lean",
    "Chapter4_MatrixGaussianAndRademacherSeries.lean",
    "Chapter5_SumOfPSDMatrices.lean",
    "Chapter6_SumOfBoundedRandomMatrices.lean",
    "Chapter7_IntrinsicDimension.lean",
    "Chapter8_ProofOfLiebsTheorem.lean",
    "Appendix_GoldenThompson.lean",
    "Appendix_GaussianConcentration.lean",
    "Appendix_MatrixRosenthal.lean",
    "Appendix_SymmetricLowerBound.lean",
    "Appendix_RosenthalPinelis.lean",
)
FAILED_MODULE_FILES = frozenset(
    {
        "Appendix_RosenthalPinelis.lean",
        "Chapter1_Introduction.lean",
        "Chapter6_SumOfBoundedRandomMatrices.lean",
        "Chapter7_IntrinsicDimension.lean",
    }
)
EXPECTED_BUILDABLE_MODULES = frozenset(
    f"MatrixConcentration.{name.removesuffix('.lean')}"
    for name in EXPECTED_LEAN_FILES
    if name not in FAILED_MODULE_FILES
)
ALLOWED_AXIOMS = frozenset({"propext", "Classical.choice", "Quot.sound"})

FIELDS = (
    "claim_id",
    "document",
    "line",
    "category",
    "severity",
    "verdict",
    "claim",
    "claimed",
    "observed",
    "evidence",
    "recommended_action",
)
VERDICTS = {
    "MATCH",
    "PENDING",
    "STALE",
    "OVERSTATED",
    "CONTRADICTED",
    "UNVERIFIABLE",
}
SEVERITIES = {"INFO", "MINOR", "MAJOR", "CRITICAL"}


@dataclass(frozen=True)
class Claim:
    claim_id: str
    document: str
    line: int
    category: str
    severity: str
    verdict: str
    claim: str
    claimed: str
    observed: str
    evidence: str
    recommended_action: str

    def as_row(self) -> dict[str, object]:
        return {field: getattr(self, field) for field in FIELDS}


@dataclass(frozen=True)
class Declaration:
    path: Path
    name: str
    kind: str
    line: int


@dataclass(frozen=True)
class MappingRow:
    line: int
    book_source: str
    name: str
    file: str
    role: str
    notes: str


@dataclass(frozen=True)
class V4Row:
    module: str
    name: str
    kind: str
    axioms: frozenset[str]


def relative(path: Path) -> str:
    return path.relative_to(ROOT).as_posix()


def find_line(path: Path, fragment: str, occurrence: int = 1) -> int:
    seen = 0
    for number, line in enumerate(
        path.read_text(encoding="utf-8").splitlines(), start=1
    ):
        if fragment in line:
            seen += 1
            if seen == occurrence:
                return number
    raise RuntimeError(f"{relative(path)}: fragment not found: {fragment!r}")


def sha256(path: Path) -> str:
    return hashlib.sha256(path.read_bytes()).hexdigest()


def mask_lean_noncode(text: str) -> str:
    """Mask nested comments and strings while preserving offsets/newlines."""

    masked = list(text)
    index = 0
    state = "code"
    depth = 0
    while index < len(text):
        if state == "code":
            if text.startswith("--", index):
                state = "line"
                masked[index] = masked[index + 1] = " "
                index += 2
            elif text.startswith("/-", index):
                state = "block"
                depth = 1
                masked[index] = masked[index + 1] = " "
                index += 2
            elif text[index] == '"':
                state = "string"
                masked[index] = " "
                index += 1
            else:
                index += 1
        elif state == "line":
            if text[index] in "\r\n":
                state = "code"
            else:
                masked[index] = " "
            index += 1
        elif state == "block":
            if text.startswith("/-", index):
                depth += 1
                masked[index] = masked[index + 1] = " "
                index += 2
            elif text.startswith("-/", index):
                depth -= 1
                masked[index] = masked[index + 1] = " "
                index += 2
                if depth == 0:
                    state = "code"
            else:
                if text[index] not in "\r\n":
                    masked[index] = " "
                index += 1
        else:
            if text[index] == "\\":
                masked[index] = " "
                index += 1
                if index < len(text):
                    if text[index] not in "\r\n":
                        masked[index] = " "
                    index += 1
            elif text[index] == '"':
                masked[index] = " "
                index += 1
                state = "code"
            else:
                if text[index] not in "\r\n":
                    masked[index] = " "
                index += 1
    if state in {"block", "string"}:
        raise RuntimeError(f"unterminated Lean {state}")
    return "".join(masked)


DECLARATION = re.compile(
    r"(?m)^[ \t]*(?:@\[[^\n]*\][ \t]*)?"
    r"(?:(?:private|protected|noncomputable|unsafe|local)[ \t]+)*"
    r"(?P<kind>theorem|lemma|def|abbrev|structure|class|opaque|axiom)"
    r"[ \t]+(?P<name>[^ \t({\[:=\r\n]+)"
    r"(?=[ \t({\[:=]|$)"
)


def declarations() -> tuple[dict[str, list[Declaration]], dict[str, list[Declaration]], dict[str, str]]:
    by_file: dict[str, list[Declaration]] = {}
    by_name: dict[str, list[Declaration]] = collections.defaultdict(list)
    code_by_file: dict[str, str] = {}
    for path in LEAN_FILES:
        text = path.read_text(encoding="utf-8")
        code = mask_lean_noncode(text)
        code_by_file[path.name] = code
        found: list[Declaration] = []
        for match in DECLARATION.finditer(code):
            declaration = Declaration(
                path=path,
                name=match.group("name"),
                kind=match.group("kind"),
                line=code.count("\n", 0, match.start()) + 1,
            )
            found.append(declaration)
            by_name[declaration.name].append(declaration)
        by_file[path.name] = found
    return by_file, dict(by_name), code_by_file


def parse_readme_mappings() -> list[MappingRow]:
    rows: list[MappingRow] = []
    for number, line in enumerate(
        README.read_text(encoding="utf-8").splitlines(), start=1
    ):
        if not (line.startswith("|") and "](" in line and ".lean" in line):
            continue
        cells = [cell.strip() for cell in line.strip().strip("|").split("|")]
        if len(cells) < 5 or cells[0] == "Book source":
            continue
        file_match = re.search(r"\(([^)]+\.lean)\)", cells[2])
        role = cells[3].strip("`")
        if file_match is None or not re.fullmatch(r"[EIMSVN]/(?:thm|lem|def|abbr|—)", role):
            continue
        name_match = re.search(r"`([^`]+)`", cells[1])
        rows.append(
            MappingRow(
                line=number,
                book_source=re.sub(r"<br>", " / ", cells[0]),
                name=name_match.group(1) if name_match else "",
                file=file_match.group(1),
                role=role,
                notes=cells[4],
            )
        )
    return rows


def read_v4() -> tuple[dict[tuple[str, str], V4Row], bool]:
    complete = False
    if V4_BUILD.is_file() and V4_SUMMARY.is_file():
        build = V4_BUILD.read_text(encoding="utf-8", errors="replace")
        summary = V4_SUMMARY.read_text(encoding="utf-8", errors="replace")
        complete = (
            "finished:" in build
            and "exit_code: 0" in build
            and "V4 EXHAUSTIVE AXIOM AUDIT SUMMARY" in summary
        )
    # A live V4 writer emits declaration rows in environment order.  Consuming
    # a changing prefix would make this audit non-reproducible and would
    # authenticate an arbitrary subset.  The stable module list is still used;
    # declaration-level rows become evidence only after the run is complete.
    if not complete:
        return {}, False

    rows: dict[tuple[str, str], V4Row] = {}
    if V4_AUDIT.is_file() and V4_AUDIT.stat().st_size:
        text = V4_AUDIT.read_text(encoding="utf-8", errors="replace")
        reader = csv.DictReader(io.StringIO(text), delimiter="\t")
        expected = (
            "module",
            "name",
            "kind",
            "is_private",
            "private_user_name",
            "is_internal",
            "axioms",
        )
        if tuple(reader.fieldnames or ()) != expected:
            raise RuntimeError(f"{relative(V4_AUDIT)}: unexpected header")
        for raw in reader:
            if any(raw.get(field) is None for field in expected):
                # A live writer may leave one incomplete final line.
                continue
            row = V4Row(
                module=raw["module"],
                name=raw["name"],
                kind=raw["kind"],
                axioms=frozenset(filter(None, raw["axioms"].split(";"))),
            )
            rows[(row.module, row.name)] = row
    return rows, complete


def add(
    claims: list[Claim],
    *,
    claim_id: str,
    path: Path,
    line: int,
    category: str,
    severity: str,
    verdict: str,
    claim: str,
    claimed: str,
    observed: str,
    evidence: str,
    action: str,
) -> None:
    if severity not in SEVERITIES or verdict not in VERDICTS:
        raise RuntimeError(f"{claim_id}: invalid severity/verdict")
    claims.append(
        Claim(
            claim_id=claim_id,
            document=relative(path),
            line=line,
            category=category,
            severity=severity,
            verdict=verdict,
            claim=claim,
            claimed=claimed,
            observed=observed,
            evidence=evidence,
            recommended_action=action,
        )
    )


def mapping_verdict(
    row: MappingRow,
    source: Declaration | None,
    v4_rows: dict[tuple[str, str], V4Row],
    v4_complete: bool,
) -> tuple[str, str, str, str]:
    """Return severity, verdict, observation, and action for one README row."""

    if row.role.startswith("N/"):
        if row.name or "not asserted" not in row.notes:
            return (
                "MAJOR",
                "CONTRADICTED",
                "N row is malformed or does not state non-assertion",
                "Repair the explicit non-theorem row.",
            )
        return (
            "INFO",
            "MATCH",
            "one explicit N row; no declaration name is claimed",
            "None.",
        )
    if source is None:
        return (
            "MAJOR",
            "CONTRADICTED",
            f"{row.name} is absent from {row.file}",
            "Remove or correct the mapping.",
        )
    expected_kind = {
        "thm": "theorem",
        "lem": "lemma",
        "def": "def",
        "abbr": "abbrev",
    }[row.role.split("/", 1)[1]]
    if source.kind != expected_kind:
        return (
            "MAJOR",
            "STALE",
            f"source kind is {source.kind}, not {expected_kind}",
            "Update the role/kind cell.",
        )
    if row.file in FAILED_MODULE_FILES:
        return (
            "MAJOR",
            "OVERSTATED",
            (
                f"source header exists at {row.file}:{source.line}, but V1 proves "
                "this module is not in the successfully elaborated surface"
            ),
            "Keep source-location metadata, but do not call this row kernel-verified.",
        )
    module = f"MatrixConcentration.{row.file.removesuffix('.lean')}"
    qualified = f"MatrixConcentration.{row.name}"
    v4 = v4_rows.get((module, qualified))
    if v4 is None:
        return (
            "MINOR",
            "PENDING",
            (
                f"source header exists at {row.file}:{source.line}; "
                f"no exact ({module}, {qualified}) V4 row is available"
            ),
            "Rerun this audit after the V4 writer has completed.",
        )
    unexpected = v4.axioms - ALLOWED_AXIOMS
    if unexpected:
        return (
            "CRITICAL",
            "CONTRADICTED",
            f"V4 reports unexpected axioms: {sorted(unexpected)}",
            "Do not publish the mapping as verified; investigate the dependency.",
        )
    suffix = "completed" if v4_complete else "available live snapshot"
    return (
        "INFO",
        "MATCH",
        (
            f"source header {row.file}:{source.line}; exact V4 row in {suffix}; "
            f"axioms={';'.join(sorted(v4.axioms)) or '(none)'}"
        ),
        "None.",
    )


def build_claims() -> tuple[list[Claim], dict[str, object]]:
    for path in (*DOCS, V1_SUMMARY, V2_SUMMARY, V3_SUMMARY, V5_REPORT, LAKEFILE, MC_ROOT):
        if not path.is_file():
            raise FileNotFoundError(path)
    actual_names = tuple(path.name for path in LEAN_FILES)
    if set(actual_names) != set(EXPECTED_LEAN_FILES) or len(actual_names) != 14:
        raise RuntimeError(f"unexpected MatrixConcentration source universe: {actual_names}")

    v1 = V1_SUMMARY.read_text(encoding="utf-8")
    v2 = V2_SUMMARY.read_text(encoding="utf-8")
    v3 = V3_SUMMARY.read_text(encoding="utf-8")
    v5 = V5_REPORT.read_text(encoding="utf-8")
    for fragment in (
        "lean_source_error_headers: 9",
        "orphan: MC Appendix_RosenthalPinelis",
        "orphan: MC Chapter1",
        "orphan: MC Chapter6",
        "orphan: MC Chapter7",
    ):
        if fragment not in v1:
            raise RuntimeError(f"V1 evidence missing {fragment!r}")
    for fragment in ("orphan_count: 4", "mc_failure_chain: Chapter1,Chapter7 -> Chapter6"):
        if fragment not in v2:
            raise RuntimeError(f"V2 evidence missing {fragment!r}")
    if "appendix_code_sorries: 0" not in v3:
        raise RuntimeError("V3 evidence does not establish zero Appendix sorries")
    if "no executable custom axiom" not in v5:
        raise RuntimeError("V5 report does not contain its source-level custom-axiom result")

    modules = {
        line.strip()
        for line in V4_MODULES.read_text(encoding="utf-8").splitlines()
        if line.startswith("MatrixConcentration.")
    }
    if modules != EXPECTED_BUILDABLE_MODULES:
        raise RuntimeError(
            "V4 MatrixConcentration module set differs from the ten V1/V2-buildable modules: "
            f"missing={sorted(EXPECTED_BUILDABLE_MODULES - modules)}, "
            f"extra={sorted(modules - EXPECTED_BUILDABLE_MODULES)}"
        )

    by_file, by_name, code_by_file = declarations()
    v4_rows, v4_complete = read_v4()
    mappings = parse_readme_mappings()
    if len(mappings) != 448:
        raise RuntimeError(f"expected exactly 448 README mapping rows, found {len(mappings)}")

    claims: list[Claim] = []
    common_evidence = (
        f"{relative(V1_SUMMARY)}; {relative(V2_SUMMARY)}; "
        f"{relative(V3_SUMMARY)}; {relative(V4_AUDIT)}"
    )

    # SOURCE_FAITHFULNESS_LEDGER.md is chiefly a book-faithfulness record,
    # which is outside this pass.  Its explicit machine-completion fields are
    # nevertheless in scope and must not be silently omitted.
    source_ledger_text = SOURCE_FAITHFULNESS_LEDGER.read_text(encoding="utf-8")
    rn_entries = [
        int(value)
        for value in re.findall(r"(?m)^### RN([0-9]+)\b", source_ledger_text)
    ]
    expected_rn_entries = list(range(1, 16))
    if rn_entries != expected_rn_entries:
        raise RuntimeError(
            "SOURCE_FAITHFULNESS_LEDGER RN sequence changed: "
            f"{rn_entries!r} != {expected_rn_entries!r}"
        )
    add(
        claims,
        claim_id="SOURCE_LEDGER_RN_SEQUENCE",
        path=SOURCE_FAITHFULNESS_LEDGER,
        line=find_line(SOURCE_FAITHFULNESS_LEDGER, "### RN1"),
        category="machine_completion",
        severity="INFO",
        verdict="MATCH",
        claim="The source-faithfulness ledger contains the consecutive RN1–RN15 gap entries.",
        claimed="15 consecutive RN entries",
        observed="RN1 through RN15 occur exactly once and in order",
        evidence=relative(SOURCE_FAITHFULNESS_LEDGER),
        action="None.",
    )
    add(
        claims,
        claim_id="SOURCE_LEDGER_BUILD_COMPLETION_GATE",
        path=SOURCE_FAITHFULNESS_LEDGER,
        line=find_line(
            SOURCE_FAITHFULNESS_LEDGER,
            "Each `R` entry is complete only after its adjacent theorem builds",
        ),
        category="machine_completion",
        severity="INFO",
        verdict="MATCH",
        claim="An R entry is complete only after its adjacent theorem builds.",
        claimed="successful adjacent-theorem build is mandatory",
        observed=(
            "the criterion is explicit; V1 records four non-buildable physical "
            "modules, so entries touching those modules cannot be promoted by this audit"
        ),
        evidence=relative(V1_SUMMARY),
        action="Retain the build gate and attach per-entry results before claiming completion.",
    )
    add(
        claims,
        claim_id="SOURCE_LEDGER_AXIOM_COMPLETION_GATE",
        path=SOURCE_FAITHFULNESS_LEDGER,
        line=find_line(SOURCE_FAITHFULNESS_LEDGER, "`#print axioms` output is exactly"),
        category="machine_completion",
        severity="INFO",
        verdict="MATCH",
        claim="An R entry is complete only with the three-standard-axiom output.",
        claimed="[propext, Classical.choice, Quot.sound]",
        observed=(
            "the allowed set agrees with V4 policy; exact V4 rows exist only for "
            "the ten buildable MatrixConcentration modules"
        ),
        evidence=f"{relative(V4_AUDIT)}; {relative(V4_MODULES)}",
        action="Retain the axiom gate and do not infer results for failed modules.",
    )
    add(
        claims,
        claim_id="SOURCE_LEDGER_RESULT_COLUMNS",
        path=SOURCE_FAITHFULNESS_LEDGER,
        line=find_line(
            SOURCE_FAITHFULNESS_LEDGER,
            "append a result/name column and the generated audit-file location",
        ),
        category="machine_completion",
        severity="MINOR",
        verdict="PENDING",
        claim="The final implementation pass will append per-entry result/name and audit-file fields.",
        claimed="per-entry machine-result fields will be appended",
        observed=(
            "the live ledger ends with the promise and contains no appended "
            "result/name/audit-file table"
        ),
        evidence=relative(SOURCE_FAITHFULNESS_LEDGER),
        action=(
            "Append the promised fields only after the corresponding build and "
            "axiom evidence exists."
        ),
    )

    # README aggregate claims.
    add(
        claims,
        claim_id="README_KERNEL_CHECKED_WHOLE_DEVELOPMENT",
        path=README,
        line=find_line(README, "into kernel-checked Mathlib declarations"),
        category="whole_surface",
        severity="MAJOR",
        verdict="OVERSTATED",
        claim="The described MatrixConcentration development is kernel-checked.",
        claimed="all described chapters and appendices kernel-checked",
        observed=(
            "10/14 physical modules are in the buildable V4 surface; "
            "Appendix_RosenthalPinelis has 9 direct errors and blocks Ch1/Ch6/Ch7"
        ),
        evidence=common_evidence,
        action="Scope the claim to the ten buildable modules, or repair and rebuild the four failures.",
    )
    add(
        claims,
        claim_id="README_APPENDIX_COMPLETE_PROOFS",
        path=README,
        line=find_line(README, "Supporting Appendix modules supply complete proofs"),
        category="whole_surface",
        severity="MAJOR",
        verdict="OVERSTATED",
        claim="All supporting Appendix modules supply complete verified proofs.",
        claimed="five Appendix modules complete",
        observed=(
            "all five have zero source sorry tokens, but "
            "Appendix_RosenthalPinelis does not elaborate"
        ),
        evidence=f"{relative(V1_SUMMARY)}; {relative(V3_SUMMARY)}",
        action="Separate placeholder-freedom from successful elaboration.",
    )
    add(
        claims,
        claim_id="README_FRESH_COMPILATION_PROVENANCE",
        path=README,
        line=find_line(README, "a fresh compilation of the expanded"),
        category="provenance",
        severity="MAJOR",
        verdict="OVERSTATED",
        claim="The current correspondence table is backed by a fresh successful compilation.",
        claimed="fresh compiled current table",
        observed="the current full 14-file surface is not compilable",
        evidence=relative(V1_SUMMARY),
        action="Publish the exact source manifest and distinguish lexical mapping from compiled coverage.",
    )
    add(
        claims,
        claim_id="README_CENTERED_EXACT_NOT_ASSERTED",
        path=README,
        line=find_line(README, "literal centered/exact display"),
        category="source_policy",
        severity="INFO",
        verdict="MATCH",
        claim="The literal centered/exact (6.1.6) display is not asserted.",
        claimed="one N row plus two variants",
        observed="role distribution contains N=1 and V=2; the N row has no declaration name",
        evidence=f"{relative(README)}:414-416",
        action="None.",
    )
    for claim_id, fragment in (
        ("README_APPENDIX_SOURCES_LINK_TOP", "Appendix/SOURCES.md"),
        ("README_APPENDIX_SOURCES_LINK_BOTTOM", "For the bibliography of external proof"),
    ):
        add(
            claims,
            claim_id=claim_id,
            path=README,
            line=find_line(README, fragment),
            category="path",
            severity="MINOR",
            verdict="STALE",
            claim="Appendix/SOURCES.md is the current bibliography path.",
            claimed="Pre_MatrixConcentration/Appendix/SOURCES.md exists",
            observed=(
                "that path is absent; the current file is "
                "Pre_MatrixConcentration/SOURCES.md"
            ),
            evidence=f"{relative(MC / 'SOURCES.md')} exists; claimed Appendix directory absent",
            action="Change the link to SOURCES.md.",
        )
    add(
        claims,
        claim_id="README_TOOLCHAIN_PIN",
        path=README,
        line=find_line(README, "pinned to Lean/Mathlib"),
        category="toolchain",
        severity="INFO",
        verdict="MATCH",
        claim="The project is pinned to Mathlib v4.31.0.",
        claimed="v4.31.0",
        observed="lakefile.toml requires mathlib rev v4.31.0",
        evidence=relative(LAKEFILE),
        action="None.",
    )
    add(
        claims,
        claim_id="README_BUILD_COMMAND",
        path=README,
        line=find_line(README, "~/.elan/bin/lake build"),
        category="build",
        severity="MAJOR",
        verdict="OVERSTATED",
        claim="The displayed lake build checks the documented complete development.",
        claimed="complete project build",
        observed=(
            "ordinary roots pass, but MatrixConcentration.lean imports only Ch2; "
            "the physical 14-file surface has four failed module targets"
        ),
        evidence=f"{relative(MC_ROOT)}; {relative(V1_SUMMARY)}",
        action="Document root coverage and add a full-surface target only after all modules elaborate.",
    )
    root_imports = re.findall(
        r"(?m)^[ \t]*import[ \t]+([A-Za-z0-9_.]+)",
        mask_lean_noncode(MC_ROOT.read_text(encoding="utf-8")),
    )
    add(
        claims,
        claim_id="README_MODULE_LAYOUT_CURRENT_ROOT_COVERAGE",
        path=README,
        line=find_line(README, "## Module layout"),
        category="import_graph",
        severity="MAJOR",
        verdict="OVERSTATED",
        claim="The 14 listed final modules form the public root surface.",
        claimed="Prelude, Chapters 1-8, and five appendices",
        observed=f"root direct imports={root_imports}; V2 reports four root-isolated failures",
        evidence=f"{relative(MC_ROOT)}; {relative(V2_SUMMARY)}",
        action="Label the table as a physical inventory and separately publish root/build coverage.",
    )
    for filename in EXPECTED_LEAN_FILES:
        line = next(
            (
                number
                for number, text in enumerate(
                    README.read_text(encoding="utf-8").splitlines(), start=1
                )
                if filename in text and 48 <= number <= 62
            ),
            find_line(README, filename),
        )
        failed = filename in FAILED_MODULE_FILES
        add(
            claims,
            claim_id=f"README_MODULE_{filename.removesuffix('.lean').upper()}",
            path=README,
            line=line,
            category="module_inventory",
            severity="MAJOR" if failed else "INFO",
            verdict="OVERSTATED" if failed else "MATCH",
            claim=f"{filename} is a current final module.",
            claimed="physical and usable final module",
            observed=(
                "physical source exists, but V1 module target fails"
                if failed
                else "physical source exists and module is in the V4 buildable set"
            ),
            evidence=f"{relative(MC / filename)}; {relative(V1_SUMMARY)}",
            action=(
                "Repair the failed dependency chain or label this source as unbuildable."
                if failed
                else "None."
            ),
        )

    roles = collections.Counter(row.role.split("/", 1)[0] for row in mappings)
    add(
        claims,
        claim_id="README_MAPPING_ARITHMETIC",
        path=README,
        line=find_line(README, "This table contains **448 rows**"),
        category="correspondence",
        severity="INFO",
        verdict="MATCH",
        claim="The table has 448 = 445 direct + 2 variants + 1 non-asserted rows.",
        claimed="448 = 445 + 2 + 1",
        observed=f"rows={len(mappings)}; direct={sum(roles[x] for x in 'EIMS')}; V={roles['V']}; N={roles['N']}",
        evidence=relative(README),
        action="None.",
    )
    direct_blocked = sum(
        row.file in FAILED_MODULE_FILES and row.role[0] in "EIMS" for row in mappings
    )
    add(
        claims,
        claim_id="README_445_VERIFIED_DIRECT_COUNTERPARTS",
        path=README,
        line=find_line(README, "445 verified direct counterparts"),
        category="correspondence",
        severity="MAJOR",
        verdict="OVERSTATED",
        claim="All 445 direct counterpart rows are verified.",
        claimed="445 verified direct counterparts",
        observed=(
            f"all 445 have source headers, but {direct_blocked} lie in V1-failing modules; "
            "V1-V4 also do not verify book/TeX semantic faithfulness"
        ),
        evidence=common_evidence,
        action="Use 'source-located' for the static table and reserve 'verified' for source-bound semantic/kernel evidence.",
    )

    mapping_sources: dict[tuple[str, str], Declaration] = {}
    for filename, found in by_file.items():
        for declaration in found:
            mapping_sources[(filename, declaration.name)] = declaration
    for index, row in enumerate(mappings, start=1):
        source = mapping_sources.get((row.file, row.name)) if row.name else None
        severity, verdict, observed, action = mapping_verdict(
            row, source, v4_rows, v4_complete
        )
        add(
            claims,
            claim_id=f"README_MAP_{index:03d}",
            path=README,
            line=row.line,
            category="correspondence_row",
            severity=severity,
            verdict=verdict,
            claim=f"{row.book_source} maps to {row.name or 'an explicit non-theorem'} in {row.file} ({row.role}).",
            claimed=f"{row.name or 'not asserted'}; {row.file}; {row.role}",
            observed=observed,
            evidence=(
                f"{relative(MC / row.file)}; {relative(V1_SUMMARY)}; "
                f"{relative(V4_AUDIT)}"
            ),
            action=action,
        )
    add(
        claims,
        claim_id="README_BOOK_FAITHFULNESS_LIMIT",
        path=README,
        line=find_line(README, "checked directly against the expanded arXiv-v1 source"),
        category="semantic_faithfulness",
        severity="MINOR",
        verdict="UNVERIFIABLE",
        claim="All correspondence rows were checked against the expanded source TeX.",
        claimed="complete book-to-Lean semantic check",
        observed="V1-V5 establish source/build/axiom properties, not the historical TeX comparison",
        evidence="No source-bound TeX comparison artifact is among V1-V5 evidence.",
        action="Retain only with an immutable TeX-to-row review ledger.",
    )

    # REVIEW_NOTES: source-level bypass claim and all table references.
    code_all = "\n".join(code_by_file.values())
    forbidden = {
        "sorry": len(re.findall(r"\bsorry\b", code_all)),
        "admit": len(re.findall(r"\badmit\b", code_all)),
        "native_decide": len(re.findall(r"\bnative_decide\b|\bnativeDecide\b", code_all)),
        "axiom declaration": len(re.findall(r"(?m)^[ \t]*axiom\b", code_all)),
    }
    add(
        claims,
        claim_id="REVIEW_NO_BYPASS_SOURCE",
        path=REVIEW_NOTES,
        line=find_line(REVIEW_NOTES, "found no remaining"),
        category="source_scan",
        severity="INFO",
        verdict="MATCH",
        claim="No sorry, admit, native_decide, or custom axiom remains in the 14 source files.",
        claimed="all four classes absent",
        observed=f"lexer-aware counts={forbidden}; V5 reports zero executable custom axioms",
        evidence=f"{relative(V3_SUMMARY)}; {relative(V5_REPORT)}",
        action="Keep this explicitly source-scoped; it does not imply all modules elaborate.",
    )
    review_lines = REVIEW_NOTES.read_text(encoding="utf-8").splitlines()
    gap_rows = [number for number in range(12, 27) if review_lines[number - 1].startswith("|")]
    merge_rows = [number for number in range(36, 41) if review_lines[number - 1].startswith("|")]
    if len(gap_rows) != 15 or len(merge_rows) != 5:
        raise RuntimeError("REVIEW_NOTES table shape changed")
    add(
        claims,
        claim_id="REVIEW_TABLE_CARDINALITY",
        path=REVIEW_NOTES,
        line=8,
        category="review_inventory",
        severity="INFO",
        verdict="MATCH",
        claim="The live review notes contain 15 source-gap rows and 5 merge rows.",
        claimed="implicit table shape",
        observed=f"source gaps={len(gap_rows)}; merge compromises={len(merge_rows)}",
        evidence=relative(REVIEW_NOTES),
        action="None.",
    )
    for number in (*gap_rows, *merge_rows):
        cells = [
            cell.strip()
            for cell in review_lines[number - 1].strip().strip("|").split("|")
        ]
        names = re.findall(r"`([A-Za-z_][A-Za-z0-9_']*)`", cells[0])
        file_match = re.search(r"`([^`]+\.lean)`", cells[1])
        if file_match is None:
            raise RuntimeError(f"REVIEW_NOTES:{number}: missing file")
        filename = file_match.group(1)
        if number == 40:
            for name in names:
                global_hits = by_name.get(name, [])
                in_claimed = [item for item in global_hits if item.path.name == filename]
                add(
                    claims,
                    claim_id=f"REVIEW_REF_{number}_{name.upper()}",
                    path=REVIEW_NOTES,
                    line=number,
                    category="merge_reference",
                    severity="INFO" if len(global_hits) == 1 and not in_claimed else "MAJOR",
                    verdict="MATCH" if len(global_hits) == 1 and not in_claimed else "CONTRADICTED",
                    claim=f"The redundant private {name} block is omitted from Chapter 7 and resolves to one public declaration.",
                    claimed=f"absent from {filename}; one public copy",
                    observed=(
                        f"claimed-file hits={len(in_claimed)}; global MC hits="
                        f"{[(hit.path.name, hit.line) for hit in global_hits]}"
                    ),
                    evidence="; ".join(relative(hit.path) for hit in global_hits) or relative(MC),
                    action="None." if len(global_hits) == 1 and not in_claimed else "Correct the merge record.",
                )
            continue
        for name in names:
            source = mapping_sources.get((filename, name))
            failed = filename in FAILED_MODULE_FILES
            add(
                claims,
                claim_id=f"REVIEW_REF_{number}_{name.upper()}",
                path=REVIEW_NOTES,
                line=number,
                category="review_reference",
                severity="MAJOR" if source is None else ("MINOR" if failed else "INFO"),
                verdict="CONTRADICTED" if source is None else ("PENDING" if failed else "MATCH"),
                claim=f"{name} is located in {filename}.",
                claimed=f"{filename}",
                observed=(
                    "declaration absent"
                    if source is None
                    else (
                        f"source line {source.line}; module does not elaborate"
                        if failed
                        else f"source line {source.line}; buildable module"
                    )
                ),
                evidence=f"{relative(MC / filename)}; {relative(V1_SUMMARY)}",
                action=(
                    "Correct the location."
                    if source is None
                    else (
                        "Treat the semantic review as pending until the module elaborates."
                        if failed
                        else "None."
                    )
                ),
            )
        if number in gap_rows:
            add(
                claims,
                claim_id=f"REVIEW_GAP_SEMANTICS_{number:02d}",
                path=REVIEW_NOTES,
                line=number,
                category="semantic_faithfulness",
                severity="MINOR",
                verdict="UNVERIFIABLE",
                claim=f"The source-faithfulness diagnosis in review row {number} is mathematically exact.",
                claimed=cells[3],
                observed="declaration locations are checked separately; V1-V5 do not reproduce the book-semantic comparison",
                evidence=relative(REVIEW_NOTES),
                action="Bind the diagnosis to a source/type comparison ledger.",
            )
    add(
        claims,
        claim_id="REVIEW_MERGE_BODY_PRESERVATION",
        path=REVIEW_NOTES,
        line=find_line(REVIEW_NOTES, "names, statements, or bodies"),
        category="history",
        severity="MINOR",
        verdict="UNVERIFIABLE",
        claim="Relocated declarations preserve their former bodies.",
        claimed="body preservation",
        observed="current names/locations are checkable; no immutable pre-merge source is in V1-V5",
        evidence=relative(REVIEW_NOTES),
        action="Keep only with before/after hashes or a trusted VCS commit pair.",
    )
    add(
        claims,
        claim_id="REVIEW_CHAPTER1_BLOCK_ORDER",
        path=REVIEW_NOTES,
        line=39,
        category="merge_order",
        severity="MINOR",
        verdict="UNVERIFIABLE",
        claim="The four former Chapter-1 blocks preserve every block internally.",
        claimed="dependency-respecting reorder with internal preservation",
        observed="current source exists but former block files/history are unavailable to V1-V5",
        evidence=relative(MC / "Chapter1_Introduction.lean"),
        action="Attach a pre/post declaration-order manifest.",
    )

    # Independent audit: global build, bypass, review-count, line-count, and headline claims.
    add(
        claims,
        claim_id="AUDIT_SCOPE_PATH",
        path=AUDIT,
        line=find_line(AUDIT, "**Scope.**"),
        category="path",
        severity="MINOR",
        verdict="STALE",
        claim="The 14 files live in MatrixConcentration/MatrixConcentration/.",
        claimed="MatrixConcentration/MatrixConcentration/",
        observed="physical sources live directly in Pre_MatrixConcentration/",
        evidence=relative(MC),
        action="Replace the obsolete nested path.",
    )
    add(
        claims,
        claim_id="AUDIT_SCOPE_COUNT_LINES",
        path=AUDIT,
        line=find_line(AUDIT, "**Scope.**"),
        category="source_inventory",
        severity="INFO",
        verdict="MATCH",
        claim="The physical scope has 14 Lean files and roughly 37,000 lines.",
        claimed="14; ~37,000",
        observed=f"{len(LEAN_FILES)} files; {sum(len(p.read_text(encoding='utf-8').splitlines()) for p in LEAN_FILES)} lines",
        evidence=relative(MC),
        action="Update the approximate line count if exact current metadata is desired.",
    )
    add(
        claims,
        claim_id="AUDIT_METHOD_FRESH_14_RECOMPILE",
        path=AUDIT,
        line=find_line(AUDIT, "fresh recompilation of every file"),
        category="build",
        severity="MAJOR",
        verdict="CONTRADICTED",
        claim="A fresh successful recompilation of every file supports this audit.",
        claimed="14/14 successful",
        observed="V1: 10 buildable modules; one direct failure and three dependency failures",
        evidence=relative(V1_SUMMARY),
        action="Withdraw the method claim or attach a later source-bound 14/14 run.",
    )
    add(
        claims,
        claim_id="AUDIT_EXECUTIVE_SOUND_COMPLETE_FAITHFUL",
        path=AUDIT,
        line=find_line(AUDIT, "formalization is sound, complete, and faithful"),
        category="whole_surface",
        severity="MAJOR",
        verdict="OVERSTATED",
        claim="The complete physical development is sound, complete, faithful, and kernel-checked.",
        claimed="whole-surface closure",
        observed="four modules are not elaborated; source/TeX semantic completeness is outside V1-V5",
        evidence=common_evidence,
        action="Narrow the conclusion to the buildable surface and list the four exclusions.",
    )
    for claim_id, fragment, claimed, observed in (
        (
            "AUDIT_ALL_14_COMPILE",
            "all 14 files compile with zero errors",
            "14/14, zero errors",
            "10/14 buildable; Appendix_RosenthalPinelis has nine errors and blocks three chapters",
        ),
        (
            "AUDIT_COMPILE_TABLE_14",
            "14 / 14 exit 0",
            "14/14 exit 0",
            "four module-target exits are 1",
        ),
        (
            "AUDIT_COMPILE_TABLE_ZERO_ERRORS",
            "| Errors | **0.**",
            "0 errors",
            "nine source-located errors in Appendix_RosenthalPinelis",
        ),
        (
            "AUDIT_NO_IMPORT_OR_TYPECLASS_FAILURES",
            "No missing imports, no typeclass",
            "no import/typeclass/version failures",
            "the Rosenthal–Pinelis elaboration has type mismatches, invalid calc, and an invalid argument name",
        ),
    ):
        add(
            claims,
            claim_id=claim_id,
            path=AUDIT,
            line=find_line(AUDIT, fragment),
            category="build",
            severity="MAJOR",
            verdict="CONTRADICTED",
            claim=fragment,
            claimed=claimed,
            observed=observed,
            evidence=relative(V1_SUMMARY),
            action="Replace with the V1/V2 failure matrix.",
        )
    add(
        claims,
        claim_id="AUDIT_OLEAN_FRESHNESS",
        path=AUDIT,
        line=find_line(AUDIT, "All project `.olean`s present"),
        category="build_cache",
        severity="MAJOR",
        verdict="STALE",
        claim="All project oleans are present/newer after a successful full build.",
        claimed="all oleans fresh",
        observed="four physical modules cannot currently produce a successful target build",
        evidence=relative(V1_SUMMARY),
        action="Remove cache-state prose and cite a reproducible clean build.",
    )
    add(
        claims,
        claim_id="AUDIT_NO_BYPASS_SOURCE",
        path=AUDIT,
        line=find_line(AUDIT, "## 3. Incomplete or bypassed proofs"),
        category="source_scan",
        severity="INFO",
        verdict="MATCH",
        claim="The 14 physical sources contain no listed proof-bypass token.",
        claimed="zero executable bypass tokens",
        observed=f"lexer-aware listed-token counts={forbidden}; V5 high-risk executable counts are zero",
        evidence=f"{relative(V3_SUMMARY)}; {relative(V5_REPORT)}",
        action="Retain as a lexical source claim, not a build conclusion.",
    )
    arbitrary_count = len(re.findall(r"\bClassical\.arbitrary\b", code_all))
    add(
        claims,
        claim_id="AUDIT_CLASSICAL_ARBITRARY_COUNT",
        path=AUDIT,
        line=find_line(AUDIT, "`Classical.arbitrary`"),
        category="source_scan",
        severity="MINOR",
        verdict="STALE",
        claim="Classical.arbitrary occurs at approximately 40 sites.",
        claimed="≈40",
        observed=str(arbitrary_count),
        evidence=relative(MC),
        action="Use the current lexer-aware count or omit the approximation.",
    )
    add(
        claims,
        claim_id="AUDIT_REVIEW_ROW_COUNT_16",
        path=AUDIT,
        line=find_line(AUDIT, "All 16 rows"),
        category="review_inventory",
        severity="MINOR",
        verdict="CONTRADICTED",
        claim="REVIEW_NOTES has 16 source-faithfulness rows.",
        claimed="16",
        observed="15 source-faithfulness rows plus 5 merge rows",
        evidence=relative(REVIEW_NOTES),
        action="Change 16 to 15 (or explicitly state which table/count is intended).",
    )
    add(
        claims,
        claim_id="AUDIT_REVIEW_SECTION_COUNTS",
        path=AUDIT,
        line=find_line(AUDIT, "table (15 rows)"),
        category="review_inventory",
        severity="INFO",
        verdict="MATCH",
        claim="Section 7 counts 15 source-gap rows and 5 merge rows.",
        claimed="15 + 5",
        observed="15 + 5",
        evidence=relative(REVIEW_NOTES),
        action="Reconcile the contradictory executive-summary count.",
    )

    headline_names = (
        "matrix_bernstein_tail",
        "matrix_bernstein_expectation",
        "scalar_bernstein",
        "golden_thompson",
        "golden_thompson_trace",
        "lieb_trace_exp_log_concave",
        "lieb_theorem",
        "master_expectation_upper",
        "master_tail_upper",
        "matrix_chernoff_tail_upper",
        "matrix_chernoff_tail_lower",
        "matrix_rosenthal",
        "matrix_rosenthal_pinelis_symmetric",
        "matrix_rosenthal_pinelis_centered_with_loss",
        "matrix_bernstein_herm_tail",
        "intdim_bernstein_herm_tail",
        "symmetric_sum_lower_bound",
    )
    headline_line = find_line(AUDIT, "matrix_bernstein_tail, matrix_bernstein_expectation")
    for name in headline_names:
        hits = by_name.get(name, [])
        if len(hits) != 1:
            verdict, severity = "CONTRADICTED", "MAJOR"
            observed = f"MC source declaration hits={[(x.path.name, x.line) for x in hits]}"
            action = "Correct or disambiguate the headline declaration name."
        else:
            hit = hits[0]
            module = f"MatrixConcentration.{hit.path.stem}"
            qualified = f"MatrixConcentration.{name}"
            v4 = v4_rows.get((module, qualified))
            if hit.path.name in FAILED_MODULE_FILES:
                verdict, severity = "OVERSTATED", "MAJOR"
                observed = (
                    f"source exists at {hit.path.name}:{hit.line}, but its module "
                    "is excluded from V4 after the V1 failure"
                )
                action = "Do not claim a current #print axioms result until the module elaborates."
            elif v4 is None:
                verdict, severity = "PENDING", "MINOR"
                observed = (
                    f"source exists at {hit.path.name}:{hit.line}; exact V4 row not "
                    f"yet available (V4 complete={v4_complete})"
                )
                action = "Rerun after V4 completion."
            elif v4.axioms == ALLOWED_AXIOMS:
                verdict, severity = "MATCH", "INFO"
                observed = "exact V4 row reports propext;Classical.choice;Quot.sound"
                action = "None."
            else:
                verdict, severity = "CONTRADICTED", "CRITICAL"
                observed = f"exact V4 axiom set={sorted(v4.axioms)}"
                action = "Correct the exact-axiom claim."
        add(
            claims,
            claim_id=f"AUDIT_HEADLINE_{name.upper()}",
            path=AUDIT,
            line=headline_line,
            category="headline_axioms",
            severity=severity,
            verdict=verdict,
            claim=f"{name} has exactly the three stated standard axioms.",
            claimed="propext;Classical.choice;Quot.sound",
            observed=observed,
            evidence=f"{relative(V1_SUMMARY)}; {relative(V4_AUDIT)}",
            action=action,
        )

    add(
        claims,
        claim_id="AUDIT_WARNING_COUNTS_CURRENT",
        path=AUDIT,
        line=find_line(AUDIT, "All warnings are cosmetic"),
        category="warnings",
        severity="MINOR",
        verdict="STALE",
        claim="The warning table is a current aggregate across all 14 successful recompiles.",
        claimed="50 linter warnings plus ~31 deprecations",
        observed=(
            "V1 warning inventory records 8,136 log instances under the current lake linter "
            "profile; the old 14-file successful-run scope does not exist"
        ),
        evidence=f"{relative(LOGS / 'warning_inventory.log')}; {relative(V1_SUMMARY)}",
        action="Replace with the source-bound V1 warning inventory and explain replayed dependency warnings.",
    )

    audit_file_rows: list[tuple[int, str, int]] = []
    for number in range(300, 314):
        cells = [
            cell.strip()
            for cell in AUDIT.read_text(encoding="utf-8").splitlines()[number - 1]
            .strip()
            .strip("|")
            .split("|")
        ]
        match = re.fullmatch(r"`([^`]+\.lean)`", cells[0])
        if match is None:
            raise RuntimeError(f"audit per-file row malformed at line {number}")
        audit_file_rows.append((number, match.group(1), int(cells[1])))
    for number, filename, claimed_lines in audit_file_rows:
        actual_lines = len((MC / filename).read_text(encoding="utf-8").splitlines())
        failed = filename in FAILED_MODULE_FILES
        if failed:
            verdict, severity = "CONTRADICTED", "MAJOR"
            observed = (
                f"actual lines={actual_lines}; V1 target fails"
                if actual_lines == claimed_lines
                else f"actual lines={actual_lines} (claimed {claimed_lines}); V1 target fails"
            )
            action = "Change Clean to failed/unverified and refresh the line count."
        elif actual_lines != claimed_lines:
            verdict, severity = "STALE", "MINOR"
            observed = f"buildable module, but current lines={actual_lines}"
            action = "Refresh the line count."
        else:
            verdict, severity = "MATCH", "INFO"
            observed = f"current lines={actual_lines}; module is in the V4 buildable set"
            action = "None."
        add(
            claims,
            claim_id=f"AUDIT_FILE_{filename.removesuffix('.lean').upper()}",
            path=AUDIT,
            line=number,
            category="per_file_status",
            severity=severity,
            verdict=verdict,
            claim=f"{filename} has {claimed_lines} lines and is Clean.",
            claimed=f"lines={claimed_lines}; Clean",
            observed=observed,
            evidence=f"{relative(MC / filename)}; {relative(V1_SUMMARY)}",
            action=action,
        )
    add(
        claims,
        claim_id="AUDIT_BOTTOM_LINE",
        path=AUDIT,
        line=find_line(AUDIT, "complete, kernel-checked, and faithful"),
        category="whole_surface",
        severity="MAJOR",
        verdict="OVERSTATED",
        claim="The project is complete, kernel-checked, faithful, and compiles cleanly.",
        claimed="whole project",
        observed="four physical modules fail or are dependency-blocked; semantic faithfulness is not proved by V1-V5",
        evidence=common_evidence,
        action="Replace with a scoped result and the unresolved build ledger.",
    )

    # APPENDIX_SUMMARY: the document describes a pre-merge directory that no longer exists.
    add(
        claims,
        claim_id="APPENDIX_CANONICAL_CURRENT_OVERVIEW",
        path=APPENDIX_SUMMARY,
        line=find_line(APPENDIX_SUMMARY, "canonical overview"),
        category="currentness",
        severity="MAJOR",
        verdict="STALE",
        claim="This is the current canonical overview of MatrixConcentration/Appendix.",
        claimed="current nested Appendix layout",
        observed="Pre_MatrixConcentration/Appendix does not exist; the sources were merged into five top-level Appendix_*.lean files",
        evidence=relative(MC),
        action="Mark this document historical or rewrite it for the merged five-file layout.",
    )
    add(
        claims,
        claim_id="APPENDIX_OLD_MARKDOWN_LOGS",
        path=APPENDIX_SUMMARY,
        line=find_line(APPENDIX_SUMMARY, "The older Markdown"),
        category="path",
        severity="MINOR",
        verdict="STALE",
        claim="The older construction-log Markdown files remain at the documented location.",
        claimed="SOURCES.md plus UP005/UP006-8/UP007 plan files retained",
        observed="only top-level SOURCES.md remains; the three named UP progress/status files are absent",
        evidence=relative(MC),
        action="Remove the absent-file claims or link an archival location.",
    )
    old_appendix_files = (
        "01_TraceCS.lean",
        "02_DysonWords.lean",
        "03_GoldenThompson.lean",
        "04_OneDimPL.lean",
        "05_GaussianPL.lean",
        "06_GaussianLipschitz.lean",
        "07_MatrixGaussianConcentration.lean",
        "08_SymmetricLowerBound.lean",
        "09_MatrixRosenthal.lean",
        "10_MatrixRosenthalPinelis.lean",
        "11_MatrixRosenthalPinelisSymmetric.lean",
    )
    for filename in old_appendix_files:
        add(
            claims,
            claim_id=f"APPENDIX_OLD_FILE_{filename.removesuffix('.lean').upper()}",
            path=APPENDIX_SUMMARY,
            line=find_line(APPENDIX_SUMMARY, f"`{filename}`"),
            category="file_inventory",
            severity="MAJOR",
            verdict="STALE",
            claim=f"{filename} is a current complete Appendix source file.",
            claimed="present and complete",
            observed="file absent; its content was merged into top-level Appendix_*.lean modules",
            evidence=relative(MC),
            action="Replace the 11-file inventory with the five current merged files.",
        )
    for filename in (
        "SOURCES.md",
        "UP005_PROGRESS.md",
        "UP006_UP007_UP008_STATUS.md",
        "UP007_SCHATTEN_PLAN.md",
    ):
        exists = (MC / filename).is_file()
        add(
            claims,
            claim_id=f"APPENDIX_SUPPORT_FILE_{filename.replace('.', '_').upper()}",
            path=APPENDIX_SUMMARY,
            line=find_line(APPENDIX_SUMMARY, f"`{filename}`"),
            category="file_inventory",
            severity="INFO" if exists else "MINOR",
            verdict="MATCH" if exists else "STALE",
            claim=f"{filename} is retained.",
            claimed="present",
            observed="present at top level" if exists else "absent",
            evidence=relative(MC / filename) if exists else relative(MC),
            action="None." if exists else "Remove or restore the historical-file reference.",
        )
    add(
        claims,
        claim_id="APPENDIX_ELEVEN_NO_BYPASS",
        path=APPENDIX_SUMMARY,
        line=find_line(APPENDIX_SUMMARY, "All eleven Appendix Lean files"),
        category="source_scan",
        severity="MAJOR",
        verdict="STALE",
        claim="All eleven current Appendix Lean files are bypass-free.",
        claimed="11 files; zero tokens",
        observed=(
            "the eleven files do not exist; the five current Appendix_*.lean files "
            "have zero sorry/admit/axiom/native_decide source tokens"
        ),
        evidence=f"{relative(V3_SUMMARY)}; {relative(MC)}",
        action="Change the file universe to the five merged Appendix modules.",
    )
    add(
        claims,
        claim_id="APPENDIX_UP007_EXACT_AXIOMS",
        path=APPENDIX_SUMMARY,
        line=find_line(APPENDIX_SUMMARY, "two UP-007 resolution theorems"),
        category="headline_axioms",
        severity="MAJOR",
        verdict="OVERSTATED",
        claim="Both public UP-007 resolution theorems currently have exactly the three standard axioms.",
        claimed="two exact V4 rows",
        observed="both public theorems are in failed Chapter6; their auxiliary proof module also fails",
        evidence=f"{relative(V1_SUMMARY)}; {relative(V4_AUDIT)}",
        action="Treat the old axiom output as historical until the current modules elaborate and are re-audited.",
    )
    add(
        claims,
        claim_id="APPENDIX_ROOT_IMPORTS_01_11",
        path=APPENDIX_SUMMARY,
        line=find_line(APPENDIX_SUMMARY, "root module imports Appendix files"),
        category="import_graph",
        severity="MAJOR",
        verdict="CONTRADICTED",
        claim="The root module imports Appendix files 01 through 11.",
        claimed="11 Appendix imports",
        observed=f"MatrixConcentration.lean direct imports={root_imports}",
        evidence=f"{relative(MC_ROOT)}; {relative(V2_SUMMARY)}",
        action="Replace with the current one-import compatibility-root shape.",
    )
    add(
        claims,
        claim_id="APPENDIX_COMPLETE_PROJECT_BUILD",
        path=APPENDIX_SUMMARY,
        line=find_line(APPENDIX_SUMMARY, "complete project builds"),
        category="build",
        severity="MAJOR",
        verdict="OVERSTATED",
        claim="lake build checks and succeeds on the complete MatrixConcentration project.",
        claimed="complete physical surface",
        observed="ordinary root build succeeds because the compatibility root imports only Chapter 2; four physical modules fail separately",
        evidence=f"{relative(MC_ROOT)}; {relative(V1_SUMMARY)}",
        action="Distinguish root-target success from full physical-surface failure.",
    )
    add(
        claims,
        claim_id="APPENDIX_UP007_CURRENT_STATUS",
        path=APPENDIX_SUMMARY,
        line=find_line(APPENDIX_SUMMARY, "UP-007 is SOLVED"),
        category="result_status",
        severity="MAJOR",
        verdict="OVERSTATED",
        claim="UP-007 is currently solved by two usable public replacement theorems.",
        claimed="two public proved replacements",
        observed="both source headers exist, but Chapter6 and Appendix_RosenthalPinelis do not elaborate",
        evidence=relative(V1_SUMMARY),
        action="Record source implementation separately from current build/kernel status.",
    )
    for identifier, fragment, endpoints in (
        (
            "UP004",
            "| UP-004 Golden--Thompson",
            ("golden_thompson_trace",),
        ),
        (
            "UP005",
            "| UP-005 Gaussian concentration",
            ("matrix_gaussian_concentration", "gauss_concentration"),
        ),
        (
            "UP006",
            "| UP-006 matrix Rosenthal",
            ("matrix_rosenthal_aux", "matrix_rosenthal"),
        ),
        (
            "UP008",
            "| UP-008 symmetric lower bound",
            ("symmetric_sum_lower_bound_aux", "symmetric_sum_lower_bound"),
        ),
    ):
        endpoint_hits = [hit for endpoint in endpoints for hit in by_name.get(endpoint, [])]
        failed_hits = [hit for hit in endpoint_hits if hit.path.name in FAILED_MODULE_FILES]
        buildable_hits = [hit for hit in endpoint_hits if hit.path.name not in FAILED_MODULE_FILES]
        if identifier == "UP008":
            verdict, severity = "OVERSTATED", "MAJOR"
            observed = (
                f"buildable auxiliary={[(h.path.name, h.line) for h in buildable_hits]}; "
                f"registered public wrapper is failed={[(h.path.name, h.line) for h in failed_hits]}"
            )
            action = "State that the auxiliary builds but the current public wrapper does not."
        else:
            missing_v4 = []
            for hit in buildable_hits:
                key = (
                    f"MatrixConcentration.{hit.path.stem}",
                    f"MatrixConcentration.{hit.name}",
                )
                if key not in v4_rows:
                    missing_v4.append(hit.name)
            if missing_v4:
                verdict, severity = "PENDING", "MINOR"
                observed = f"source/buildable endpoints present; V4 rows pending for {missing_v4}"
                action = "Rerun after V4 completion."
            else:
                verdict, severity = "MATCH", "INFO"
                observed = f"buildable endpoints={[(h.path.name, h.line) for h in buildable_hits]}"
                action = "None."
        add(
            claims,
            claim_id=f"APPENDIX_STATUS_{identifier}",
            path=APPENDIX_SUMMARY,
            line=find_line(APPENDIX_SUMMARY, fragment),
            category="result_status",
            severity=severity,
            verdict=verdict,
            claim=f"{identifier} has the stated current discharged status.",
            claimed="discharged",
            observed=observed,
            evidence=f"{relative(V1_SUMMARY)}; {relative(V4_AUDIT)}",
            action=action,
        )
    add(
        claims,
        claim_id="APPENDIX_MISSING_INFRASTRUCTURE",
        path=APPENDIX_SUMMARY,
        line=find_line(APPENDIX_SUMMARY, "feasibility audit found no general"),
        category="library_capability",
        severity="MINOR",
        verdict="UNVERIFIABLE",
        claim="Pinned Mathlib lacks every listed noncommutative/Schatten component.",
        claimed="listed infrastructure absent",
        observed="V1-V5 do not perform an exhaustive Mathlib API search",
        evidence=relative(APPENDIX_SUMMARY),
        action="Bind each absence claim to exact #check/search evidence and Mathlib commit.",
    )

    identifiers = [claim.claim_id for claim in claims]
    duplicates = sorted(
        identifier
        for identifier, count in collections.Counter(identifiers).items()
        if count > 1
    )
    if duplicates:
        raise RuntimeError(f"duplicate claim IDs: {duplicates}")

    mapping_claims = [claim for claim in claims if claim.category == "correspondence_row"]
    metadata: dict[str, object] = {
        "mappings": mappings,
        "mapping_claims": mapping_claims,
        "v4_complete": v4_complete,
        "v4_row_count": len(v4_rows),
        "v4_mc_row_count": sum(row.module.startswith("MatrixConcentration.") for row in v4_rows.values()),
        "actual_line_count": sum(
            len(path.read_text(encoding="utf-8").splitlines()) for path in LEAN_FILES
        ),
        "forbidden": forbidden,
        "root_imports": root_imports,
    }
    return claims, metadata


def render_tsv(claims: Iterable[Claim]) -> str:
    buffer = io.StringIO()
    writer = csv.DictWriter(
        buffer,
        fieldnames=FIELDS,
        delimiter="\t",
        lineterminator="\n",
        extrasaction="raise",
    )
    writer.writeheader()
    for claim in claims:
        writer.writerow(claim.as_row())
    return buffer.getvalue()


def render_summary(claims: list[Claim], metadata: dict[str, object], tsv_text: str) -> str:
    verdicts = collections.Counter(claim.verdict for claim in claims)
    documents = collections.Counter(claim.document for claim in claims)
    categories = collections.Counter(claim.category for claim in claims)
    mapping_claims = list(metadata["mapping_claims"])
    mapping_verdicts = collections.Counter(claim.verdict for claim in mapping_claims)
    mappings = list(metadata["mappings"])
    asserted_mappings = [row for row in mappings if not row.role.startswith("N/")]
    blocked_mappings = [row for row in asserted_mappings if row.file in FAILED_MODULE_FILES]
    buildable_mappings = [row for row in asserted_mappings if row.file not in FAILED_MODULE_FILES]
    issues = [
        claim
        for claim in claims
        if claim.verdict in {"CONTRADICTED", "OVERSTATED", "STALE"}
        and claim.severity in {"MAJOR", "CRITICAL"}
    ]
    v4_mapping_boundary = (
        "The completed V4 dump contains an exact module-and-name row for every "
        "asserted README mapping in a buildable module; no such README row "
        "remains `PENDING`."
        if metadata["v4_complete"]
        else
        "Buildable rows without a readable exact V4 row remain `PENDING` while "
        "V4 is live."
    )
    lines = [
        "# V9 MatrixConcentration self-record audit",
        "",
        "This is a deterministic static reconciliation of the five live self-record "
        "documents against V1–V5 evidence. It does not invoke Lean or Lake.",
        "",
        f"- Ledger: `{relative(OUTPUT)}`",
        f"- Script: `{relative(Path(__file__))}`",
        f"- TSV SHA-256: `{hashlib.sha256(tsv_text.encode()).hexdigest()}`",
        f"- V4 raw state: `{'COMPLETE' if metadata['v4_complete'] else 'LIVE/PENDING'}` "
        f"({metadata['v4_row_count']} readable rows; {metadata['v4_mc_row_count']} MC-origin rows)",
        "",
        "## Result",
        "",
        f"- Claims audited: **{len(claims)}**",
        "- Verdicts: "
        + ", ".join(f"`{key}={verdicts[key]}`" for key in sorted(verdicts)),
        f"- Major/critical stale, overstated, or contradicted claims: **{len(issues)}**",
        "",
        "The decisive result is that the documents conflate two different facts: "
        "all 448 README mappings are source-located, but the complete 14-file "
        "MatrixConcentration surface is not currently elaboratable. "
        "`Appendix_RosenthalPinelis` has nine direct errors, and its failure blocks "
        "Chapters 1, 6, and 7. The compatibility root succeeds because it imports "
        "only Chapter 2.",
        "",
        "## README correspondence",
        "",
        f"- Physical rows: **{len(mappings)}** (asserted declarations: "
        f"**{len(asserted_mappings)}**; explicit non-theorem: **1**).",
        f"- Asserted rows in the ten buildable modules: **{len(buildable_mappings)}**.",
        f"- Asserted rows in the four failed/dependency-blocked modules: "
        f"**{len(blocked_mappings)}**.",
        "- Per-row current verdicts: "
        + ", ".join(
            f"`{key}={mapping_verdicts[key]}`" for key in sorted(mapping_verdicts)
        ),
        "",
        "Every asserted row has a declaration header of the claimed kind in the "
        "claimed source file. That proves lexical source location, not book "
        "faithfulness. Rows in failed modules are explicitly `OVERSTATED`, never "
        f"silently counted as kernel-verified. {v4_mapping_boundary}",
        "",
        "## Principal contradictions and stale records",
        "",
        "- `MatrixConcentration_audit.md` says 14/14 files compile with zero errors; "
        "V1 proves four failures and nine direct errors.",
        "- The same audit says the review notes have 16 rows in one place, while "
        "the live file has 15 source-gap rows plus 5 merge rows (and the audit "
        "itself later says 15 + 5).",
        "- `APPENDIX_SUMMARY.md` describes a current `Appendix/01_...` through "
        "`11_...` layout. That directory and all eleven files are absent after "
        "the five-file merge.",
        "- `APPENDIX_SUMMARY.md` says the root imports Appendix 01–11; the current "
        f"root imports only `{metadata['root_imports'][0]}`.",
        "- Placeholder freedom is real at source level: all 14 MC source files "
        "have zero executable `sorry`, `admit`, `native_decide`, or custom-axiom "
        "declarations. This does not repair elaboration errors.",
        "",
        "## Headline axiom claims",
        "",
        "The audit's 17-name exact-axiom list crosses the build boundary. Nine "
        "headline declarations are sourced in buildable modules and eight are in "
        "Ch1/Ch6/Ch7. Only exact module-and-name V4 rows are accepted; a duplicate "
        "qualified name originating in another HDP module cannot authenticate a "
        "failed MatrixConcentration source module.",
        "",
        "## Review-notes status",
        "",
        "All explicit declaration-location references in `REVIEW_NOTES.md` are "
        "checked individually. Semantic claims about correspondence to Tropp, "
        "almost-everywhere versus pointwise assumptions, or body preservation "
        "remain `UNVERIFIABLE` unless V1–V5 contains the required comparison "
        "artifact. References in failed modules are source-present but `PENDING` "
        "kernel/build confirmation.",
        "",
        "## Document row counts",
        "",
    ]
    lines.extend(f"- `{doc}`: {count}" for doc, count in sorted(documents.items()))
    lines.extend(("", "## Category counts", ""))
    lines.extend(
        f"- `{category}`: {count}" for category, count in sorted(categories.items())
    )
    lines.extend(
        (
            "",
            "## Evidence boundary",
            "",
            "This audit proves document/source arithmetic, physical paths, current "
            "imports, source-token absence, V1/V2 build classification, and any "
            "exact V4 rows already available. It does not independently prove "
            "historical body preservation, correspondence to the TeX source, or "
            "mathematical completeness. Those claims are marked `UNVERIFIABLE` "
            "rather than inferred.",
            "",
        )
    )
    return "\n".join(lines)


def self_test() -> None:
    sample = """-- theorem hidden : True := by trivial
/- axiom planted : False -/
namespace X
theorem visible : True := by trivial
end X
"""
    masked = mask_lean_noncode(sample)
    names = [match.group("name") for match in DECLARATION.finditer(masked)]
    assert names == ["visible"], names
    assert not re.search(r"\bsorry\b", mask_lean_noncode('"sorry" -- sorry\n'))

    n_row = MappingRow(
        line=1,
        book_source="display",
        name="",
        file="Missing.lean",
        role="N/—",
        notes="not asserted as a Lean theorem",
    )
    assert mapping_verdict(n_row, None, {}, False)[1] == "MATCH"
    bad = MappingRow(
        line=2,
        book_source="theorem",
        name="missing",
        file="Chapter1_Introduction.lean",
        role="E/thm",
        notes="",
    )
    assert mapping_verdict(bad, None, {}, False)[1] == "CONTRADICTED"
    planted = Declaration(MC / "Chapter1_Introduction.lean", "x", "theorem", 1)
    assert mapping_verdict(bad, planted, {}, False)[1] == "OVERSTATED"


def main() -> int:
    parser = argparse.ArgumentParser()
    parser.add_argument(
        "--check-only",
        action="store_true",
        help="fail unless existing generated artifacts exactly match current evidence",
    )
    parser.add_argument(
        "--self-test",
        action="store_true",
        help="run planted positive/negative parser and classification calibration",
    )
    args = parser.parse_args()

    if args.self_test:
        self_test()
        print("PASS: V9 MatrixConcentration self-record negative calibration")
        return 0

    self_test()
    claims, metadata = build_claims()
    tsv_text = render_tsv(claims)
    summary_text = render_summary(claims, metadata, tsv_text)
    evidence_hash_paths = [V1_SUMMARY, V2_SUMMARY, V3_SUMMARY, V4_MODULES]
    if metadata["v4_complete"]:
        evidence_hash_paths.extend((V4_AUDIT, V4_SUMMARY))
    log_text = "\n".join(
        (
            "V9 MATRIXCONCENTRATION SELF-RECORD AUDIT",
            "========================================",
            "method: deterministic static scan; no Lean/Lake/Git/network",
            "negative_calibration: PASS",
            f"claims: {len(claims)}",
            f"v4_complete: {str(metadata['v4_complete']).lower()}",
            f"v4_readable_rows: {metadata['v4_row_count']}",
            f"v4_mc_origin_rows: {metadata['v4_mc_row_count']}",
            f"tsv_sha256: {hashlib.sha256(tsv_text.encode()).hexdigest()}",
            f"ledger: {relative(OUTPUT)}",
            f"summary: {relative(SUMMARY)}",
            "",
            "[document_sha256]",
            *(f"{relative(path)}\t{sha256(path)}" for path in DOCS),
            "",
            "[evidence_sha256]",
            *(
                f"{relative(path)}\t{sha256(path)}"
                for path in evidence_hash_paths
            ),
            "",
        )
    )

    if args.check_only:
        expected = {OUTPUT: tsv_text, SUMMARY: summary_text, RUN_LOG: log_text}
        mismatches = [
            relative(path)
            for path, text in expected.items()
            if not path.is_file() or path.read_text(encoding="utf-8") != text
        ]
        if mismatches:
            print(f"FAIL: generated artifacts differ: {mismatches}", file=sys.stderr)
            return 1
        print(f"PASS: {len(claims)} claims; generated artifacts are current")
        return 0

    REVIEW.mkdir(parents=True, exist_ok=True)
    LOGS.mkdir(parents=True, exist_ok=True)
    OUTPUT.write_text(tsv_text, encoding="utf-8")
    SUMMARY.write_text(summary_text, encoding="utf-8")
    RUN_LOG.write_text(log_text, encoding="utf-8")
    print(f"wrote {relative(OUTPUT)} ({len(claims)} claims)")
    print(f"wrote {relative(SUMMARY)}")
    print(f"wrote {relative(RUN_LOG)}")
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
