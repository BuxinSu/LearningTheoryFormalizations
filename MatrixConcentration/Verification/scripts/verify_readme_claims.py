#!/usr/bin/env python3
"""Reproduce the source README's machine-checkable counts and endpoint claims."""

from __future__ import annotations

import argparse
import csv
import html
import json
import re
import sys
from collections import Counter
from pathlib import Path

from lean_source_scan import lean_universe
from v6_scan_vacuity import extract as extract_theorems, mask_noncode


SCRIPT = Path(__file__).resolve()
VERIFY = SCRIPT.parent.parent
ROOT = VERIFY.parent.parent
SOURCE = ROOT / "MatrixConcentration"
README = SOURCE / "README.md"
APPENDIX = SOURCE / "APPENDIX_SUMMARY.md"
LOGS = VERIFY / "logs"
WORK = ROOT / ".audit_work"
EXPECTED_CHAPTERS = {1: 21, 2: 136, 3: 35, 4: 55, 5: 71, 6: 62, 7: 63, 8: 24}
STANDARD_AXIOMS = {"propext", "Classical.choice", "Quot.sound"}
FAKE_NAME = "verificationDefinitelyMissingEndpoint"


def plain_cell(cell: str) -> str:
    cell = html.unescape(cell.strip())
    cell = re.sub(r"\[([^\]]+)\]\([^)]+\)", r"\1", cell)
    cell = cell.replace("<br>", " ").replace("<br/>", " ").replace("`", "")
    return re.sub(r"\s+", " ", cell).strip()


def correspondence_rows(readme: Path) -> list[dict[str, object]]:
    text = readme.read_text(encoding="utf-8")
    active = False
    chapter: int | None = None
    chapter_row = 0
    rows: list[dict[str, object]] = []
    for line_number, line in enumerate(text.splitlines(), 1):
        if line == "## Book → Lean correspondence":
            active = True
            continue
        if active and line.startswith("## ") and not line.startswith("### "):
            break
        match = re.fullmatch(r"### Chapter ([1-8])", line)
        if active and match:
            chapter = int(match.group(1))
            chapter_row = 0
            continue
        if not active or chapter is None or not line.startswith("|"):
            continue
        cells = [part.strip() for part in line.strip().strip("|").split("|")]
        if len(cells) != 5:
            raise RuntimeError(f"{readme}:{line_number}: expected five table cells")
        if cells[0] == "Book source" or all(set(cell) <= {":", "-"} for cell in cells):
            continue
        chapter_row += 1
        role = plain_cell(cells[3])
        rows.append(
            {
                "global_row": len(rows) + 1,
                "chapter": chapter,
                "chapter_row": chapter_row,
                "readme_line": line_number,
                "declaration": plain_cell(cells[1]),
                "final_module": plain_cell(cells[2]),
                "role": role,
                "role_kind": role.rsplit("/", 1)[-1],
            }
        )
    return rows


def source_counts() -> Counter[str]:
    counts: Counter[str] = Counter()
    for path in lean_universe():
        for statement in extract_theorems(path):
            if not statement.is_private:
                counts[statement.keyword] += 1
        text = path.read_text(encoding="utf-8")
        masked = mask_noncode(text)
        pattern = re.compile(
            r"(?m)^[ \t]*(?:@\[[^\n]*\]\s*)*"
            r"(?:(?:private|protected|noncomputable)\s+)*"
            r"def\s+(?P<name>[^\s({:\[]+)"
        )
        for match in pattern.finditer(masked):
            prefix = masked[match.start() : match.end("name")]
            if not re.search(r"\bprivate\b", prefix):
                counts["def"] += 1
    return counts


def source_declaration_index() -> dict[str, dict[str, str]]:
    """Index public source declarations by the README's short-name convention."""

    index: dict[str, dict[str, str]] = {}

    def add(name: str, final_module: str, role_kind: str) -> None:
        if name in index:
            raise RuntimeError(f"duplicate public source declaration short name: {name}")
        index[name] = {
            "final_module": final_module,
            "role_kind": role_kind,
        }

    definition = re.compile(
        r"(?m)^[ \t]*(?:@\[[^\n]*\]\s*)*"
        r"(?:(?:private|protected|noncomputable)\s+)*"
        r"(?P<keyword>def|abbrev)\s+(?P<name>[^\s({:\[]+)"
    )
    for path in lean_universe():
        for statement in extract_theorems(path):
            if not statement.is_private:
                add(
                    statement.name,
                    path.name,
                    "thm" if statement.keyword == "theorem" else "lem",
                )
        masked = mask_noncode(path.read_text(encoding="utf-8"))
        for match in definition.finditer(masked):
            prefix = masked[match.start() : match.start("keyword")]
            if re.search(r"\bprivate\b", prefix):
                continue
            add(
                match.group("name"),
                path.name,
                "def" if match.group("keyword") == "def" else "abbr",
            )
    return index


def parse_tsv(path: Path) -> list[dict[str, str]]:
    with path.open(encoding="utf-8", newline="") as handle:
        return list(csv.DictReader(handle, delimiter="\t"))


def write_tsv(path: Path, fields: list[str], rows: list[dict[str, object]]) -> None:
    with path.open("w", encoding="utf-8", newline="") as handle:
        writer = csv.DictWriter(handle, fieldnames=fields, delimiter="\t", lineterminator="\n")
        writer.writeheader()
        writer.writerows(rows)


def endpoint_reconciliation(
    rows: list[dict[str, object]], *, write_outputs: bool
) -> tuple[list[str], list[dict[str, object]]]:
    telescope = {
        (int(row["chapter"]), int(row["chapter_row"])): row
        for row in parse_tsv(LOGS / "v6_endpoint_telescopes.tsv")
    }
    axiom_rows = parse_tsv(LOGS / "axiom_audit.tsv")
    axiom_by_name: dict[str, set[str]] = {}
    for row in axiom_rows:
        axioms = {item for item in row["axioms"].split(",") if item}
        axiom_by_name[row["name"]] = axioms
        axiom_by_name[row["user_name"]] = axioms
    source_declarations = source_declaration_index()

    problems: list[str] = []
    output: list[dict[str, object]] = []
    for source_row in rows:
        key = (int(source_row["chapter"]), int(source_row["chapter_row"]))
        endpoint = telescope.get(key)
        if endpoint is None or endpoint["readme_name"] != source_row["declaration"]:
            problems.append(
                f"unresolved row {source_row['global_row']}: "
                f"{source_row['declaration']}"
            )
            output.append(
                {
                    **source_row,
                    "resolved_name": "",
                    "kind": "",
                    "measured_final_module": "",
                    "measured_role_kind": "",
                    "module_result": "UNRESOLVED",
                    "role_result": "UNRESOLVED",
                    "collector_axioms": "",
                    "v4_axioms": "",
                    "result": "UNRESOLVED",
                }
            )
            continue
        collector_axioms = {item for item in endpoint["axioms"].split(",") if item}
        v4_axioms = axiom_by_name.get(endpoint["resolved_name"])
        source_declaration = source_declarations.get(
            str(source_row["declaration"])
        )
        result = "PASS"
        module_result = "PASS"
        role_result = "PASS"
        measured_final_module = ""
        measured_role_kind = ""
        if source_declaration is None:
            problems.append(
                f"row {source_row['global_row']} missing from public source "
                f"declaration index: {source_row['declaration']}"
            )
            module_result = "FAIL"
            role_result = "FAIL"
            result = "FAIL"
        else:
            measured_final_module = source_declaration["final_module"]
            measured_role_kind = source_declaration["role_kind"]
            if source_row["final_module"] != measured_final_module:
                problems.append(
                    f"row {source_row['global_row']} final-module mismatch: "
                    f"published={source_row['final_module']}, "
                    f"measured={measured_final_module}"
                )
                module_result = "FAIL"
                result = "FAIL"
            if source_row["role_kind"] != measured_role_kind:
                problems.append(
                    f"row {source_row['global_row']} role-kind mismatch: "
                    f"published={source_row['role_kind']}, "
                    f"measured={measured_role_kind}"
                )
                role_result = "FAIL"
                result = "FAIL"
            expected_environment_kind = (
                "theorem"
                if measured_role_kind in {"thm", "lem"}
                else "definition"
            )
            if endpoint["kind"] != expected_environment_kind:
                problems.append(
                    f"row {source_row['global_row']} environment/source-kind "
                    f"mismatch: environment={endpoint['kind']}, "
                    f"source={measured_role_kind}"
                )
                role_result = "FAIL"
                result = "FAIL"
        if collector_axioms != STANDARD_AXIOMS:
            problems.append(
                f"row {source_row['global_row']} collector axiom mismatch: "
                f"{sorted(collector_axioms)}"
            )
            result = "FAIL"
        if v4_axioms != STANDARD_AXIOMS:
            problems.append(
                f"row {source_row['global_row']} V4 axiom mismatch or missing: "
                f"{endpoint['resolved_name']}"
            )
            result = "FAIL"
        output.append(
            {
                **source_row,
                "resolved_name": endpoint["resolved_name"],
                "kind": endpoint["kind"],
                "measured_final_module": measured_final_module,
                "measured_role_kind": measured_role_kind,
                "module_result": module_result,
                "role_result": role_result,
                "collector_axioms": ",".join(sorted(collector_axioms)),
                "v4_axioms": "" if v4_axioms is None else ",".join(sorted(v4_axioms)),
                "result": result,
            }
        )
    if write_outputs:
        write_tsv(
            LOGS / "v9_readme_endpoints.tsv",
            [
                "global_row",
                "chapter",
                "chapter_row",
                "readme_line",
                "declaration",
                "final_module",
                "measured_final_module",
                "module_result",
                "role",
                "role_kind",
                "measured_role_kind",
                "role_result",
                "resolved_name",
                "kind",
                "collector_axioms",
                "v4_axioms",
                "result",
            ],
            output,
        )
    return problems, output


def module_checks(readme: Path) -> tuple[list[str], dict[str, object]]:
    text = readme.read_text(encoding="utf-8")
    layout = text.split("## Module layout", 1)[1].split("\n## ", 1)[0]
    linked = sorted(set(re.findall(r"\]\(([^)]+\.lean)\)", layout)))
    physical = sorted(path.name for path in SOURCE.glob("*.lean"))
    root_text = (ROOT / "MatrixConcentration.lean").read_text(encoding="utf-8")
    imports = sorted(
        match.group(1) + ".lean"
        for match in re.finditer(r"(?m)^import MatrixConcentration\.([A-Za-z0-9_]+)$", root_text)
    )
    problems: list[str] = []
    if linked != physical:
        problems.append("module-layout links differ from physical 14-module set")
    if imports != physical:
        problems.append("root imports differ from physical 14-module set")
    return problems, {"linked": linked, "physical": physical, "imports": imports}


def version_checks(readme: Path) -> tuple[list[str], dict[str, str]]:
    text = readme.read_text(encoding="utf-8")
    toolchain = (ROOT / "lean-toolchain").read_text(encoding="utf-8").strip()
    manifest = json.loads((ROOT / "lake-manifest.json").read_text(encoding="utf-8"))
    mathlib = next(package for package in manifest["packages"] if package["name"] == "mathlib")
    revision = mathlib.get("inputRev", "")
    problems: list[str] = []
    if toolchain != "leanprover/lean4:v4.31.0":
        problems.append(f"unexpected toolchain pin {toolchain}")
    if revision != "v4.31.0":
        problems.append(f"unexpected Mathlib inputRev {revision}")
    if toolchain not in text or "Mathlib `v4.31.0`" not in text:
        problems.append("README version claim does not match pins")
    return problems, {"toolchain": toolchain, "mathlib_inputRev": revision}


def ledger_checks() -> tuple[list[str], list[dict[str, object]]]:
    claims = [
        ("UP-001", "matrix_bernstein_tail"),
        ("UP-002", "matrix_bernstein_expectation"),
        ("UP-003", "lieb_trace_exp_log_concave"),
        ("UP-004", "golden_thompson_trace"),
        ("UP-005", "gauss_concentration"),
        ("UP-006", "matrix_rosenthal"),
        ("SUPPORT-007a", "matrix_rosenthal_pinelis_symmetric"),
        ("SUPPORT-007b", "matrix_rosenthal_pinelis_centered_with_loss"),
        ("UP-008", "symmetric_sum_lower_bound"),
    ]
    axiom_rows = parse_tsv(LOGS / "axiom_audit.tsv")
    by_short: dict[str, list[dict[str, str]]] = {}
    for row in axiom_rows:
        by_short.setdefault(row["user_name"].split(".")[-1], []).append(row)
    problems: list[str] = []
    output: list[dict[str, object]] = []
    for item, name in claims:
        candidates = by_short.get(name, [])
        exact = [
            row
            for row in candidates
            if {part for part in row["axioms"].split(",") if part} == STANDARD_AXIOMS
        ]
        result = "PASS" if len(exact) == 1 else "FAIL"
        if result == "FAIL":
            problems.append(f"{item} does not map uniquely to an exact-three-axiom declaration")
        output.append(
            {
                "item": item,
                "declaration": name,
                "resolved_name": exact[0]["user_name"] if len(exact) == 1 else "",
                "axioms": exact[0]["axioms"] if len(exact) == 1 else "",
                "result": result,
            }
        )
    appendix_text = APPENDIX.read_text(encoding="utf-8")
    for phrase in [
        "| UP-004 Golden--Thompson | **discharged** |",
        "| UP-005 Gaussian concentration | **discharged** |",
        "| UP-006 matrix Rosenthal | **discharged** |",
        "| UP-007 / Book display (6.1.6) | **explicit formal-coverage exception; not covered** |",
        "| Related symmetric and centered-with-loss variants | **supporting results retained; not correspondence endpoints** |",
        "| UP-008 symmetric lower bound | **discharged** |",
    ]:
        if phrase not in appendix_text:
            problems.append(f"Appendix status phrase missing: {phrase}")
    write_tsv(
        LOGS / "v9_ledger_endpoints.tsv",
        ["item", "declaration", "resolved_name", "axioms", "result"],
        output,
    )
    return problems, output


def make_calibration_copy() -> None:
    WORK.mkdir(parents=True, exist_ok=True)
    text = README.read_text(encoding="utf-8")
    marker = "\n## Coverage scope"
    fake = (
        f"| V9 calibration | `{FAKE_NAME}` | "
        "[`Chapter8_ProofOfLiebsTheorem.lean`](Chapter8_ProofOfLiebsTheorem.lean) "
        "| `S/thm` | planted fake name |"
    )
    if marker not in text:
        raise RuntimeError("README coverage marker not found")
    (WORK / "README_fake_name.md").write_text(
        text.replace(marker, f"\n{fake}\n{marker}", 1), encoding="utf-8"
    )


def run(readme: Path, *, production: bool) -> tuple[int, str]:
    rows = correspondence_rows(readme)
    problems: list[str] = []
    measured_chapters = Counter(int(row["chapter"]) for row in rows)
    for chapter, expected in EXPECTED_CHAPTERS.items():
        if measured_chapters[chapter] != expected:
            problems.append(
                f"chapter {chapter} rows: expected {expected}, measured "
                f"{measured_chapters[chapter]}"
            )
    if len(rows) != 467:
        problems.append(f"correspondence rows: expected 467, measured {len(rows)}")

    endpoint_problems, endpoint_rows = endpoint_reconciliation(
        rows, write_outputs=production
    )
    problems.extend(endpoint_problems)

    counts = source_counts()
    if counts != Counter({"theorem": 467, "lemma": 841, "def": 135}):
        problems.append(f"public source counts differ: {dict(counts)}")
    if production:
        write_tsv(
            LOGS / "v9_public_source_counts.tsv",
            ["kind", "measured", "published", "result"],
            [
                {
                    "kind": kind,
                    "measured": counts[kind],
                    "published": expected,
                    "result": "PASS" if counts[kind] == expected else "FAIL",
                }
                for kind, expected in [("theorem", 467), ("lemma", 841), ("def", 135)]
            ]
            + [
                {
                    "kind": "total",
                    "measured": sum(counts.values()),
                    "published": 1443,
                    "result": "PASS" if sum(counts.values()) == 1443 else "FAIL",
                }
            ],
        )
        module_problems, modules = module_checks(readme)
        version_problems, versions = version_checks(readme)
        ledger_problems, ledger = ledger_checks()
        problems.extend(module_problems + version_problems + ledger_problems)
    else:
        modules = {}
        versions = {}
        ledger = []

    theorem_endpoints = sum(row.get("kind") == "theorem" for row in endpoint_rows)
    definition_endpoints = sum(row.get("kind") == "definition" for row in endpoint_rows)
    module_matches = sum(
        row.get("module_result") == "PASS" for row in endpoint_rows
    )
    role_matches = sum(
        row.get("role_result") == "PASS" for row in endpoint_rows
    )
    summary = "\n".join(
        [
            "V9 README CLAIMS CHECK",
            f"readme={readme}",
            f"correspondence_rows={len(rows)}",
            *(
                f"chapter_{chapter}_rows={measured_chapters[chapter]}"
                for chapter in sorted(EXPECTED_CHAPTERS)
            ),
            f"resolved_exact_three_axioms={sum(row.get('result') == 'PASS' for row in endpoint_rows)}",
            f"final_module_matches={module_matches}",
            f"role_kind_matches={role_matches}",
            f"theorem_lemma_endpoints={theorem_endpoints}",
            f"definition_endpoints={definition_endpoints}",
            f"public_theorem={counts['theorem']}",
            f"public_lemma={counts['lemma']}",
            f"public_def={counts['def']}",
            f"public_total={sum(counts.values())}",
            *(
                [
                    f"module_links={len(modules['linked'])}",
                    f"physical_inner_modules={len(modules['physical'])}",
                    f"root_imports={len(modules['imports'])}",
                    f"toolchain={versions['toolchain']}",
                    f"mathlib_inputRev={versions['mathlib_inputRev']}",
                    f"ledger_endpoints={len(ledger)}",
                ]
                if production
                else []
            ),
            f"problems={len(problems)}",
            *(f"PROBLEM {problem}" for problem in problems),
            f"result={'PASS' if not problems else 'FAIL'}",
            "",
        ]
    )
    if production:
        (LOGS / "v9_readme_claims_summary.txt").write_text(summary, encoding="utf-8")
    return (0 if not problems else 1), summary


def main() -> int:
    parser = argparse.ArgumentParser()
    parser.add_argument("--readme", type=Path, default=README)
    parser.add_argument("--make-calibration-copy", action="store_true")
    parser.add_argument("--production", action="store_true")
    args = parser.parse_args()
    if args.make_calibration_copy:
        make_calibration_copy()
        print(WORK / "README_fake_name.md")
        return 0
    status, summary = run(args.readme.resolve(), production=args.production)
    print(summary, end="")
    return status


if __name__ == "__main__":
    sys.exit(main())
