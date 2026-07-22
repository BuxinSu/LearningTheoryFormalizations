#!/usr/bin/env python3
"""Calibrated syntactic vacuity/triviality triage for every theorem statement.

This is intentionally a red-flag scanner, not a semantic decision procedure.
Every source-level ``theorem`` and ``lemma`` in the fixed FILE-WALK UNIVERSE is
recorded, including statements with no hit.  The same detector is first run on
``.audit_work/VacuityPlant.lean`` and must recognize each required plant class.
"""

from __future__ import annotations

from dataclasses import dataclass
import csv
import json
import re
from pathlib import Path
from typing import Iterable

from lean_source_scan import ROOT, LOGS, lean_universe, lexical_contexts, relative, tsv_safe


PLANT = ROOT / ".audit_work" / "VacuityPlant.lean"


@dataclass
class Statement:
    path: Path
    line: int
    keyword: str
    name: str
    is_private: bool
    header: str
    conclusion: str


def mask_noncode(text: str) -> str:
    contexts = lexical_contexts(text)
    chars = list(text)
    for index, context in enumerate(contexts):
        if context and chars[index] != "\n":
            chars[index] = " "
    return "".join(chars)


def find_assignment(masked: str, start: int) -> int | None:
    """Find the declaration's top-level ``:=``, respecting binder nesting."""

    opening = {"(": ")", "[": "]", "{": "}"}
    closing = set(opening.values())
    stack: list[str] = []
    index = start
    while index + 1 < len(masked):
        char = masked[index]
        if char in opening:
            stack.append(opening[char])
        elif char in closing:
            if stack and char == stack[-1]:
                stack.pop()
        elif char == ":" and masked[index + 1] == "=" and not stack:
            return index
        index += 1
    return None


def main_colon(header: str, name_end: int) -> int | None:
    opening = {"(": ")", "[": "]", "{": "}"}
    closing = set(opening.values())
    stack: list[str] = []
    for index in range(name_end, len(header)):
        char = header[index]
        if char in opening:
            stack.append(opening[char])
        elif char in closing:
            if stack and char == stack[-1]:
                stack.pop()
        elif char == ":" and not stack:
            return index
    return None


def extract(path: Path) -> list[Statement]:
    text = path.read_text(encoding="utf-8")
    masked = mask_noncode(text)
    declaration = re.compile(
        r"(?m)^[ \t]*(?:@\[[^\n]*\]\s*)*"
        r"(?:(?:private|protected|noncomputable)\s+)*"
        r"(?P<keyword>theorem|lemma)\s+(?P<name>[^\s({:\[]+)"
    )
    statements: list[Statement] = []
    for match in declaration.finditer(masked):
        assignment = find_assignment(masked, match.end())
        if assignment is None:
            raise RuntimeError(
                f"{relative(path)}:{masked.count(chr(10), 0, match.start()) + 1}: "
                f"could not find top-level ':=' for {match.group('name')}"
            )
        header = text[match.start() : assignment]
        masked_header = masked[match.start() : assignment]
        name_end = match.end("name") - match.start()
        colon = main_colon(masked_header, name_end)
        if colon is None:
            raise RuntimeError(
                f"{relative(path)}:{masked.count(chr(10), 0, match.start()) + 1}: "
                f"could not find result colon for {match.group('name')}"
            )
        statements.append(
            Statement(
                path=path,
                line=masked.count("\n", 0, match.start()) + 1,
                keyword=match.group("keyword"),
                name=match.group("name"),
                is_private=bool(re.search(r"\bprivate\b", masked_header[:name_end])),
                header=header,
                conclusion=header[colon + 1 :].strip(),
            )
        )
    return statements


def normalized(text: str) -> str:
    text = re.sub(r"\s+", " ", text).strip()
    while text.startswith("(") and text.endswith(")"):
        depth = 0
        encloses = True
        for index, char in enumerate(text):
            if char == "(":
                depth += 1
            elif char == ")":
                depth -= 1
                if depth == 0 and index != len(text) - 1:
                    encloses = False
                    break
        if not encloses:
            break
        text = text[1:-1].strip()
    return text


def hypothesis_bodies(header: str) -> list[str]:
    """Return named explicit/implicit binder bodies for contradiction triage."""

    return [
        normalized(match.group(1))
        for match in re.finditer(r"[\(\{]\s*h[\w₀-₉']*\s*:\s*([^)\}]+)[\)\}]", header)
    ]


def comparison(body: str) -> tuple[str, str, str] | None:
    match = re.fullmatch(r"(.+?)\s*(<=|>=|≤|<|≥|>)\s*(.+)", body)
    if not match:
        return None
    left, op, right = (normalized(part) for part in match.groups())
    if op in {"≥", ">="}:
        return right, "≤", left
    if op == ">":
        return right, "<", left
    if op == "<=":
        return left, "≤", right
    return left, op, right


def contradictory_pair(header: str) -> str | None:
    comparisons = [
        item for body in hypothesis_bodies(header) if (item := comparison(body)) is not None
    ]
    for index, (left, op, right) in enumerate(comparisons):
        for left2, op2, right2 in comparisons[index + 1 :]:
            if left == right2 and right == left2 and {op, op2} in (
                {"<", "≤"},
                {"<"},
            ):
                return f"{left} {op} {right} versus {left2} {op2} {right2}"
            if left == left2 and right == right2 and {op, op2} == {"<", "≤"}:
                # Same-direction < and ≤ are compatible, so do not flag.
                continue
    return None


def reflexive_equality(conclusion: str) -> bool:
    conclusion = normalized(conclusion)
    depth = 0
    for index, char in enumerate(conclusion):
        if char in "([{":
            depth += 1
        elif char in ")]}":
            depth = max(0, depth - 1)
        elif char == "=" and depth == 0:
            before = conclusion[index - 1] if index else ""
            after = conclusion[index + 1] if index + 1 < len(conclusion) else ""
            if before in "<>!:" or after in "=>":
                continue
            return normalized(conclusion[:index]) == normalized(conclusion[index + 1 :])
    return False


def flags(statement: Statement) -> list[tuple[str, str]]:
    header = normalized(statement.header)
    conclusion = normalized(statement.conclusion)
    found: list[tuple[str, str]] = []

    contradiction = contradictory_pair(header)
    if contradiction:
        found.append(("contradictory_numeric_hypotheses", contradiction))
    if re.search(r"\bIsEmpty\b", header):
        found.append(("empty_domain_IsEmpty", "statement assumes an IsEmpty instance"))
    if re.search(r"\bFin\s+0\b|\bFin\s*\(\s*0\s*\)", header):
        found.append(("empty_domain_Fin0", "statement mentions the empty index type Fin 0"))
    if re.search(r"\bFintype\.card\b[^\n:;,)]*=\s*0\b", header):
        found.append(("empty_domain_card_zero", "statement assumes a Fintype cardinality of zero"))
    if re.search(r"\[(?:Subsingleton|Unique)\b|\b(?:Subsingleton|Unique)\s+[A-Za-zα-ωΑ-Ω]", header):
        found.append(
            (
                "degenerate_typeclass",
                "statement carries a Subsingleton/Unique assumption requiring review",
            )
        )
    if re.search(r"\bMatrix\s*\(\s*Fin\s+0\s*\)\s*\(\s*Fin\s+0\s*\)", header):
        found.append(("zero_dimension_matrix", "statement explicitly uses a 0×0 matrix type"))
    if re.search(r"(?:∀|forall)\s+[^,]+,\s*[^,\n]+\s*∈\s*(?:∅|Set\.empty)", conclusion):
        found.append(("empty_set_quantifier", "conclusion quantifies over an empty set"))
    if conclusion == "True":
        found.append(("trivial_true", "conclusion is syntactically True"))
    if reflexive_equality(conclusion):
        found.append(("reflexive_conclusion", "conclusion is a syntactic reflexive equality"))
    if re.search(r"≤\s*⊤\s*$", conclusion):
        found.append(("top_upper_bound", "conclusion is syntactically bounded above by top"))
    if re.match(
        r"0\s*≤\s*(?:‖|norm\b|abs\b|Real\.sqrt\b|"
        r"\([^)]*\)\s*\^\s*(?:2|[02468])\s*$)",
        conclusion,
    ):
        found.append(
            (
                "syntactic_nonnegativity",
                "conclusion has a standard syntactically nonnegative shape",
            )
        )
    return found


def write_rows(
    path: Path, statements: Iterable[Statement], *, include_clean: bool
) -> tuple[int, int]:
    fields = [
        "path",
        "line",
        "keyword",
        "name",
        "visibility",
        "flags",
        "details",
        "conclusion",
        "statement",
    ]
    statement_count = 0
    hit_count = 0
    with path.open("w", encoding="utf-8", newline="") as handle:
        writer = csv.DictWriter(handle, delimiter="\t", fieldnames=fields)
        writer.writeheader()
        for statement in statements:
            statement_count += 1
            statement_flags = flags(statement)
            if statement_flags:
                hit_count += 1
            if include_clean or statement_flags:
                writer.writerow(
                    {
                        "path": relative(statement.path),
                        "line": statement.line,
                        "keyword": statement.keyword,
                        "name": statement.name,
                        "visibility": "private" if statement.is_private else "non-private",
                        "flags": ",".join(flag for flag, _ in statement_flags),
                        "details": " | ".join(detail for _, detail in statement_flags),
                        "conclusion": tsv_safe(normalized(statement.conclusion)),
                        "statement": tsv_safe(normalized(statement.header)),
                    }
                )
    return statement_count, hit_count


def main() -> int:
    LOGS.mkdir(parents=True, exist_ok=True)
    if not PLANT.is_file():
        raise RuntimeError(f"required calibration plant is missing: {PLANT}")

    plant_statements = extract(PLANT)
    plant_count, plant_hits = write_rows(
        LOGS / "v6_vacuity_calibration.tsv", plant_statements, include_clean=True
    )
    plant_by_name = {statement.name: {flag for flag, _ in flags(statement)} for statement in plant_statements}
    calibration_requirements = {
        "verificationContradictionPlant": {"contradictory_numeric_hypotheses"},
        "verificationIsEmptyPlant": {"empty_domain_IsEmpty"},
        "verificationTrivialConclusionPlant": {"reflexive_conclusion"},
    }
    calibration_missing = {
        name: sorted(required - plant_by_name.get(name, set()))
        for name, required in calibration_requirements.items()
        if not required.issubset(plant_by_name.get(name, set()))
    }

    universe = lean_universe()
    statements = [statement for path in universe for statement in extract(path)]
    statement_count, hit_statements = write_rows(
        LOGS / "v6_tier_a_statements.tsv", statements, include_clean=True
    )
    _, hit_statements_check = write_rows(
        LOGS / "v6_tier_a_hits.tsv", statements, include_clean=False
    )
    assert hit_statements == hit_statements_check
    keyword_counts = {
        keyword: sum(statement.keyword == keyword for statement in statements)
        for keyword in ("theorem", "lemma")
    }
    flag_counts: dict[str, int] = {}
    for statement in statements:
        for flag, _ in flags(statement):
            flag_counts[flag] = flag_counts.get(flag, 0) + 1
    private_counts = {
        keyword: sum(
            statement.keyword == keyword and statement.is_private
            for statement in statements
        )
        for keyword in ("theorem", "lemma")
    }
    nonprivate_counts = {
        keyword: keyword_counts[keyword] - private_counts[keyword]
        for keyword in ("theorem", "lemma")
    }
    expected_public = {"theorem": 467, "lemma": 841}
    coverage_problem = nonprivate_counts != expected_public

    summary = {
        "scope": [relative(path) for path in universe],
        "source_files": len(universe),
        "statements": statement_count,
        "keyword_counts": keyword_counts,
        "private_keyword_counts": private_counts,
        "nonprivate_keyword_counts": nonprivate_counts,
        "statements_with_flags": hit_statements,
        "flag_counts": dict(sorted(flag_counts.items())),
        "calibration_statements": plant_count,
        "calibration_statements_with_flags": plant_hits,
        "calibration_missing": calibration_missing,
        "expected_nonprivate_keyword_counts": expected_public,
        "coverage_reconciliation": (
            "all extracted statements = README non-private keyword counts + "
            "separately measured private statements"
        ),
        "coverage_matches_nonprivate_keyword_counts": not coverage_problem,
    }
    (LOGS / "v6_tier_a_summary.json").write_text(
        json.dumps(summary, indent=2, sort_keys=True) + "\n", encoding="utf-8"
    )
    lines = [
        "V6 TIER A CALIBRATED VACUITY/TRIVIALITY TRIAGE",
        f"CALIBRATION_PLANT {relative(PLANT)}",
        f"CALIBRATION_STATEMENTS {plant_count}",
        f"CALIBRATION_HIT_STATEMENTS {plant_hits}",
        f"CALIBRATION_MISSING {len(calibration_missing)}",
        *(
            f"MISSING {name} {','.join(missing)}"
            for name, missing in sorted(calibration_missing.items())
        ),
        f"SOURCE_FILES {len(universe)}",
        f"STATEMENTS {statement_count}",
        f"THEOREMS {keyword_counts['theorem']}",
        f"LEMMAS {keyword_counts['lemma']}",
        f"PRIVATE_THEOREMS {private_counts['theorem']}",
        f"PRIVATE_LEMMAS {private_counts['lemma']}",
        f"NONPRIVATE_THEOREMS {nonprivate_counts['theorem']}",
        f"NONPRIVATE_LEMMAS {nonprivate_counts['lemma']}",
        f"EXPECTED_NONPRIVATE_THEOREMS {expected_public['theorem']}",
        f"EXPECTED_NONPRIVATE_LEMMAS {expected_public['lemma']}",
        f"COVERAGE_MATCH {str(not coverage_problem).lower()}",
        f"FLAGGED_STATEMENTS {hit_statements}",
        "FLAG_COUNTS",
        *(f"{name}\t{count}" for name, count in sorted(flag_counts.items())),
        f"VERDICT {'PASS' if not calibration_missing and not coverage_problem else 'FAIL'}",
        "NOTE A PASS here means scanner calibration and coverage succeeded; Tier A hits are triage, "
        "not findings, and silence is not a semantic proof.",
    ]
    (LOGS / "v6_tier_a_run.log").write_text(
        "\n".join(lines) + "\n", encoding="utf-8"
    )
    print("\n".join(lines))
    return 0 if not calibration_missing and not coverage_problem else 1


if __name__ == "__main__":
    raise SystemExit(main())
