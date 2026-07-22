from __future__ import annotations

import re
from pathlib import Path

from .memory import normalize_lean_type
from .models import TheoremContract, ValidationCheck

DECL_RE = re.compile(
    r"^\s*(?:theorem|lemma|corollary|proposition)\s+([A-Za-z0-9_'.]+)\b"
    r"(.*?):=\s*(by|fun)(.*?)(?=^\s*(?:theorem|lemma|corollary|proposition|def|namespace|section|end)\b|\Z)",
    re.MULTILINE | re.DOTALL,
)


def declaration_signatures(project: Path) -> dict[str, tuple[str, str]]:
    result: dict[str, tuple[str, str]] = {}
    for path in sorted(project.rglob("*.lean")):
        if any(part in {".lake", ".git"} for part in path.parts): continue
        text = path.read_text(encoding="utf-8", errors="replace")
        for match in DECL_RE.finditer(text):
            name = match.group(1)
            signature = normalize_lean_type(match.group(2))
            body = normalize_lean_type(match.group(3) + " " + match.group(4))
            result.setdefault(name, (signature, body))
            result.setdefault(name.split(".")[-1], (signature, body))
    return result


def verify_theorem_contracts(project: Path, contracts: list[TheoremContract]) -> list[ValidationCheck]:
    observed = declaration_signatures(project)
    checks: list[ValidationCheck] = []
    for contract in contracts:
        actual = observed.get(contract.declaration) or observed.get(contract.declaration.split(".")[-1])
        if actual is None:
            checks.append(ValidationCheck(name=f"contract:{contract.declaration}", passed=not contract.required,
                                          details="declaration missing")); continue
        expected = normalize_lean_type(contract.lean_type)
        compatible = expected == "<compatible type required>" or actual[0] == expected
        genuine = not re.search(r"\b(?:sorry|admit)\b", actual[1])
        checks.append(ValidationCheck(
            name=f"contract:{contract.declaration}", passed=compatible and genuine,
            details=("compatible genuine proof" if compatible and genuine else
                     f"signature_match={compatible}, genuine_proof={genuine}, observed={actual[0]}"),
        ))
    return checks
