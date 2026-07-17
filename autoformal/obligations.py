from __future__ import annotations

import re
from pathlib import Path

from .lean.dependencies import import_graph
from .models import ObligationKind, ObligationStatus, ProofObligation

MARKERS = {
    "EXERCISE-SORRY": ObligationKind.EXERCISE_DEFERRED,
    "EXTERNAL-SORRY": ObligationKind.EXTERNAL_DEFERRED,
    "UNRESOLVED-PROOF-": ObligationKind.UNRESOLVED_PROOF,
    "FORWARD-SORRY-": ObligationKind.FORWARD_DEPENDENCY,
}


def obligation_kind_for_marker(marker: str) -> ObligationKind:
    for prefix, kind in MARKERS.items():
        if prefix in marker: return kind
    raise ValueError(f"unregistered proof-gap marker: {marker}")


def main_line_blocking(obligation: ProofObligation, allowed_categories: set[str]) -> bool:
    category = {
        ObligationKind.EXERCISE_DEFERRED: "A", ObligationKind.EXTERNAL_DEFERRED: "B",
        ObligationKind.UNRESOLVED_PROOF: "C", ObligationKind.FORWARD_DEPENDENCY: "D",
    }.get(obligation.kind)
    if obligation.status in {ObligationStatus.DISCHARGED, ObligationStatus.WAIVED}: return False
    if category not in allowed_categories: return True
    if category in {"A", "B"}: return not obligation.isolated
    return False  # C/D yield conditional verification, not immediate dependency blocking.


def verify_leaf_isolation(project: Path, leaf_modules: set[str], core_modules: set[str]) -> list[str]:
    graph = import_graph(project)
    violations: list[str] = []
    for core in core_modules:
        stack, seen = [core], set()
        while stack:
            node = stack.pop()
            if node in seen: continue
            seen.add(node)
            for imported in graph.get(node, []):
                if imported in leaf_modules:
                    violations.append(f"{core} transitively imports deferred leaf {imported}")
                if imported in graph: stack.append(imported)
    return sorted(set(violations))


def registered_marker_ids(text: str) -> set[str]:
    return set(re.findall(r"(?:UNRESOLVED-PROOF|FORWARD-SORRY|SPEC-OBLIGATION)-[A-Za-z0-9_-]+|EXERCISE-SORRY|EXTERNAL-SORRY", text))


def gap_registration_violations(placeholders: list[dict[str, object]], obligations: list[ProofObligation]) -> list[dict[str, object]]:
    registered = {item.marker for item in obligations if item.marker and item.status == ObligationStatus.OPEN}
    violations: list[dict[str, object]] = []
    for finding in placeholders:
        if finding.get("kind") != "sorry":
            continue
        context = str(finding.get("context", finding.get("excerpt", "")))
        markers = registered_marker_ids(context)
        if not markers or not any(marker in registered for marker in markers):
            violations.append(finding)
    return violations


def discharge_forward_obligation(state, project: Path, obligation_id: str) -> ProofObligation:
    from .lean.axioms import public_declarations
    from .lean.dependencies import detect_cycles, import_graph

    obligation = state.obligation(obligation_id)
    if obligation.kind != ObligationKind.FORWARD_DEPENDENCY:
        raise ValueError(f"not a forward-dependency obligation: {obligation_id}")
    cycles = detect_cycles(import_graph(project))
    if cycles:
        raise ValueError(f"cannot discharge through an import cycle: {cycles}")
    target = obligation.discharge_target or obligation.declaration
    declarations = public_declarations(project)
    if not target or not any(item == target or item.endswith("." + target) for item in declarations):
        raise ValueError(f"forward discharge target is not available: {target}")
    return state.transition_obligation(obligation_id, ObligationStatus.DISCHARGED,
                                       reason=f"verified target {target}")


def proposition_registration_violations(findings: list[dict[str, object]],
                                        obligations: list[ProofObligation]) -> list[dict[str, object]]:
    registered = {item.marker for item in obligations if item.marker and item.status == ObligationStatus.OPEN}
    violations: list[dict[str, object]] = []
    for finding in findings:
        context = str(finding.get("context", ""))
        markers = registered_marker_ids(context)
        if not finding.get("registered") or not any(
            marker in obligation_marker for marker in markers for obligation_marker in registered
        ):
            violations.append(finding)
    return violations
