"""Pure completion classification and chapter-verdict construction."""

from __future__ import annotations

from collections.abc import Iterable

from ...models import ChapterVerdict, ProofObligation


def classify_completion(
    blocker_count: int,
    open_obligations: Iterable[ProofObligation],
) -> str:
    obligations = list(open_obligations)
    conditional = [
        item
        for item in obligations
        if item.kind.value in {"unresolved_proof", "forward_dependency"}
    ]
    deferred = [
        item
        for item in obligations
        if item.kind.value in {"exercise_deferred", "external_deferred"}
        and item.isolated
    ]
    invalid = [
        item for item in obligations if item not in conditional and item not in deferred
    ]
    if blocker_count or invalid:
        return "incomplete"
    if conditional:
        return "structurally_complete_conditionally_verified"
    if deferred:
        return "main_line_verified_deferred_leaf_items"
    return "fully_formalized_and_verified"


def chapter_verdict(
    *,
    book_id: str,
    chapter_id: str,
    classification: str,
    build_passed: bool,
    blocker_count: int,
    audit_units: int,
    finding_count: int,
    placeholder_count: int,
    theorem_contracts: int,
    contract_failures: int,
    artifact_hashes: dict[str, str],
) -> ChapterVerdict:
    return ChapterVerdict(
        book_id=book_id,
        chapter_id=chapter_id,
        classification=classification,
        build_passed=build_passed,
        blocking_findings=blocker_count,
        counts={
            "audit_units": audit_units,
            "findings": finding_count,
            "blockers": blocker_count,
            "placeholders": placeholder_count,
            "theorem_contracts": theorem_contracts,
            "contract_failures": contract_failures,
        },
        artifact_hashes=artifact_hashes,
    )
