"""Shared green-checkpoint verification for all writer workflows."""

from __future__ import annotations

from collections.abc import Callable
from dataclasses import dataclass, field
from pathlib import Path
from typing import Any

from ..domain import CommandResult
from ..obligations import gap_registration_violations, proposition_registration_violations
from .ports.verification import ArtifactWriter, GreenWorkspace, VerificationState


@dataclass(slots=True)
class VerificationRequest:
    book_id: str
    chapter_id: str | None
    scan_root: Path
    report_prefixes: list[str]
    commit_message: str
    phase: str
    job_id: str | None = None
    session_id: str | None = None
    attempt_payload: dict[str, Any] = field(default_factory=dict)
    axiom_modules: str | list[str] | None = None
    axiom_declarations: list[str] = field(default_factory=list)
    axiom_output: Path | None = None
    require_axioms: bool = False


@dataclass(slots=True)
class VerificationResult:
    build: CommandResult
    placeholders: list[dict[str, Any]]
    proposition_specifications: list[dict[str, Any]]
    violations: list[dict[str, Any]]
    axioms: CommandResult | None
    green_commit: str | None
    attempt_id: str | None

    @property
    def passed(self) -> bool:
        axiom_clean = self.axioms is None or (
            self.axioms.returncode == 0 and "sorryAx" not in self.axioms.stdout
        )
        return self.build.returncode == 0 and not self.violations and axiom_clean


class VerificationService:
    def __init__(
        self,
        *,
        build: Callable[[Path], CommandResult],
        scan_placeholders: Callable[[Path], list[dict[str, Any]]],
        unregistered_placeholders: Callable[[list[dict[str, Any]]], list[dict[str, Any]]],
        scan_propositions: Callable[[Path], list[dict[str, Any]]],
        unregistered_propositions: Callable[[list[dict[str, Any]]], list[dict[str, Any]]],
        print_axioms: Callable[[Path, str | list[str], list[str], Path], CommandResult],
    ) -> None:
        self._build = build
        self._scan_placeholders = scan_placeholders
        self._unregistered_placeholders = unregistered_placeholders
        self._scan_propositions = scan_propositions
        self._unregistered_propositions = unregistered_propositions
        self._print_axioms = print_axioms

    def verify(
        self,
        request: VerificationRequest,
        state: VerificationState,
        workspace: GreenWorkspace,
        artifacts: ArtifactWriter,
    ) -> VerificationResult:
        build = self._build(workspace.path)
        placeholders = self._scan_placeholders(request.scan_root)
        propositions = self._scan_propositions(request.scan_root)
        obligations = state.obligations(request.book_id, request.chapter_id)
        violations = self._unregistered_placeholders(placeholders)
        violations += gap_registration_violations(placeholders, obligations)
        violations += self._unregistered_propositions(propositions)
        violations += proposition_registration_violations(propositions, obligations)

        axioms = None
        if request.require_axioms and (
            request.axiom_modules is None or not request.axiom_declarations
        ):
            violations.append({
                "kind": "axiom_audit_missing",
                "context": "axiom modules and declarations are required",
            })
        if request.axiom_modules is not None and request.axiom_declarations:
            output = request.axiom_output or artifacts.path(
                f"verification/{request.phase}/axioms"
            )
            axioms = self._print_axioms(
                workspace.path,
                request.axiom_modules,
                request.axiom_declarations,
                output,
            )

        for prefix in request.report_prefixes:
            artifacts.write_json(f"{prefix}-build.json", build)
            artifacts.write_json(f"{prefix}-placeholders.json", placeholders)
            artifacts.write_json(f"{prefix}-proposition-specifications.json", propositions)
            artifacts.write_json(f"{prefix}-verification-violations.json", violations)
            if axioms is not None:
                artifacts.write_json(f"{prefix}-axioms.json", axioms)

        provisional = VerificationResult(
            build=build,
            placeholders=placeholders,
            proposition_specifications=propositions,
            violations=violations,
            axioms=axioms,
            green_commit=None,
            attempt_id=None,
        )
        if not provisional.passed:
            return provisional

        green_commit = workspace.commit_green(request.commit_message)
        attempt_id = None
        if request.job_id:
            attempt_id = state.create_attempt(
                request.job_id,
                "completed",
                session_id=request.session_id,
                checkpoint=green_commit,
                green_commit=green_commit,
                payload={"phase": request.phase, **request.attempt_payload},
            )
        provisional.green_commit = green_commit
        provisional.attempt_id = attempt_id
        return provisional
