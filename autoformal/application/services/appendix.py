from __future__ import annotations

import hashlib
import uuid
from pathlib import Path
from typing import Callable

from ...adapters.verification import verification_service
from ...application.verification import VerificationRequest
from ...artifacts import ArtifactStore
from ...infrastructure.git_worktree import GitWorkspace
from ...lean.axioms import public_declarations
from ...memory import KnowledgeStore
from ...models import AgentJob, BookConfig, ObligationKind, ProofObligation
from ...state import StateStore
from ..job_control import LeaseSpec, managed_job


def run_appendix_job(
    config: BookConfig,
    state: StateStore,
    workspace: GitWorkspace,
    theorem_name: str,
    module_path: Path,
    citation: str,
    literature_evidence: str,
    proof_strategy: str,
    worker: Callable[[Path], None],
) -> dict[str, object]:
    """Prove an external result under an appendix-only writer lease."""
    absolute_module = (
        module_path if module_path.is_absolute() else workspace.path / module_path
    )
    appendix_root = workspace.path / config.policy.module_layout.get(
        "appendix", f"{config.lean.namespace}.Appendix"
    ).replace(".", "/")
    try:
        absolute_module.resolve().relative_to(appendix_root.resolve())
    except ValueError as error:
        raise ValueError(
            f"appendix job path is outside appendix scope: {absolute_module}"
        ) from error

    snapshot = f"{citation}\n{literature_evidence}\n{proof_strategy}"
    job = AgentJob(
        id=f"job-{uuid.uuid4().hex}",
        book_id=config.book_id,
        role="appendix",
        pass_name="appendix",
        input_snapshot_hash=hashlib.sha256(snapshot.encode()).hexdigest(),
        allowed_paths=[str(absolute_module)],
        status="running",
    )
    with managed_job(
        state,
        job,
        [LeaseSpec("appendix", str(absolute_module))],
        config.codex.timeout_seconds,
    ) as active_job:
        store = ArtifactStore(state.active_run_dir(config.book_id))
        memory = KnowledgeStore(
            config.runtime_dir / "memory" / "knowledge.sqlite3"
        )
        dossier_id = memory.save_literature_dossier(
            theorem_name,
            citation,
            proof_strategy,
            "in_progress",
            {
                "literature_evidence": literature_evidence,
                "module": str(absolute_module),
            },
        )
        checkpoint: dict[str, object] = {
            "theorem": theorem_name,
            "citation": citation,
            "literature_evidence": literature_evidence,
            "proof_strategy": proof_strategy,
            "dossier_id": dossier_id,
            "status": "running",
            "module": str(absolute_module),
        }
        store.write_json(f"appendix/{theorem_name}/checkpoint.json", checkpoint)
        worker(absolute_module)
        declarations = [
            item
            for item in public_declarations(absolute_module.parent)
            if item.endswith(theorem_name)
        ]
        module = ".".join(
            absolute_module.relative_to(workspace.path).with_suffix("").parts
        )
        verification = verification_service().verify(
            VerificationRequest(
                book_id=config.book_id,
                chapter_id=None,
                scan_root=absolute_module.parent,
                report_prefixes=[f"appendix/{theorem_name}/verification"],
                commit_message=f"Prove appendix result {theorem_name}",
                phase="appendix",
                job_id=active_job.id,
                attempt_payload={"theorem": theorem_name},
                axiom_modules=module,
                axiom_declarations=declarations,
                axiom_output=store.path(f"appendix/{theorem_name}/axioms"),
                require_axioms=True,
            ),
            state,
            workspace,
            store,
        )
        if verification.passed:
            commit = verification.green_commit
            assert commit is not None
            checkpoint.update(status="done", checkpoint=commit)
            active_job.status = "completed"
            active_job.checkpoint = commit
            active_job.latest_attempt_id = verification.attempt_id
            active_job.last_green_attempt_id = verification.attempt_id
            memory.save_literature_dossier(
                theorem_name,
                citation,
                proof_strategy,
                "done",
                {
                    "literature_evidence": literature_evidence,
                    "module": str(absolute_module),
                    "green_commit": commit,
                },
            )
            memory.record_proof_strategy(
                None, theorem_name, proof_strategy, successful=True
            )
        else:
            obligation = ProofObligation(
                id=f"APPENDIX-{uuid.uuid4().hex[:12]}",
                book_id=config.book_id,
                kind=ObligationKind.EXTERNAL_DEFERRED,
                declaration=theorem_name,
                source_evidence=literature_evidence,
                reason="appendix proof did not verify",
                attempted_routes=[proof_strategy],
                marker="EXTERNAL-SORRY",
                isolated=True,
                discharge_target=str(absolute_module),
            )
            state.save_obligation(obligation)
            checkpoint.update(
                status="appendix_unresolved", obligation_id=obligation.id
            )
            active_job.status = "blocked"
            memory.save_literature_dossier(
                theorem_name,
                citation,
                proof_strategy,
                "appendix_unresolved",
                {
                    "literature_evidence": literature_evidence,
                    "module": str(absolute_module),
                    "obligation_id": obligation.id,
                },
            )
            memory.record_proof_strategy(
                None,
                theorem_name,
                proof_strategy,
                successful=False,
                failure=(
                    verification.build.stderr
                    or "placeholder/axiom verification failed"
                )[-4000:],
            )
        checkpoint["build"] = verification.build.model_dump(mode="json")
        checkpoint["placeholders"] = verification.placeholders
        checkpoint["axioms"] = (
            verification.axioms.model_dump(mode="json")
            if verification.axioms
            else None
        )
        store.write_json(f"appendix/{theorem_name}/checkpoint.json", checkpoint)
        return checkpoint
