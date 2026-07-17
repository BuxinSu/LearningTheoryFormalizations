from __future__ import annotations

import json
import uuid
from pathlib import Path

from ...artifacts import ArtifactStore
from ...lean.dependencies import detect_cycles, import_graph
from ...models import (
    AgentJob, BookConfig, CoverageDecision, CoverageStatus, FormalizationPlan,
    ObligationKind, ProofObligation, SourceClaim, SourceManifest, Stage, TheoremContract,
)
from .source_discovery import discover_book_claims
from ...state import StateStore

CHAPTER1_REQUIRED_CONTRACTS = [
    "scalar_bernstein", "bernstein_variance_identity", "matrix_bernstein_variance_eq",
    "matrix_bernstein_tail", "matrix_bernstein_expectation", "expectation_sampleCovariance",
    "sampleCovariance_expected_error", "sampleCovariance_relative_error",
]


def discover_source_claims(config: BookConfig, state: StateStore, worktree: Path) -> list[SourceClaim]:
    claims: list[SourceClaim] = []
    reports = worktree / "TranslationReport"
    for path in sorted(reports.glob("Chapter*_inventory.json")) if reports.exists() else []:
        payload = json.loads(path.read_text(encoding="utf-8"))
        chapter_id = str(payload.get("chapter_id") or path.stem.split("Chapter", 1)[-1].split("_", 1)[0])
        for unit in payload.get("units", payload.get("items", [])):
            decision = str(unit.get("decision", "formalize"))
            if decision not in set(CoverageDecision): decision = "formalize"
            declaration_names = [str(item) for item in unit.get("lean_declarations", [])]
            status = CoverageStatus.FORMALIZED if declaration_names else (
                CoverageStatus.JUSTIFIED_OMISSION if decision == "omit" else CoverageStatus.MISSING
            )
            claim = SourceClaim(
                id=str(unit.get("id")), book_id=config.book_id, chapter_id=chapter_id,
                section_id=str(unit.get("section_id", chapter_id)), kind=str(unit.get("kind", "prose_claim")),
                claim=str(unit.get("claim", unit.get("exact_claim", ""))),
                pdf_location=str(unit.get("source_location", "PDF location pending verification")),
                tex_location=str(path), load_bearing=bool(unit.get("load_bearing", False)),
                later_uses=[str(value) for value in unit.get("later_uses", [])],
                external_used_downstream=bool(unit.get("external_used_downstream", False)),
                decision=decision, coverage_status=status, lean_declarations=declaration_names,
            )
            state.save_source_claim(claim); claims.append(claim)
    return claims


def plan_book(config: BookConfig, state: StateStore, worktree: Path) -> FormalizationPlan:
    preflight = state.latest_preflight(config.book_id)
    profile = state.active_policy_profile(config.book_id)
    if not preflight or not preflight.passed or not profile or preflight.policy_hash != profile.policy_hash:
        raise ValueError("a passing preflight for the active policy is required")
    job = AgentJob(
        id=f"job-{uuid.uuid4().hex}", book_id=config.book_id, role="planner",
        pass_name="planning", read_only=True, input_snapshot_hash=preflight.build_hash or preflight.policy_hash,
        allowed_paths=[str(worktree), str(state.active_run_dir(config.book_id) / "source")], status="running",
    )
    state.save_job(job)
    manifest_path = state.active_run_dir(config.book_id) / "source" / "source-manifest.json"
    if not manifest_path.is_file():
        raise ValueError("source manifest is required before planning")
    manifest = SourceManifest.model_validate_json(manifest_path.read_text(encoding="utf-8"))
    claims = discover_book_claims(config, state, manifest)
    inventory_claims = discover_source_claims(config, state, worktree)
    claims = list({item.id: item for item in [*claims, *inventory_claims]}.values())
    for claim in claims:
        obligation = None
        if claim.kind == "exercise" and claim.exercise_is_proof_question:
            if claim.load_bearing:
                obligation = ProofObligation(
                    id=f"EXERCISE-PROOF-{claim.id}", book_id=config.book_id,
                    chapter_id=claim.chapter_id, kind=ObligationKind.PROOF,
                    source_claim_id=claim.id, source_evidence=claim.pdf_location,
                    reason="load-bearing proof exercise must be formalized",
                    discharge_target=(claim.lean_declarations[0] if claim.lean_declarations else None),
                )
            else:
                obligation = ProofObligation(
                    id=f"EXERCISE-{claim.id}", book_id=config.book_id,
                    chapter_id=claim.chapter_id, kind=ObligationKind.EXERCISE_DEFERRED,
                    source_claim_id=claim.id, source_evidence=claim.pdf_location,
                    reason="non-load-bearing proof exercise deferred to an isolated leaf",
                    marker="EXERCISE-SORRY", isolated=True,
                    discharge_target=f"exercise leaf for {claim.id}",
                )
        elif claim.kind == "external_result":
            if claim.external_used_downstream:
                obligation = ProofObligation(
                    id=f"EXTERNAL-PROOF-{claim.id}", book_id=config.book_id,
                    chapter_id=claim.chapter_id, kind=ObligationKind.PROOF,
                    source_claim_id=claim.id, source_evidence=claim.pdf_location,
                    reason="downstream-used external result must be independently proved",
                    discharge_target=(claim.lean_declarations[0] if claim.lean_declarations else None),
                )
            else:
                obligation = ProofObligation(
                    id=f"EXTERNAL-{claim.id}", book_id=config.book_id,
                    chapter_id=claim.chapter_id, kind=ObligationKind.EXTERNAL_DEFERRED,
                    source_claim_id=claim.id, source_evidence=claim.pdf_location,
                    reason="unused external result assigned to isolated appendix",
                    marker="EXTERNAL-SORRY", isolated=True,
                    discharge_target=f"appendix proof for {claim.id}",
                )
        if obligation: state.save_obligation(obligation)
    graph = import_graph(worktree)
    cycles = detect_cycles(graph)
    if cycles: raise ValueError(f"Lean module dependency cycle: {cycles}")
    contracts: list[TheoremContract] = []
    contract_snapshot = config.prompts.formalization_policy.parent / "references" / "chapter1_contracts.json"
    if contract_snapshot.is_file():
        contracts = [TheoremContract.model_validate(item) for item in
                     json.loads(contract_snapshot.read_text(encoding="utf-8"))]
    elif config.book_id == "tropp-matrix-concentration":
        # Backward-compatible profile fallback; production profiles should carry
        # exact versioned contract snapshots rather than placeholder signatures.
        contracts.extend(TheoremContract(declaration=name, lean_type="<compatible type required>", chapter_id="1")
                         for name in CHAPTER1_REQUIRED_CONTRACTS)
    modules = sorted(graph)
    reachable: set[str] = set(); stack = [config.lean.namespace]
    while stack:
        module = stack.pop()
        if module in reachable: continue
        reachable.add(module); stack.extend(item for item in graph.get(module, []) if item in graph)
    nonreachable = set(modules) - reachable
    exercise = [name for name in modules if name in nonreachable and "exercise" in name.lower()]
    appendix = [name for name in modules if name in nonreachable and "appendix" in name.lower()]
    deferred = [name for name in modules if name in nonreachable and "deferred" in name.lower()]
    leaves = set(exercise + appendix + deferred)
    plan = FormalizationPlan(
        id=f"plan-{uuid.uuid4().hex}", book_id=config.book_id, policy_hash=profile.policy_hash,
        theorem_contracts=contracts,
        load_bearing_claim_ids=[claim.id for claim in claims if claim.load_bearing],
        module_dag=graph, core_modules=[name for name in modules if name not in leaves],
        exercise_modules=exercise, appendix_modules=appendix, deferred_modules=deferred,
        obligation_ids=[item.id for item in state.obligations(config.book_id)],
        verification_commands=[["lake", "build"], ["lake", "env", "lean", "PrintAxioms.lean"]],
        acceptance_conditions=[
            "Every required public contract exists with a compatible type.",
            "The project builds with the pinned toolchain and Mathlib revision.",
            "Every public theorem has recorded #print axioms output.",
            "There are no unregistered proof gaps or import cycles.",
            "Deferred exercise/appendix items are isolated from main-line imports.",
        ],
    )
    state.save_plan(plan)
    ArtifactStore(state.active_run_dir(config.book_id)).write_json("plans/formalization-plan.json", plan)
    job.status = "completed"; job.checkpoint = plan.id; state.save_job(job)
    state.set_book_stage(config.book_id, Stage.PLANNED)
    for chapter in manifest.chapters:
        state.set_chapter_stage(config.book_id, chapter.id, Stage.PLANNED,
                                pass_budgets=config.policy.pass_budgets)
    return plan
