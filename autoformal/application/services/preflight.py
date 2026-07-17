from __future__ import annotations

import json
import uuid
from pathlib import Path

from ...artifacts import ArtifactStore
from ...infrastructure.hashing import hash_tree, sha256_file
from ...lean.build import lake_build
from ...lean.dependencies import detect_cycles, import_graph
from ...models import AgentJob, BookConfig, PreflightManifest, SourceManifest, Stage, ValidationCheck
from ...obligations import verify_leaf_isolation
from ...policy import resolve_policy_profile
from ...state import StateStore


class PreflightError(RuntimeError):
    def __init__(self, manifest: PreflightManifest) -> None:
        failed = ", ".join(check.name for check in manifest.checks if not check.passed)
        super().__init__(f"preflight failed: {failed}")
        self.manifest = manifest


def _check_file(name: str, path: Path) -> ValidationCheck:
    return ValidationCheck(name=name, passed=path.is_file(), details=str(path))


def run_preflight(config: BookConfig, state: StateStore, worktree: Path, *, build: bool = True) -> PreflightManifest:
    profile = resolve_policy_profile(config)
    state.save_policy_profile(profile)
    job = AgentJob(
        id=f"job-{uuid.uuid4().hex}", book_id=config.book_id, role="preflight",
        pass_name="preflight", read_only=True, input_snapshot_hash=profile.policy_hash,
        allowed_paths=[str(path) for path in profile.required_paths], status="running",
    )
    state.save_job(job)
    checks: list[ValidationCheck] = []
    resolved = {"pdf": str(config.input_pdf), "worktree": str(worktree)}
    checks.append(_check_file("authoritative_pdf", config.input_pdf))
    prompt_paths = {
        "formalization_policy": config.prompts.formalization_policy,
        "source_conventions": config.prompts.source_conventions,
        "draft_template": config.prompts.draft_template,
        "review_template": config.prompts.review_template,
        "revision_template": config.prompts.revision_template,
    }
    for name, path in prompt_paths.items():
        resolved[name] = str(path); checks.append(_check_file(name, path))
    for index, path in enumerate(config.policy.required_paths):
        resolved[f"required_{index}"] = str(path)
        checks.append(ValidationCheck(name=f"required_path_{index}", passed=path.exists(), details=str(path)))
    for group, paths in (("exercise", config.policy.exercise_paths), ("hint", config.policy.hint_paths), ("report", config.policy.report_paths)):
        for index, path in enumerate(paths):
            resolved[f"{group}_{index}"] = str(path)
            checks.append(ValidationCheck(name=f"{group}_path_{index}", passed=path.exists(), details=str(path)))

    start, end = config.policy.authoritative_page_start, config.policy.authoritative_page_end
    range_ok = start is None or end is None or start <= end
    checks.append(ValidationCheck(name="authoritative_page_range", passed=range_ok, details=f"{start or 'first'}..{end or 'last'}"))
    checks.append(ValidationCheck(name="transcription_status", passed=True, details=config.policy.transcription_status))

    source_manifest_path = state.active_run_dir(config.book_id) / "source" / "source-manifest.json"
    if source_manifest_path.is_file():
        try:
            source_manifest = SourceManifest.model_validate_json(
                source_manifest_path.read_text(encoding="utf-8")
            )
            checks.append(ValidationCheck(
                name="source_manifest_identity", passed=source_manifest.book_id == config.book_id,
                details=source_manifest.book_id,
            ))
            checks.append(ValidationCheck(
                name="source_pdf_fingerprint",
                passed=config.input_pdf.is_file() and source_manifest.pdf_sha256 == sha256_file(config.input_pdf),
                details=source_manifest.pdf_sha256,
            ))
            checks.append(ValidationCheck(
                name="canonical_tex_complete", passed=Path(source_manifest.canonical_tex_root).is_dir()
                and bool(source_manifest.chapters), details=source_manifest.canonical_tex_root,
            ))
            failed_source = [item.name for item in source_manifest.validation if not item.passed]
            checks.append(ValidationCheck(
                name="source_validation", passed=not failed_source, details=", ".join(failed_source) or "all passed",
            ))
            range_within_pdf = not source_manifest.page_count or (
                (start is None or start <= source_manifest.page_count)
                and (end is None or end <= source_manifest.page_count)
            )
            checks.append(ValidationCheck(
                name="page_range_within_pdf", passed=range_within_pdf,
                details=f"page_count={source_manifest.page_count}",
            ))
        except Exception as error:
            checks.append(ValidationCheck(name="source_manifest_parse", passed=False, details=repr(error)))

    toolchain = worktree / "lean-toolchain"
    lakefile = worktree / "lakefile.toml"
    aggregator = worktree / f"{config.lean.namespace}.lean"
    checks.append(ValidationCheck(
        name="lean_toolchain_pin",
        passed=toolchain.is_file() and toolchain.read_text().strip() == config.lean.toolchain,
        details=f"expected {config.lean.toolchain} in {toolchain}",
    ))
    lake_text = lakefile.read_text(encoding="utf-8", errors="replace") if lakefile.is_file() else ""
    checks.append(ValidationCheck(
        name="mathlib_pin", passed=lakefile.is_file() and config.lean.mathlib_revision in lake_text,
        details=f"expected {config.lean.mathlib_revision} in {lakefile}",
    ))
    checks.append(ValidationCheck(name="root_aggregator", passed=aggregator.is_file(), details=str(aggregator)))
    graph = import_graph(worktree) if worktree.exists() else {}
    cycles = detect_cycles(graph)
    checks.append(ValidationCheck(name="acyclic_module_graph", passed=not cycles, details=json.dumps(cycles)))
    namespace_modules = [name for name in graph if name == config.lean.namespace or name.startswith(config.lean.namespace + ".")]
    checks.append(ValidationCheck(name="namespace_reachable", passed=bool(namespace_modules), details=", ".join(namespace_modules)))
    root_module = config.lean.namespace
    reachable: set[str] = set()
    stack = [root_module]
    while stack:
        module = stack.pop()
        if module in reachable: continue
        reachable.add(module)
        stack.extend(item for item in graph.get(module, []) if item in graph)
    leaf_tokens = {"exercise", "appendix", "deferred"}
    nonreachable = set(namespace_modules) - reachable
    leaf_modules = {
        name for name in nonreachable if any(token in name.lower() for token in leaf_tokens)
    }
    unexpected_unreachable = sorted(nonreachable - leaf_modules)
    core_modules = (set(namespace_modules) & reachable) - {root_module}
    checks.append(ValidationCheck(
        name="aggregator_reachability", passed=not unexpected_unreachable,
        details=", ".join(unexpected_unreachable) or "all core modules reachable",
    ))
    isolation_violations = verify_leaf_isolation(worktree, leaf_modules, core_modules | {root_module})
    checks.append(ValidationCheck(
        name="deferred_leaf_isolation", passed=not isolation_violations,
        details="; ".join(isolation_violations) or "isolated",
    ))

    build_result = lake_build(worktree) if build and worktree.exists() else None
    if build_result is not None:
        checks.append(ValidationCheck(name="existing_project_build", passed=build_result.returncode == 0,
                                      details=(build_result.stdout + build_result.stderr)[-4000:]))
    manifest = PreflightManifest(
        book_id=config.book_id, policy_hash=profile.policy_hash, checks=checks,
        resolved_paths=resolved, toolchain=config.lean.toolchain,
        mathlib_revision=config.lean.mathlib_revision,
        source_page_range=(start, end), transcription_status=config.policy.transcription_status,
        build_hash=hash_tree(worktree),
    )
    state.save_preflight(manifest)
    store = ArtifactStore(state.active_run_dir(config.book_id))
    store.write_json("preflight/manifest.json", manifest)
    if build_result is not None:
        store.write_json("preflight/build.json", build_result)
    if not manifest.passed:
        job.status = "failed"; state.save_job(job)
        raise PreflightError(manifest)
    job.status = "completed"; job.checkpoint = manifest.build_hash; state.save_job(job)
    state.set_book_stage(config.book_id, Stage.PREFLIGHT)
    return manifest
