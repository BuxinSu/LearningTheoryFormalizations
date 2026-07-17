from __future__ import annotations

from pathlib import Path

from .infrastructure.hashing import sha256_file, sha256_json
from .models import BookConfig, PolicyProfile


def resolve_policy_profile(config: BookConfig) -> PolicyProfile:
    required = [
        config.input_pdf,
        config.prompts.formalization_policy,
        config.prompts.source_conventions,
        config.prompts.draft_template,
        config.prompts.review_template,
        config.prompts.revision_template,
        *config.policy.required_paths,
        *config.policy.exercise_paths,
        *config.policy.hint_paths,
        *config.policy.report_paths,
    ]
    payload = {
        "book_id": config.book_id,
        "name": config.policy.profile_name,
        "version": config.policy.profile_version,
        "pdf_is_final_authority": config.source.pdf_is_final_authority,
        "source_authority_rules": [
            "The configured PDF is the sole mathematical authority.",
            "TeX, mechanical extracts, reports, and memory are navigation aids.",
            "Citations must be verified against the PDF before literature retrieval.",
        ],
        "allowed_gap_categories": sorted(config.policy.allowed_gap_categories),
        "module_layout": config.policy.module_layout,
        "required_paths": sorted(str(Path(path).resolve()) for path in required),
        "path_hashes": {
            str(Path(path).resolve()): sha256_file(Path(path)) if Path(path).is_file() else "missing"
            for path in required
        },
        "pass_budgets": config.policy.pass_budgets,
        "toolchain": config.lean.toolchain,
        "mathlib_revision": config.lean.mathlib_revision,
        "authoritative_page_range": [
            config.policy.authoritative_page_start, config.policy.authoritative_page_end,
        ],
        "transcription_status": config.policy.transcription_status,
    }
    return PolicyProfile(**payload, policy_hash=sha256_json(payload))
