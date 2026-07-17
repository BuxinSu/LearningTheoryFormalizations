from __future__ import annotations

import shutil
from datetime import datetime, timezone
from pathlib import Path

from ...agents.prompt_renderer import PromptRenderer
from ...artifacts import ArtifactStore, atomic_write_json
from ...ingest.pdf_converter import PDFConverter, pdf_page_count
from ...ingest.segmenter import discover_structure
from ...ingest.source_resolver import download_authoritative_source
from ...ingest.tex_normalizer import normalize_tex_tree
from ...ingest.validator import validate_tex_tree
from ...infrastructure.hashing import sha256_file
from ...models import BookConfig, SourceManifest, Stage
from ...state import StateStore


def ingest_source(config: BookConfig, state: StateStore, renderer: PromptRenderer) -> SourceManifest:
    if not config.input_pdf.is_file():
        raise FileNotFoundError(f"input PDF not found: {config.input_pdf}")
    run_dir = state.active_run_dir(config.book_id)
    store = ArtifactStore(run_dir)
    source_dir = store.path("source")
    canonical_root: Path
    provenance: str
    authoritative_error: Exception | None = None

    if config.source.prefer_authoritative and config.source.authoritative_url:
        try:
            authoritative_dir = source_dir / "authoritative"
            files = download_authoritative_source(
                config.source.authoritative_url, authoritative_dir, config.transport_retries
            )
            if not any(path.suffix.lower() == ".tex" for path in files):
                raise ValueError("authoritative archive contains no TeX files")
            canonical_root = authoritative_dir / "tex"
            provenance = "authoritative_tex"
        except Exception as error:
            authoritative_error = error
            canonical_root = Path()
            provenance = "ai_conversion"
    else:
        canonical_root = Path()
        provenance = "ai_conversion"

    if provenance == "ai_conversion":
        if not config.converter.model:
            detail = f"; authoritative source failed: {authoritative_error}" if authoritative_error else ""
            raise RuntimeError("AI conversion is required but converter.model is not configured" + detail)
        canonical_root = source_dir / "ai" / "tex"
        converter = PDFConverter(
            config.converter, renderer, renderer.prompt_root / "source_conversion" / "pdf_pages_to_tex.md.j2",
            config.transport_retries,
        )
        converted, batches = converter.convert(config.input_pdf, canonical_root, config.title)
        store.write_json("source/ai/batches.json", batches)
        if not converted.is_file():
            raise RuntimeError("AI conversion did not produce canonical TeX")

    normalize_tex_tree(canonical_root)
    chapters = discover_structure(canonical_root, config.chapters.starts_at, source_dir / "chapters")
    validation = validate_tex_tree(canonical_root, chapters)
    if authoritative_error:
        store.write_text("source/authoritative-error.txt", repr(authoritative_error) + "\n")
    try:
        pages = pdf_page_count(config.input_pdf)
    except Exception:
        pages = None
    manifest = SourceManifest(
        book_id=config.book_id,
        pdf_path=str(config.input_pdf),
        pdf_sha256=sha256_file(config.input_pdf),
        page_count=pages,
        provenance=provenance,
        canonical_tex_root=str(canonical_root),
        chapters=chapters,
        validation=validation,
    )
    atomic_write_json(store.path("source/source-manifest.json"), manifest)
    state.invalidate_chapters(config.book_id, "source manifest regenerated")
    state.set_book_stage(config.book_id, Stage.SOURCE_READY)
    store.seal()
    return manifest


def approve_source(config: BookConfig, state: StateStore, approver: str) -> SourceManifest:
    path = state.active_run_dir(config.book_id) / "source" / "source-manifest.json"
    manifest = SourceManifest.model_validate_json(path.read_text(encoding="utf-8"))
    failed = [check for check in manifest.validation if not check.passed]
    if failed:
        names = ", ".join(check.name for check in failed)
        raise ValueError(f"source validation has failed checks: {names}")
    manifest.approved_by = approver
    manifest.approved_at = datetime.now(timezone.utc)
    atomic_write_json(path, manifest)
    state.set_book_stage(config.book_id, Stage.SOURCE_APPROVED)
    return manifest

