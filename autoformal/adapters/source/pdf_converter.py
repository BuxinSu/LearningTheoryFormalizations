from __future__ import annotations

import io
import json
import re
import tempfile
from pathlib import Path

from ..agents.http_client import HTTPModelClient
from ..agents.prompt_renderer import PromptRenderer
from ...domain import ServiceConfig

CONVERSION_SCHEMA = {
    "type": "object", "additionalProperties": False,
    "required": ["batch_id", "page_start", "page_end", "tex", "uncertainties", "observed_structure"],
    "properties": {
        "batch_id": {"type": "string"}, "page_start": {"type": "integer"},
        "page_end": {"type": "integer"}, "tex": {"type": "string"},
        "uncertainties": {"type": "array", "items": {"type": "string"}},
        "observed_structure": {"type": "array", "items": {"type": "string"}},
    },
}

PAGE_MARKER_RE = re.compile(r"\\AutoFormalPage\{(\d+)\}")


def merge_page_batches(batches: list[dict], page_count: int) -> tuple[str, list[str]]:
    """Merge overlapping batches by page marker and report conflicting transcriptions."""
    pages: dict[int, str] = {}
    conflicts: list[str] = []
    for batch in batches:
        tex = str(batch["tex"])
        markers = list(PAGE_MARKER_RE.finditer(tex))
        if not markers:
            raise ValueError(f"converter batch {batch['batch_id']} contains no \\AutoFormalPage markers")
        for index, marker in enumerate(markers):
            page = int(marker.group(1))
            end = markers[index + 1].start() if index + 1 < len(markers) else len(tex)
            fragment = tex[marker.start():end].strip() + "\n"
            if page in pages and " ".join(pages[page].split()) != " ".join(fragment.split()):
                conflicts.append(f"page {page} differs in overlapping batches; retained first transcription")
            else:
                pages.setdefault(page, fragment)
    missing = [page for page in range(1, page_count + 1) if page not in pages]
    if missing:
        raise ValueError(f"converted TeX is missing page markers for pages: {missing}")
    return "\n".join(pages[page] for page in range(1, page_count + 1)), conflicts


def pdf_page_count(pdf: Path) -> int:
    from pypdf import PdfReader

    return len(PdfReader(str(pdf)).pages)


class PDFConverter:
    def __init__(
        self, config: ServiceConfig, renderer: PromptRenderer, template: Path,
        retries: int = 3, batch_pages: int = 8, overlap_pages: int = 1,
    ) -> None:
        if batch_pages <= overlap_pages:
            raise ValueError("batch_pages must exceed overlap_pages")
        self.client = HTTPModelClient(config, retries)
        self.renderer = renderer
        self.template = template
        self.batch_pages = batch_pages
        self.overlap_pages = overlap_pages

    def convert(self, pdf: Path, destination: Path, book_title: str) -> tuple[Path, list[dict]]:
        from pypdf import PdfReader, PdfWriter

        destination.mkdir(parents=True, exist_ok=True)
        reader = PdfReader(str(pdf))
        batches: list[dict] = []
        previous_context = "none"
        start = 0
        batch_number = 1
        while start < len(reader.pages):
            end = min(len(reader.pages), start + self.batch_pages)
            writer = PdfWriter()
            for page in reader.pages[start:end]:
                writer.add_page(page)
            with tempfile.NamedTemporaryFile(suffix=".pdf", delete=False) as handle:
                writer.write(handle)
                batch_pdf = Path(handle.name)
            batch_id = f"batch-{batch_number:04d}"
            prompt = self.renderer.render(self.template, {
                "book_title": book_title, "page_start": start + 1, "page_end": end,
                "batch_id": batch_id, "previous_context": previous_context,
            })
            try:
                result = self.client.generate_json(
                    prompt, CONVERSION_SCHEMA, [batch_pdf], schema_name="autoformal_tex_batch"
                )
            finally:
                batch_pdf.unlink(missing_ok=True)
            if result.get("batch_id") != batch_id or result.get("page_start") != start + 1 or result.get("page_end") != end:
                raise ValueError(f"converter returned mismatched batch metadata for {batch_id}")
            (destination / f"{batch_id}.json").write_text(json.dumps(result, indent=2) + "\n")
            batches.append(result)
            previous_context = result["tex"][-2000:]
            if end == len(reader.pages):
                break
            start = end - self.overlap_pages
            batch_number += 1

        merged, conflicts = merge_page_batches(batches, len(reader.pages))
        combined = destination / "converted.tex"
        combined.write_text(merged, encoding="utf-8")
        (destination / "merge-conflicts.json").write_text(json.dumps(conflicts, indent=2) + "\n")
        return combined, batches

