from __future__ import annotations

import hashlib
import re
from pathlib import Path

from ...infrastructure.hashing import sha256_json
from ...models import (
    BookConfig, CoverageDecision, CoverageStatus, SourceClaim, SourceManifest,
)
from ...state import StateStore

ENV_RE = re.compile(
    r"\\begin\{(theorem|lemma|proposition|corollary|definition|exercise|example|equation\*?)\}"
    r"(?:\[([^\]]+)\])?(.*?)\\end\{\1\}", re.DOTALL | re.IGNORECASE,
)
LABEL_RE = re.compile(r"\\label\{([^}]+)\}")
REF_RE = re.compile(r"\\(?:eqref|ref|autoref|cref|Cref)\{([^}]+)\}")
CITE_RE = re.compile(r"\\cite\w*\{([^}]+)\}")


def _plain_tex(value: str) -> str:
    value = re.sub(r"%.*", "", value)
    value = re.sub(r"\\(?:label|cite\w*|ref|eqref|autoref|cref|Cref)\{[^}]+\}", "", value)
    value = re.sub(r"\\[A-Za-z]+\*?(?:\[[^\]]*\])?", " ", value)
    return re.sub(r"\s+", " ", value).strip()


def discover_book_claims(config: BookConfig, state: StateStore, manifest: SourceManifest) -> list[SourceClaim]:
    """Structural, mathematical-prose, then cross-book-usage discovery passes.

    TeX is used only for navigation and candidate enumeration.  Every location
    remains explicitly marked for PDF verification because the PDF is the sole
    mathematical authority.
    """
    candidates: list[tuple[SourceClaim, str | None]] = []
    label_owner: dict[str, SourceClaim] = {}
    all_text: dict[str, str] = {}
    for chapter in manifest.chapters:
        path = Path(chapter.tex_path)
        if not path.is_file():
            continue
        text = path.read_text(encoding="utf-8", errors="replace")
        all_text[chapter.id] = text
        for ordinal, match in enumerate(ENV_RE.finditer(text), 1):
            environment = match.group(1).lower().rstrip("*")
            title, body = match.group(2), match.group(3)
            label_match = LABEL_RE.search(body)
            label = label_match.group(1) if label_match else None
            digest = hashlib.sha256(f"{chapter.id}|{environment}|{ordinal}|{body}".encode()).hexdigest()[:16]
            claim_id = f"SRC-{chapter.id}-{digest}"
            kind = "numbered_equation" if environment == "equation" else environment
            if kind in {"theorem", "lemma", "proposition", "corollary"}: kind = "named_result"
            is_proof_exercise = bool(re.search(r"\b(prove|show|verify|derive|establish|demonstrate)\b", body, re.IGNORECASE)) \
                if environment == "exercise" else None
            decision = (
                CoverageDecision.DEFER if environment == "exercise" and is_proof_exercise
                else CoverageDecision.OMIT if environment == "exercise"
                else CoverageDecision.FORMALIZE
            )
            status = CoverageStatus.OUT_OF_SCOPE if decision == CoverageDecision.OMIT else CoverageStatus.MISSING
            citations = CITE_RE.findall(body)
            if citations and environment in {"theorem", "lemma", "proposition", "corollary"}:
                kind = "external_result"
            location = f"PDF chapter {chapter.id}"
            if chapter.page_start or chapter.page_end:
                location += f", pages {chapter.page_start or '?'}–{chapter.page_end or '?'}"
            location += "; verify exact page against authoritative PDF"
            claim = SourceClaim(
                id=claim_id, book_id=config.book_id, chapter_id=chapter.id,
                kind=kind, claim=_plain_tex((title + ". " if title else "") + body),
                pdf_location=location, tex_location=f"{path}:{text.count(chr(10), 0, match.start()) + 1}",
                decision=decision, coverage_status=status,
                exercise_is_proof_question=is_proof_exercise,
                evidence_hash=sha256_json({"environment": environment, "body": body}),
            )
            candidates.append((claim, label))
            if label: label_owner[label] = claim
        # Bibliographic prose is recorded but is not automatically made a proposition.
        for keys in CITE_RE.findall(text):
            for key in (item.strip() for item in keys.split(",") if item.strip()):
                claim_id = f"CITE-{chapter.id}-{hashlib.sha256(key.encode()).hexdigest()[:12]}"
                candidates.append((SourceClaim(
                    id=claim_id, book_id=config.book_id, chapter_id=chapter.id,
                    kind="bibliographic", claim=f"Bibliographic citation {key}",
                    pdf_location=f"PDF chapter {chapter.id}; verify citation text against PDF",
                    tex_location=str(path), decision=CoverageDecision.OMIT,
                    coverage_status=CoverageStatus.OUT_OF_SCOPE,
                    evidence_hash=sha256_json(key),
                ), None))

    # Cross-book usage pass: a later reference makes the source claim load-bearing.
    chapter_order = {chapter.id: index for index, chapter in enumerate(manifest.chapters)}
    for using_chapter, text in all_text.items():
        for label in REF_RE.findall(text):
            owner = label_owner.get(label)
            if owner and using_chapter != owner.chapter_id:
                owner.later_uses.append(f"chapter {using_chapter}: {label}")
                if chapter_order.get(using_chapter, 0) >= chapter_order.get(owner.chapter_id or "", 0):
                    owner.load_bearing = True
                    if owner.kind == "exercise":
                        owner.decision = CoverageDecision.FORMALIZE
                        owner.coverage_status = CoverageStatus.MISSING
                    if owner.kind == "external_result":
                        owner.external_used_downstream = True
                        owner.decision = CoverageDecision.FORMALIZE

    unique: dict[str, SourceClaim] = {}
    for claim, _ in candidates:
        unique[claim.id] = claim
    claims = list(unique.values())
    for claim in claims: state.save_source_claim(claim)
    state.event(config.book_id, None, "source_discovery", {
        "structural_candidates": len(claims),
        "mathematical_claims": sum(item.kind not in {"bibliographic", "historical", "motivational"} for item in claims),
        "cross_book_uses": sum(len(item.later_uses) for item in claims),
    })
    return claims
