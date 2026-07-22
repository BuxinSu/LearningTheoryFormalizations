#!/usr/bin/env python3
"""Reconcile the current placeholder scan with all located gap ledgers.

The project records refer to ``TranslationReport/forward_sorry_ledger.md``,
but that file is not inside the Lean project root.  The companion
documentation is stored below the sibling directory
``High_Dimensional_Probability``.  This script searches the exact project and
sibling locations, requires one unambiguous forward ledger, hashes every
consulted document, and compares its numeric/status claims with the current
V3 scan and the in-project authoritative Appendix summary.
"""

from __future__ import annotations

import argparse
import hashlib
import io
import json
import re
import tempfile
from collections.abc import Callable
from contextlib import redirect_stdout
from dataclasses import dataclass, replace
from pathlib import Path


ROOT = Path(__file__).resolve().parents[3]
LOGS = ROOT / "HighDimensionalProbability" / "Verification" / "logs"
DEFAULT_V3 = LOGS / "v3_library.json"
DEFAULT_OUTPUT = LOGS / "v3_ledger_reconciliation.txt"
DEFAULT_FORWARD_SNAPSHOT = (
    LOGS / "recert_v3_forward_sorry_ledger_snapshot.md"
)

PROJECT_FORWARD = ROOT / "TranslationReport" / "forward_sorry_ledger.md"
SIBLING_DOC_ROOT = ROOT.parent / "High_Dimensional_Probability"
SIBLING_FORWARD = (
    SIBLING_DOC_ROOT / "TranslationReport" / "forward_sorry_ledger.md"
)
REVIEW_NOTES = (
    ROOT / "HighDimensionalProbability" / "Verification" / "REVIEW_NOTES.md"
)
CORRECTION_LEDGER = (
    ROOT / "HighDimensionalProbability" / "Verification" / "CORRECTION_LEDGER.md"
)
FINAL_CORRECTION_REPORT = (
    ROOT
    / "HighDimensionalProbability"
    / "Verification"
    / "FINAL_CORRECTION_REPORT.md"
)
APPENDIX_SUMMARY = (
    ROOT
    / "HighDimensionalProbability"
    / "APPENDIX_SUMMARY.md"
)


@dataclass(frozen=True)
class ForwardClaims:
    category_a: int
    category_b: int
    total: int
    whole_category_a: int
    whole_category_b: int
    whole_category_c: int
    whole_category_d: int
    registry_total: int
    registry_faithful: int
    registry_strengthened: int
    registry_skipped: int


@dataclass(frozen=True)
class AppendixStatus:
    total: int
    faithful: int
    strengthened: int
    skipped: int


def sha256_bytes(data: bytes) -> str:
    return hashlib.sha256(data).hexdigest()


def _display_path(path: Path) -> str:
    try:
        return str(path.relative_to(ROOT))
    except ValueError:
        try:
            return str(Path("..") / path.relative_to(ROOT.parent))
        except ValueError:
            return str(path)


def _read_utf8(path: Path, *, label: str) -> tuple[bytes, str]:
    data = path.read_bytes()
    try:
        return data, data.decode("utf-8")
    except UnicodeDecodeError as error:
        raise ValueError(f"{label} is not valid UTF-8: {path}") from error


def _must_match_exactly_once(
    pattern: str, text: str, *, label: str
) -> re.Match[str]:
    matches = list(
        re.finditer(pattern, text, flags=re.MULTILINE | re.DOTALL)
    )
    if len(matches) != 1:
        raise ValueError(
            f"expected exactly one {label}, found {len(matches)}"
        )
    return matches[0]


def _locate_exactly_one(
    candidates: tuple[Path, ...], *, label: str
) -> Path:
    located = [path for path in candidates if path.is_file()]
    if len(located) != 1:
        rendered = ", ".join(str(path) for path in located) or "(none)"
        raise ValueError(
            f"expected exactly one located {label}, found {rendered}"
        )
    return located[0]


def _parse_forward_claims(text: str) -> ForwardClaims:
    """Parse the ledger's explicitly labelled current census and registry.

    Historical counts are intentionally allowed elsewhere in the document,
    so both expressions anchor on the prose that introduces the *current*
    claims rather than searching for an unqualified number.
    """

    _must_match_exactly_once(
        r"There are \*\*zero open category-C or category-D deferrals\*\* "
        r"and no\s+`FORWARD-SORRY-NNN` declarations in Chapters 1--9\.",
        text,
        label="forward-ledger zero-open-C/D statement",
    )
    counts = _must_match_exactly_once(
        r"current executable-placeholder census is \*\*"
        r"(?P<category_a>\d+) category A \+ "
        r"(?P<category_b>\d+) category B\s*=\s*"
        r"(?P<total>\d+) literal `sorry` proof occurrences\*\*",
        text,
        label="forward-ledger current executable count",
    )
    whole = _must_match_exactly_once(
        r"^\| \*\*Whole source tree\*\* "
        r"\| \*\*(?P<category_a>\d+)\*\* "
        r"\| \*\*(?P<category_b>\d+)\*\* "
        r"\| \*\*(?P<category_c>\d+)\*\* "
        r"\| \*\*(?P<category_d>\d+)\*\* \|$",
        text,
        label="forward-ledger whole-source A/B/C/D row",
    )
    registry = _must_match_exactly_once(
        r"Appendix registry has a\s+different, semantic denominator:\s*\*\*"
        r"(?P<total>\d+) registered targets\s*=\s*"
        r"(?P<faithful>\d+) source-faithful\s+proved\s*\+\s*"
        r"(?P<strengthened>\d+) assumption-strengthened proved\s*\+\s*"
        r"(?P<skipped>\d+) skipped\*\*",
        text,
        label="forward-ledger current registry split",
    )
    return ForwardClaims(
        category_a=int(counts.group("category_a")),
        category_b=int(counts.group("category_b")),
        total=int(counts.group("total")),
        whole_category_a=int(whole.group("category_a")),
        whole_category_b=int(whole.group("category_b")),
        whole_category_c=int(whole.group("category_c")),
        whole_category_d=int(whole.group("category_d")),
        registry_total=int(registry.group("total")),
        registry_faithful=int(registry.group("faithful")),
        registry_strengthened=int(registry.group("strengthened")),
        registry_skipped=int(registry.group("skipped")),
    )


def _forward_claims_stale(
    claims: ForwardClaims,
    *,
    current_sorries: int,
    appendix_sorries: int,
) -> bool:
    current_category_a = current_sorries - appendix_sorries
    registry_sum = (
        claims.registry_faithful
        + claims.registry_strengthened
        + claims.registry_skipped
    )
    return (
        current_category_a < 0
        or claims.category_a != current_category_a
        or claims.category_b != appendix_sorries
        or claims.total != current_sorries
        or claims.category_a + claims.category_b != claims.total
        or claims.whole_category_a != claims.category_a
        or claims.whole_category_b != claims.category_b
        or claims.whole_category_c != 0
        or claims.whole_category_d != 0
        or (
            claims.whole_category_a
            + claims.whole_category_b
            + claims.whole_category_c
            + claims.whole_category_d
            != claims.total
        )
        or (
            claims.whole_category_a,
            claims.whole_category_b,
            claims.whole_category_c,
            claims.whole_category_d,
        )
        != (228, 0, 0, 0)
        or claims.registry_total != 14
        or registry_sum != claims.registry_total
        or (
            claims.registry_faithful,
            claims.registry_strengthened,
            claims.registry_skipped,
        )
        != (14, 0, 0)
    )


def _parse_appendix_status(text: str) -> AppendixStatus:
    delimiter = "\n## Historical 17-target reconstruction record"
    if text.count(delimiter) != 1:
        raise ValueError(
            "expected exactly one Appendix current-status delimiter"
        )
    current_block = text.split(delimiter, 1)[0]
    if current_block.count("# HDP Appendix active registry") != 1:
        raise ValueError(
            "expected exactly one Appendix current-status heading"
        )
    active = _must_match_exactly_once(
        r"\A# HDP Appendix active registry\s+Date: 2026-07-20\s+"
        r"The active Appendix registry contains exactly "
        r"\*\*(?P<faithful>\d+)/(?P<total>\d+) source-faithful proved\s+"
        r"targets\*\*\.",
        current_block,
        label="anchored Appendix active-registry heading",
    )
    projection = _must_match_exactly_once(
        r"The active whole-book projection is \*\*(?P<total>\d+) = "
        r"(?P<core>\d+) core \+ (?P<appendix>\d+) Appendix \+ "
        r"(?P<deferred>\d+)\s+deferred/source-limited\*\*\.",
        current_block,
        label="Appendix active whole-book projection",
    )
    active_rows = re.findall(
        r"^\| \d+ \| [^|\n]+ \| `[^|\n]+` "
        r"\| SOURCE-FAITHFUL PROVED \|$",
        current_block,
        flags=re.MULTILINE,
    )
    removal_rows = re.findall(
        r"^\| `APPENDIX-UNRESOLVED-00[123]`:[^|\n]+ "
        r"\| \*\*RESOLVED BY REMOVAL\.\*\*",
        current_block,
        flags=re.MULTILINE,
    )
    status = AppendixStatus(
        total=int(active.group("total")),
        faithful=int(active.group("faithful")),
        strengthened=0,
        skipped=0,
    )
    if (
        status != AppendixStatus(14, 14, 0, 0)
        or status.faithful + status.strengthened + status.skipped
        != status.total
        or len(active_rows) != 14
        or len(removal_rows) != 3
        or (
            int(projection.group("total")),
            int(projection.group("core")),
            int(projection.group("appendix")),
            int(projection.group("deferred")),
        )
        != (835, 769, 66, 0)
    ):
        raise ValueError(
            "Appendix active registry is not exact 14=14+0+0 with "
            "835=769+66+0 current projection and three removed scopes"
        )
    return status


def _require_review_notes_status(text: str) -> None:
    match = _must_match_exactly_once(
        r"^\| Placeholder scan \| Current lexer/kernel reconciliation finds "
        r"exactly \*\*(?P<total>\d+) executable `sorry` proofs\*\*, "
        r"all marked Exercise leaves in (?P<files>\d+) files; Appendix has "
        r"(?P<appendix>zero|\d+)\. \| [^|\n]+ \|$",
        text,
        label="REVIEW_NOTES current placeholder fixed-point row",
    )
    appendix = (
        0
        if match.group("appendix") == "zero"
        else int(match.group("appendix"))
    )
    if (
        int(match.group("total")) != 228
        or int(match.group("files")) != 46
        or appendix != 0
    ):
        raise ValueError(
            "REVIEW_NOTES current placeholder row is not 228/46/0"
        )


def _require_correction_ledger_status(text: str) -> None:
    _must_match_exactly_once(
        r"^\| `FIXED` \| [^|\n]*\bV3-F2\b[^|\n]* \| [^|\n]* \| "
        r"[^|\n]*reconciled the live placeholder/registry records;"
        r"[^|\n]* \|$",
        text,
        label="CORRECTION_LEDGER V3 resolution anchor",
    )
    match = _must_match_exactly_once(
        r"Static reconciliation finds exactly (?P<total>\d+) executable "
        r"`sorry` proofs,\s+all in the intentionally deferred "
        r"non-load-bearing exercise leaves; Appendix\s+source has "
        r"(?P<appendix>zero|\d+) `sorry`",
        text,
        label="CORRECTION_LEDGER current placeholder anchor",
    )
    appendix = (
        0
        if match.group("appendix") == "zero"
        else int(match.group("appendix"))
    )
    if int(match.group("total")) != 228 or appendix != 0:
        raise ValueError(
            "CORRECTION_LEDGER current placeholder anchor is not 228/0"
        )


def _require_final_correction_status(text: str) -> None:
    start = "\n### 3.1 Exact active counts\n"
    end = "\n## 6. Coverage boundary\n"
    if not text.startswith("# Final correction report\n"):
        raise ValueError(
            "FINAL_CORRECTION_REPORT lacks its authoritative heading"
        )
    if text.count(start) != 1 or text.count(end) != 1:
        raise ValueError(
            "expected exactly one FINAL_CORRECTION_REPORT active-counts "
            "section"
        )
    current_block = text.split(start, 1)[1].split(end, 1)[0]
    registry = _must_match_exactly_once(
        r"^\| Active Appendix registry \| "
        r"\*\*(?P<faithful>\d+)/(?P<total>\d+) "
        r"source-faithful proved targets\*\* \|$",
        current_block,
        label="FINAL_CORRECTION_REPORT current Appendix registry anchor",
    )
    placeholders = _must_match_exactly_once(
        r"^\| Ledgered Exercise `sorry` proofs \| "
        r"\*\*(?P<total>\d+) in (?P<files>\d+) files\*\* \|$",
        current_block,
        label="FINAL_CORRECTION_REPORT current placeholder anchor",
    )
    if (
        int(registry.group("faithful")) != 14
        or int(registry.group("total")) != 14
        or int(placeholders.group("total")) != 228
        or int(placeholders.group("files")) != 46
    ):
        raise ValueError(
            "FINAL_CORRECTION_REPORT current anchors are not 228/46 "
            "and 14/14"
        )


def analyze(
    v3_path: Path,
    output_path: Path,
    *,
    project_forward: Path = PROJECT_FORWARD,
    sibling_forward: Path = SIBLING_FORWARD,
    forward_snapshot: Path = DEFAULT_FORWARD_SNAPSHOT,
    review_notes: Path = REVIEW_NOTES,
    correction_ledger: Path = CORRECTION_LEDGER,
    final_correction_report: Path = FINAL_CORRECTION_REPORT,
    appendix_summary: Path = APPENDIX_SUMMARY,
) -> int:
    payload = json.loads(v3_path.read_text(encoding="utf-8"))
    summary = payload["summary"]
    by_pattern = summary["by_pattern"]
    current_sorries = int(by_pattern["v3.sorry"]["code"])
    exercise_markers = int(
        by_pattern["v3.exercise_sorry_marker"]["raw"]
    )
    appendix_sorries = sum(
        1
        for hit in payload["hits"]
        if hit["pattern_id"] == "v3.sorry"
        and hit["in_code"]
        and (
            hit["path"] == "HighDimensionalProbability/Appendix.lean"
            or hit["path"].startswith(
                "HighDimensionalProbability/Appendix/"
            )
        )
    )

    forward_path = _locate_exactly_one(
        (project_forward, sibling_forward),
        label="forward-sorry ledger",
    )
    forward_bytes, forward_text = _read_utf8(
        forward_path, label="live forward-sorry ledger"
    )
    snapshot_bytes, _ = _read_utf8(
        forward_snapshot, label="preserved forward-sorry ledger snapshot"
    )
    if forward_bytes != snapshot_bytes:
        raise ValueError(
            "live forward-sorry ledger differs byte-for-byte from "
            f"Verification snapshot: {_display_path(forward_snapshot)}"
        )
    forward_claims = _parse_forward_claims(forward_text)

    appendix_bytes, appendix_text = _read_utf8(
        appendix_summary, label="Appendix summary"
    )
    appendix_status = _parse_appendix_status(appendix_text)

    review_bytes, review_text = _read_utf8(
        review_notes, label="REVIEW_NOTES"
    )
    _require_review_notes_status(review_text)
    correction_bytes, correction_text = _read_utf8(
        correction_ledger, label="CORRECTION_LEDGER"
    )
    _require_correction_ledger_status(correction_text)
    final_bytes, final_text = _read_utf8(
        final_correction_report, label="FINAL_CORRECTION_REPORT"
    )
    _require_final_correction_status(final_text)

    forward_stale = _forward_claims_stale(
        forward_claims,
        current_sorries=current_sorries,
        appendix_sorries=appendix_sorries,
    )
    stale_records_found = forward_stale

    consulted = (
        (review_notes, review_bytes),
        (correction_ledger, correction_bytes),
        (final_correction_report, final_bytes),
        (appendix_summary, appendix_bytes),
        (forward_snapshot, snapshot_bytes),
        (forward_path, forward_bytes),
    )
    lines = [
        "V3 LIVE-LEDGER RECONCILIATION",
        "=============================",
        f"verdict: {'STALE_RECORDS_FOUND' if stale_records_found else 'PASS'}",
        f"project_root_forward_ledger_exists: {project_forward.is_file()}",
        f"sibling_document_forward_ledger_exists: {sibling_forward.is_file()}",
        f"located_forward_ledger: {_display_path(forward_path)}",
        f"forward_ledger_snapshot: {_display_path(forward_snapshot)}",
        "forward_snapshot_matches_live: true",
        (
            "manifest_note: the located forward ledger is outside the "
            "Lean-project source manifest; its exact bytes are preserved "
            "under Verification and both SHA-256 values are recorded below"
        ),
        "",
        "[current source measurement]",
        f"current_code_sorries: {current_sorries}",
        (
            "current_category_a_sorries: "
            f"{current_sorries - appendix_sorries}"
        ),
        f"current_appendix_code_sorries: {appendix_sorries}",
        f"current_exercise_marker_occurrences: {exercise_markers}",
        (
            "current_appendix_registry: "
            f"{appendix_status.total} total = "
            f"{appendix_status.faithful} source-faithful + "
            f"{appendix_status.strengthened} assumption-strengthened + "
            f"{appendix_status.skipped} skipped"
        ),
        "",
        "[located forward-ledger claims]",
        f"claimed_category_a_sorries: {forward_claims.category_a}",
        f"claimed_category_b_sorries: {forward_claims.category_b}",
        f"claimed_code_sorries: {forward_claims.total}",
        (
            "claimed_whole_source_row: "
            f"{forward_claims.whole_category_a} A + "
            f"{forward_claims.whole_category_b} B + "
            f"{forward_claims.whole_category_c} C + "
            f"{forward_claims.whole_category_d} D"
        ),
        "claimed_open_category_c_or_d_deferrals: 0",
        (
            "claimed_appendix_registry: "
            f"{forward_claims.registry_total} total = "
            f"{forward_claims.registry_faithful} source-faithful + "
            f"{forward_claims.registry_strengthened} "
            "assumption-strengthened + "
            f"{forward_claims.registry_skipped} skipped"
        ),
        f"forward_ledger_stale: {str(forward_stale).lower()}",
        "",
        "[other live records]",
        "review_notes_current_228_appendix_zero: true",
        "correction_ledger_v3_resolution_228_appendix_zero: true",
        "final_correction_report_current_228_46_14_14: true",
        "appendix_summary_current_14_14_0_0_three_removed: true",
        "",
        "[consulted document SHA-256]",
    ]
    lines.extend(
        f"{_display_path(path)}\t{sha256_bytes(data)}"
        for path, data in consulted
    )
    output_path.parent.mkdir(parents=True, exist_ok=True)
    output_path.write_text("\n".join(lines) + "\n", encoding="utf-8")
    print("\n".join(lines))
    return 1 if stale_records_found else 0


def self_test() -> int:
    def expect_rejected(label: str, action: Callable[[], object]) -> None:
        try:
            action()
        except ValueError:
            return
        raise AssertionError(f"accepted planted false-pass case: {label}")

    forward_sample = "\n".join(
        (
            "There are **zero open category-C or category-D deferrals** and no",
            "`FORWARD-SORRY-NNN` declarations in Chapters 1--9.",
            "",
            "The current executable-placeholder census is **228 category A + "
            "0 category B",
            "= 228 literal `sorry` proof occurrences**. The Appendix registry "
            "has a",
            "different, semantic denominator: **14 registered targets = "
            "14 source-faithful",
            "proved + 0 assumption-strengthened proved + 0 skipped**.",
            "",
            "| Scope | Literal A | Literal B | C | D |",
            "|---|---:|---:|---:|---:|",
            "| **Whole source tree** | **228** | **0** | **0** | **0** |",
            "",
        )
    )
    expected_forward = ForwardClaims(
        category_a=228,
        category_b=0,
        total=228,
        whole_category_a=228,
        whole_category_b=0,
        whole_category_c=0,
        whole_category_d=0,
        registry_total=14,
        registry_faithful=14,
        registry_strengthened=0,
        registry_skipped=0,
    )
    parsed = _parse_forward_claims(forward_sample)
    if parsed != expected_forward:
        raise AssertionError(f"unexpected current-ledger parse: {parsed!r}")
    if _forward_claims_stale(
        parsed, current_sorries=228, appendix_sorries=0
    ):
        raise AssertionError("accepted forward claims were classified stale")
    historical = (
        forward_sample
        + "\nThe frozen ledger reported 231 A + 15 B = 246 and "
        + "13 proved + 4 unresolved."
    )
    if _parse_forward_claims(historical) != parsed:
        raise AssertionError("historical prose changed the current-ledger parse")
    if not _forward_claims_stale(
        replace(parsed, registry_total=999),
        current_sorries=228,
        appendix_sorries=0,
    ):
        raise AssertionError("ignored planted Appendix registry-total drift")
    if not _forward_claims_stale(
        replace(parsed, category_b=1),
        current_sorries=228,
        appendix_sorries=1,
    ):
        raise AssertionError("ignored planted A+B category arithmetic drift")
    if not _forward_claims_stale(
        replace(parsed, whole_category_c=1),
        current_sorries=228,
        appendix_sorries=0,
    ):
        raise AssertionError("ignored planted category-C whole-row drift")
    expect_rejected(
        "nonzero forward C/D prose",
        lambda: _parse_forward_claims(
            forward_sample.replace(
                "zero open category-C or category-D deferrals",
                "one open category-C or category-D deferral",
            )
        ),
    )

    appendix_sample = "\n".join(
        (
            "# HDP Appendix active registry",
            "",
            "Date: 2026-07-20",
            "",
            "The active Appendix registry contains exactly **14/14 "
            "source-faithful proved",
            "targets**.",
            "",
            "| # | Book target | Active declaration | Status |",
            "|---:|---|---|---|",
            *(
                f"| {index} | Target {index} | `HDP.target_{index}` "
                "| SOURCE-FAITHFUL PROVED |"
                for index in range(1, 15)
            ),
            "",
            "| Former scope | Active disposition |",
            "|---|---|",
            "| `APPENDIX-UNRESOLVED-001`: Q1 "
            "| **RESOLVED BY REMOVAL.** deleted |",
            "| `APPENDIX-UNRESOLVED-002`: Q2 "
            "| **RESOLVED BY REMOVAL.** deleted |",
            "| `APPENDIX-UNRESOLVED-003`: Q3 "
            "| **RESOLVED BY REMOVAL.** deleted |",
            "",
            "The active whole-book projection is **835 = 769 core + 66 "
            "Appendix + 0",
            "deferred/source-limited**.",
            "",
            "## Historical 17-target reconstruction record",
            "",
            "Historical detail.",
        )
    )
    if _parse_appendix_status(appendix_sample) != AppendixStatus(
        14, 14, 0, 0
    ):
        raise AssertionError("unexpected Appendix current-status parse")
    expect_rejected(
        "historical-only Appendix phrases",
        lambda: _parse_appendix_status(
            "\n".join(
                (
                    "HISTORICAL: 14 registered targets",
                    "14 source-faithful PROVED",
                    "0 assumption-strengthened PROVED",
                    "0 SKIPPED",
                    "Q4, the Brownian expected-running-maximum formula, "
                    "is fully proved",
                    "HDP.Chapter7.brownianReflectionPrinciple_external",
                    "CURRENT: 99 registered targets and Q4 unresolved",
                )
            )
        ),
    )
    expect_rejected(
        "duplicate contradictory Appendix current registry",
        lambda: _parse_appendix_status(
            appendix_sample.replace(
                "The active Appendix registry contains exactly **14/14",
                "The active Appendix registry contains exactly **14/14\n"
                "The active Appendix registry contains exactly **99/99",
            )
        ),
    )

    review_sample = (
        "| Placeholder scan | Current lexer/kernel reconciliation finds "
        "exactly **228 executable `sorry` proofs**, all marked Exercise "
        "leaves in 46 files; Appendix has zero. | V3/V4 evidence |"
    )
    correction_sample = (
        "| `FIXED` | V2-F2, V3-F2 | 1 confirmed | Wired imports; reconciled "
        "the live placeholder/registry records; repaired evidence. |\n\n"
        "Static reconciliation finds exactly 228 executable `sorry` proofs,\n"
        "all in the intentionally deferred non-load-bearing exercise leaves; "
        "Appendix\nsource has zero `sorry`, `admit`, or `axiom` constructs.\n"
    )
    final_sample = "\n".join(
        (
            "# Final correction report",
            "",
            "## Authoritative disposition",
            "",
            "Current post-removal scope.",
            "",
            "### 3.1 Exact active counts",
            "",
            "| Measurement | Active value |",
            "|---|---:|",
            "| Ledgered Exercise `sorry` proofs | **228 in 46 files** |",
            "| Active Appendix registry | "
            "**14/14 source-faithful proved targets** |",
            "",
            "## 6. Coverage boundary",
            "",
            "Every retained mapped item is covered.",
            "",
        )
    )
    _require_review_notes_status(review_sample)
    _require_correction_ledger_status(correction_sample)
    _require_final_correction_status(final_sample)
    expect_rejected(
        "empty REVIEW_NOTES",
        lambda: _require_review_notes_status(""),
    )
    expect_rejected(
        "stale REVIEW_NOTES count",
        lambda: _require_review_notes_status(
            review_sample.replace("228 executable", "999 executable")
        ),
    )
    expect_rejected(
        "duplicate REVIEW_NOTES current row",
        lambda: _require_review_notes_status(
            review_sample + "\n" + review_sample
        ),
    )
    expect_rejected(
        "empty CORRECTION_LEDGER",
        lambda: _require_correction_ledger_status(""),
    )
    expect_rejected(
        "CORRECTION_LEDGER missing V3 resolution",
        lambda: _require_correction_ledger_status(
            correction_sample.replace("V3-F2", "V2-F2")
        ),
    )
    expect_rejected(
        "empty FINAL_CORRECTION_REPORT",
        lambda: _require_final_correction_status(""),
    )
    expect_rejected(
        "stale FINAL_CORRECTION_REPORT registry",
        lambda: _require_final_correction_status(
            final_sample.replace(
                "14/14 source-faithful proved",
                "99/99 source-faithful proved",
            )
        ),
    )
    expect_rejected(
        "stale FINAL_CORRECTION_REPORT placeholder files",
        lambda: _require_final_correction_status(
            final_sample.replace("228 in 46 files", "228 in 99 files")
        ),
    )

    with tempfile.TemporaryDirectory(prefix="v3-ledger-locator-") as temporary:
        base = Path(temporary)
        first = base / "first.md"
        second = base / "second.md"
        try:
            _locate_exactly_one(
                (first, second), label="planted locator record"
            )
        except ValueError:
            pass
        else:
            raise AssertionError("locator accepted zero live records")
        first.write_text("first\n", encoding="utf-8")
        if (
            _locate_exactly_one(
                (first, second), label="planted locator record"
            )
            != first
        ):
            raise AssertionError("locator did not select the unique record")
        second.write_text("second\n", encoding="utf-8")
        try:
            _locate_exactly_one(
                (first, second), label="planted locator record"
            )
        except ValueError:
            pass
        else:
            raise AssertionError("locator accepted ambiguous live records")
    with tempfile.TemporaryDirectory(
        prefix="v3-ledger-analyze-"
    ) as temporary:
        base = Path(temporary)
        v3_fixture = base / "v3.json"
        output = base / "reconciliation.txt"
        forward = base / "forward_sorry_ledger.md"
        snapshot = base / "forward_sorry_ledger.snapshot.md"
        missing_forward = base / "missing_forward_sorry_ledger.md"
        review = base / "REVIEW_NOTES.md"
        correction = base / "CORRECTION_LEDGER.md"
        final = base / "FINAL_CORRECTION_REPORT.md"
        appendix = base / "APPENDIX_SUMMARY.md"

        def write_v3_fixture(code_sorries: int) -> None:
            v3_fixture.write_text(
                json.dumps(
                    {
                        "summary": {
                            "by_pattern": {
                                "v3.sorry": {"code": code_sorries},
                                "v3.exercise_sorry_marker": {"raw": 234},
                            }
                        },
                        "hits": [],
                    }
                ),
                encoding="utf-8",
            )

        write_v3_fixture(228)
        forward.write_text(forward_sample, encoding="utf-8")
        snapshot.write_text(forward_sample, encoding="utf-8")
        review.write_text(review_sample, encoding="utf-8")
        correction.write_text(correction_sample, encoding="utf-8")
        final.write_text(final_sample, encoding="utf-8")
        appendix.write_text(appendix_sample, encoding="utf-8")
        with redirect_stdout(io.StringIO()):
            pass_exit = analyze(
                v3_fixture,
                output,
                project_forward=forward,
                sibling_forward=missing_forward,
                forward_snapshot=snapshot,
                review_notes=review,
                correction_ledger=correction,
                final_correction_report=final,
                appendix_summary=appendix,
            )
        if pass_exit != 0 or "verdict: PASS" not in output.read_text(
            encoding="utf-8"
        ):
            raise AssertionError("analyze rejected the matching control fixture")

        write_v3_fixture(227)
        with redirect_stdout(io.StringIO()):
            stale_exit = analyze(
                v3_fixture,
                output,
                project_forward=forward,
                sibling_forward=missing_forward,
                forward_snapshot=snapshot,
                review_notes=review,
                correction_ledger=correction,
                final_correction_report=final,
                appendix_summary=appendix,
            )
        if stale_exit == 0:
            raise AssertionError(
                "analyze accepted a stale current placeholder count"
            )
        if "verdict: STALE_RECORDS_FOUND" not in output.read_text(
            encoding="utf-8"
        ):
            raise AssertionError(
                "stale analyze fixture did not record its failure verdict"
            )
        snapshot.write_text(
            forward_sample + "planted drift\n", encoding="utf-8"
        )
        expect_rejected(
            "live/snapshot byte drift",
            lambda: analyze(
                v3_fixture,
                output,
                project_forward=forward,
                sibling_forward=missing_forward,
                forward_snapshot=snapshot,
                review_notes=review,
                correction_ledger=correction,
                final_correction_report=final,
                appendix_summary=appendix,
            ),
        )
    print("PASS: V3 live-ledger fail-closed parser/analyzer self-test")
    return 0


def _resolve(path: Path) -> Path:
    return path if path.is_absolute() else ROOT / path


def main() -> int:
    parser = argparse.ArgumentParser()
    parser.add_argument("--self-test", action="store_true")
    parser.add_argument(
        "--v3-json",
        type=Path,
        default=DEFAULT_V3.relative_to(ROOT),
    )
    parser.add_argument(
        "--output",
        type=Path,
        default=DEFAULT_OUTPUT.relative_to(ROOT),
    )
    args = parser.parse_args()
    if args.self_test:
        return self_test()
    return analyze(_resolve(args.v3_json), _resolve(args.output))


if __name__ == "__main__":
    raise SystemExit(main())
