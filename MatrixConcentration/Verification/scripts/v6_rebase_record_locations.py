#!/usr/bin/env python3
"""Rebase V6's human-reviewed source locations after nonsemantic line drift.

This maintenance helper changes only source-coordinate fields:

* the first ``source: File.lean:line[-line]`` reference in each Tier-B row;
* ``application_site`` for every Tier-C library or named-application row.

All judgments, rationales, obligation metadata, witness names, and evidence
methods are preserved byte-for-byte at the field level.  Tier-B locations are
derived from the endpoint declarations.  Tier-C locations are accepted only
when the audited endpoint occurs inside the recorded caller's current
declaration body; if a caller uses it more than once, the old location is used
only as a nearest-occurrence tie-breaker.
"""

from __future__ import annotations

import argparse
import csv
import re
import sys
from pathlib import Path


SCRIPT = Path(__file__).resolve()
VERIFICATION = SCRIPT.parent.parent
PACKAGE_ROOT = VERIFICATION.parent
CURATION = VERIFICATION / "curation"

TIER_B_FILES = [
    CURATION / f"v6_tier_b_chapter_{chapter}.tsv"
    for chapter in range(1, 9)
]
TIER_C_FILE = CURATION / "v6_tier_c_evidence.tsv"

SOURCE_REF_RE = re.compile(
    r"\bsource:\s*(?:MatrixConcentration/)?"
    r"(?P<path>[A-Za-z0-9_./-]+\.lean):"
    r"(?P<start>[0-9]+)(?:-(?P<end>[0-9]+))?"
)
SITE_RE = re.compile(
    r"^(?P<prefix>MatrixConcentration/)?"
    r"(?P<path>[A-Za-z0-9_./-]+\.lean):(?P<line>[0-9]+)$"
)
ANY_DECL_RE = re.compile(
    r"^\s*(?:@\[[^\]]+\]\s*)*"
    r"(?:(?:private|protected|noncomputable|unsafe)\s+)*"
    r"(?:theorem|lemma|def|abbrev|opaque)\s+"
    r"(?P<name>[^\s({:\[]+)(?=$|[\s({:\[])"
)


def declaration_re(name: str) -> re.Pattern[str]:
    return re.compile(
        r"^\s*(?:@\[[^\]]+\]\s*)*"
        r"(?:(?:private|protected|noncomputable|unsafe)\s+)*"
        r"(?:theorem|lemma|def|abbrev|opaque)\s+"
        + re.escape(name)
        + r"(?=$|[\s({:\[])"
    )


def identifier_re(name: str) -> re.Pattern[str]:
    return re.compile(
        r"(?<![A-Za-z0-9_'])" + re.escape(name) + r"(?![A-Za-z0-9_'])"
    )


def read_tsv(path: Path) -> tuple[list[str], list[dict[str, str]]]:
    with path.open(newline="", encoding="utf-8") as handle:
        reader = csv.DictReader(handle, delimiter="\t")
        return list(reader.fieldnames or []), list(reader)


def write_tsv(
    path: Path,
    fields: list[str],
    rows: list[dict[str, str]],
) -> None:
    with path.open("w", newline="", encoding="utf-8") as handle:
        writer = csv.DictWriter(
            handle, fieldnames=fields, delimiter="\t", lineterminator="\n"
        )
        writer.writeheader()
        writer.writerows(rows)


def source_index() -> dict[str, list[tuple[Path, int]]]:
    index: dict[str, list[tuple[Path, int]]] = {}
    for path in sorted(PACKAGE_ROOT.glob("*.lean")):
        for line_number, line in enumerate(
            path.read_text(encoding="utf-8").splitlines(), 1
        ):
            match = ANY_DECL_RE.match(line)
            if match is not None:
                index.setdefault(match.group("name"), []).append(
                    (path, line_number)
                )
    return index


def caller_span(
    path: Path,
    caller: str,
) -> tuple[list[str], int, int]:
    lines = path.read_text(encoding="utf-8").splitlines()
    starts = [
        line_number
        for line_number, line in enumerate(lines, 1)
        if declaration_re(caller).match(line)
    ]
    if len(starts) != 1:
        raise ValueError(
            f"{path.name}: expected one declaration of caller {caller}, "
            f"found {starts}"
        )
    start = starts[0]
    end = len(lines)
    for line_number in range(start + 1, len(lines) + 1):
        if ANY_DECL_RE.match(lines[line_number - 1]):
            end = line_number - 1
            break
    return lines, start, end


def rebase_tier_b(
    index: dict[str, list[tuple[Path, int]]],
    write: bool,
) -> tuple[int, int]:
    rows_seen = 0
    rows_changed = 0
    for path in TIER_B_FILES:
        fields, rows = read_tsv(path)
        for row in rows:
            rows_seen += 1
            declaration = row["declaration"]
            locations = index.get(declaration, [])
            if len(locations) != 1:
                rendered = [
                    f"{p.name}:{line}" for p, line in locations
                ]
                raise ValueError(
                    f"{declaration}: expected one source declaration, "
                    f"found {rendered}"
                )
            source_path, line_number = locations[0]
            old = row["evidence_refs"]
            match = SOURCE_REF_RE.search(old)
            if match is None:
                raise ValueError(
                    f"{declaration}: no primary source reference to rebase"
                )
            replacement = f"source: {source_path.name}:{line_number}"
            new = old[: match.start()] + replacement + old[match.end() :]
            if new != old:
                row["evidence_refs"] = new
                rows_changed += 1
        if write:
            write_tsv(path, fields, rows)
    return rows_seen, rows_changed


def rebase_library_site(
    declaration: str,
    caller_name: str,
    site: str,
) -> str:
    match = SITE_RE.fullmatch(site)
    if match is None:
        raise ValueError(f"{declaration}: malformed application site {site!r}")
    rel = Path(match.group("path"))
    path = PACKAGE_ROOT / rel
    if not path.is_file():
        raise ValueError(f"{declaration}: missing application file {rel}")
    caller = caller_name.rsplit(".", 1)[-1]
    lines, start, end = caller_span(path, caller)
    target = identifier_re(declaration)
    hits = [
        line_number
        for line_number in range(start, end + 1)
        if target.search(lines[line_number - 1])
    ]
    if not hits:
        raise ValueError(
            f"{declaration}: expected at least one use in "
            f"{rel}:{start}-{end} ({caller}), found {hits}"
        )
    old_line = int(match.group("line"))
    distances = {line: abs(line - old_line) for line in hits}
    nearest_distance = min(distances.values())
    nearest = [
        line for line in hits if distances[line] == nearest_distance
    ]
    if len(nearest) != 1:
        raise ValueError(
            f"{declaration}: old site {old_line} is equidistant from "
            f"multiple uses in {rel}:{start}-{end}: {nearest}"
        )
    prefix = match.group("prefix") or ""
    return f"{prefix}{rel}:{nearest[0]}"


def rebase_named_site(
    declaration: str,
    evidence_name: str,
    site: str,
) -> str:
    match = SITE_RE.fullmatch(site)
    if match is None:
        raise ValueError(f"{declaration}: malformed application site {site!r}")
    rel = Path(match.group("path"))
    path = PACKAGE_ROOT / rel
    if not path.is_file():
        raise ValueError(f"{declaration}: missing application file {rel}")
    evidence = evidence_name.rsplit(".", 1)[-1]
    hits = [
        line_number
        for line_number, line in enumerate(
            path.read_text(encoding="utf-8").splitlines(), 1
        )
        if declaration_re(evidence).match(line)
    ]
    if len(hits) != 1:
        raise ValueError(
            f"{declaration}: expected one named application declaration "
            f"{evidence} in {rel}, found {hits}"
        )
    prefix = match.group("prefix") or ""
    return f"{prefix}{rel}:{hits[0]}"


def rebase_tier_c(write: bool) -> tuple[int, int]:
    fields, rows = read_tsv(TIER_C_FILE)
    evidence_rows = 0
    sites_changed = 0
    for row in rows:
        if row["evidence_method"] not in {
            "LIBRARY_CITATION",
            "NAMED_APPLICATION",
        }:
            raise ValueError(
                f"{row['declaration']}: unknown evidence method "
                f"{row['evidence_method']!r}"
            )
        evidence_rows += 1
        evidence_names = [
            item.strip()
            for item in row["evidence_names"].split(";")
            if item.strip()
        ]
        sites = [
            item.strip()
            for item in row["application_site"].split(";")
            if item.strip()
        ]
        if len(evidence_names) != len(sites):
            raise ValueError(
                f"{row['declaration']}: evidence/site cardinality mismatch "
                f"({len(evidence_names)} != {len(sites)})"
            )
        if row["evidence_method"] == "LIBRARY_CITATION":
            rebased = [
                rebase_library_site(
                    row["declaration"],
                    caller_name,
                    site,
                )
                for caller_name, site in zip(
                    evidence_names, sites, strict=True
                )
            ]
        else:
            rebased = [
                rebase_named_site(
                    row["declaration"],
                    evidence_name,
                    site,
                )
                for evidence_name, site in zip(
                    evidence_names, sites, strict=True
                )
            ]
        new = ";".join(rebased)
        if new != row["application_site"]:
            row["application_site"] = new
            sites_changed += 1
    if write:
        write_tsv(TIER_C_FILE, fields, rows)
    return evidence_rows, sites_changed


def main() -> int:
    parser = argparse.ArgumentParser()
    parser.add_argument(
        "--write",
        action="store_true",
        help="write the derived coordinates (default: dry run)",
    )
    args = parser.parse_args()
    try:
        tier_b_rows, tier_b_changed = rebase_tier_b(
            source_index(), args.write
        )
        tier_c_rows, tier_c_changed = rebase_tier_c(args.write)
    except (OSError, KeyError, ValueError) as error:
        print(f"ERROR: {error}", file=sys.stderr)
        return 1
    mode = "WROTE" if args.write else "DRY-RUN"
    print(f"{mode} Tier-B rows={tier_b_rows} changed={tier_b_changed}")
    print(
        f"{mode} Tier-C evidence rows={tier_c_rows} "
        f"changed={tier_c_changed}"
    )
    return 0


if __name__ == "__main__":
    sys.exit(main())
