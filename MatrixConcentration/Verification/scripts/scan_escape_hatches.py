#!/usr/bin/env python3
"""V5 calibrated escape-hatch and trust-surface scanner."""

from __future__ import annotations

import argparse
from collections import Counter, defaultdict
import csv
import json
from pathlib import Path
import re
import sys

from lean_source_scan import (
    LOGS,
    ROOT,
    WORK,
    compile_pattern,
    find_hits,
    lean_universe,
    lexical_contexts,
    relative,
    tsv_safe,
)


L = r"(?<![A-Za-z0-9_'])"
R = r"(?![A-Za-z0-9_'])"

# Every construct named in V5 appears explicitly here.  Some categories are
# inventories rather than prohibitions; ``kind`` below governs classification.
PATTERN_SPECS = [
    ("axiom", L + r"axiom" + R, "prohibited"),
    ("opaque", L + r"opaque" + R, "prohibited"),
    ("native_decide", L + r"native_decide" + R, "prohibited"),
    ("unsafe", L + r"unsafe" + R, "prohibited"),
    ("implemented_by", r"@\s*\[\s*implemented_by\b", "prohibited"),
    ("extern", r"@\s*\[\s*extern\b", "prohibited"),
    ("csimp", r"@\s*\[\s*csimp\b", "prohibited"),
    ("set_option", L + r"set_option" + R, "option"),
    ("debug.skipKernelTC", L + r"debug\.skipKernelTC" + R, "critical_option"),
    ("bootstrap_option", L + r"bootstrap\.[A-Za-z0-9_.]+" + R, "critical_option"),
    ("run_cmd", L + r"run_cmd" + R, "environment_mutation"),
    ("run_elab", L + r"run_elab" + R, "environment_mutation"),
    ("#eval", r"(?<![A-Za-z0-9_'])#eval" + R, "environment_mutation"),
    ("initialize", L + r"initialize" + R, "environment_mutation"),
    ("modifyEnv", L + r"modifyEnv" + R, "environment_mutation"),
    ("addDecl", L + r"addDecl" + R, "environment_mutation"),
    ("Environment.add", L + r"Environment\.add" + R, "environment_mutation"),
    ("partial_def", L + r"partial\s+def" + R, "partial"),
    ("reducible", r"@\s*\[\s*reducible\s*\]", "reducible"),
    ("local_instance", L + r"local\s+instance" + R, "local_instance"),
    ("letI", L + r"letI" + R, "local_instance"),
    ("haveI", L + r"haveI" + R, "local_instance"),
    ("Fact", L + r"Fact" + R, "fact"),
    ("macro_rules", L + r"macro_rules" + R, "meta_syntax"),
    ("macro", L + r"macro" + R, "meta_syntax"),
    ("syntax", L + r"syntax" + R, "meta_syntax"),
    ("elab_rules", L + r"elab_rules" + R, "meta_syntax"),
    ("elab", L + r"elab" + R, "meta_syntax"),
    ("notation", L + r"notation" + R, "meta_syntax"),
    ("infix_notation", L + r"(?:infix|infixl|infixr)" + R, "meta_syntax"),
    ("prefix_notation", L + r"prefix" + R, "meta_syntax"),
    ("postfix_notation", L + r"postfix" + R, "meta_syntax"),
]
PATTERNS = [
    (name, compile_pattern(expression))
    for name, expression, _kind in PATTERN_SPECS
]
KINDS = {name: kind for name, _expression, kind in PATTERN_SPECS}

PRODUCTION_SEVERITY = {
    "prohibited": "CRITICAL",
    "critical_option": "CRITICAL",
    "environment_mutation": "MAJOR",
    "partial": "review",
    "reducible": "INFO",
    "local_instance": "INFO",
    "fact": "INFO",
    "meta_syntax": "MAJOR-pending-shadowing-review",
    "option": "INFO",
}


def scan(paths: list[Path]) -> list[dict[str, object]]:
    rows: list[dict[str, object]] = []
    for hit in find_hits(paths, PATTERNS):
        kind = KINDS[hit.pattern]
        active = hit.context == "code"
        rows.append(
            {
                "path": relative(hit.path),
                "line": hit.line,
                "column": hit.column,
                "pattern": hit.pattern,
                "kind": kind,
                "matched": hit.matched,
                "context": hit.context,
                "active": "yes" if active else "no",
                "classification": (
                    PRODUCTION_SEVERITY[kind] if active else "textual_mention"
                ),
                "snippet": hit.snippet,
            }
        )
    rows.sort(
        key=lambda row: (
            str(row["path"]),
            int(row["line"]),
            int(row["column"]),
            str(row["pattern"]),
        )
    )
    return rows


def write_tsv(path: Path, rows: list[dict[str, object]]) -> None:
    fields = [
        "path",
        "line",
        "column",
        "pattern",
        "kind",
        "matched",
        "context",
        "active",
        "classification",
        "snippet",
    ]
    with path.open("w", encoding="utf-8", newline="") as handle:
        writer = csv.DictWriter(handle, fieldnames=fields, delimiter="\t")
        writer.writeheader()
        for row in rows:
            writer.writerow({key: tsv_safe(row[key]) for key in fields})


def parse_set_options(paths: list[Path]) -> list[dict[str, object]]:
    rows: list[dict[str, object]] = []
    command = re.compile(
        L + r"set_option\s+([A-Za-z0-9_.]+)(?:\s+([^\s]+))?", re.MULTILINE
    )
    for path in paths:
        text = path.read_text(encoding="utf-8")
        contexts = lexical_contexts(text)
        for match in command.finditer(text):
            if contexts[match.start()] != 0:
                continue
            line = text.count("\n", 0, match.start()) + 1
            line_start = text.rfind("\n", 0, match.start()) + 1
            line_end = text.find("\n", match.start())
            if line_end < 0:
                line_end = len(text)
            option = match.group(1)
            value = match.group(2) or ""
            disabling = option == "debug.skipKernelTC" or option.startswith("bootstrap.")
            rows.append(
                {
                    "path": relative(path),
                    "line": line,
                    "column": match.start() - line_start + 1,
                    "option": option,
                    "value": value,
                    "checking_disabling": "yes" if disabling else "no",
                    "snippet": text[line_start:line_end].strip(),
                }
            )
    rows.sort(key=lambda row: (str(row["path"]), int(row["line"])))
    return rows


def write_option_tsv(path: Path, rows: list[dict[str, object]]) -> None:
    fields = [
        "path",
        "line",
        "column",
        "option",
        "value",
        "checking_disabling",
        "snippet",
    ]
    with path.open("w", encoding="utf-8", newline="") as handle:
        writer = csv.DictWriter(handle, fieldnames=fields, delimiter="\t")
        writer.writeheader()
        for row in rows:
            writer.writerow({key: tsv_safe(row[key]) for key in fields})


def production() -> int:
    LOGS.mkdir(parents=True, exist_ok=True)
    paths = lean_universe()
    rows = scan(paths)
    active = [row for row in rows if row["active"] == "yes"]
    options = parse_set_options(paths)
    write_tsv(LOGS / "escape_hatch_scan.tsv", rows)
    write_option_tsv(LOGS / "set_option_inventory.tsv", options)

    active_by_pattern = Counter(str(row["pattern"]) for row in active)
    active_by_kind = Counter(str(row["kind"]) for row in active)
    option_counts = Counter(str(row["option"]) for row in options)
    disabling_options = [
        row for row in options if row["checking_disabling"] == "yes"
    ]
    prohibited = [
        row
        for row in active
        if row["kind"] in {"prohibited", "critical_option", "environment_mutation"}
    ]
    partials = [row for row in active if row["kind"] == "partial"]
    meta = [row for row in active if row["kind"] == "meta_syntax"]

    lakefile = ROOT / "lakefile.toml"
    lake_text = lakefile.read_text(encoding="utf-8")
    relaxed_match = re.search(
        r"^\s*relaxedAutoImplicit\s*=\s*([^\s#]+)", lake_text, re.MULTILINE
    )
    auto_match = re.search(
        r"^\s*autoImplicit\s*=\s*([^\s#]+)", lake_text, re.MULTILINE
    )
    auto_facts = {
        "lakefile_relaxedAutoImplicit": (
            relaxed_match.group(1) if relaxed_match else "not-set"
        ),
        "lakefile_autoImplicit": auto_match.group(1) if auto_match else "not-set",
        "effective_autoImplicit": (
            auto_match.group(1) if auto_match else "true (Lean default)"
        ),
    }
    with (LOGS / "autoimplicit_trust_surface.txt").open(
        "w", encoding="utf-8"
    ) as out:
        out.write("V5 AUTO-IMPLICIT TRUST-SURFACE RECORD\n")
        out.write(f"source\t{relative(lakefile)}\n")
        out.write(
            "lakefile_relaxedAutoImplicit\t"
            f"{auto_facts['lakefile_relaxedAutoImplicit']}\n"
        )
        out.write(
            f"lakefile_autoImplicit\t{auto_facts['lakefile_autoImplicit']}\n"
        )
        out.write(
            f"effective_autoImplicit\t{auto_facts['effective_autoImplicit']}\n"
        )
        out.write(
            "interpretation\trelaxedAutoImplicit=false restricts which undeclared "
            "names may be auto-bound; it does not turn autoImplicit off\n"
        )

    result = {
        "universe_definition": (
            "all .lean files physically under the project root, excluding .lake/**, "
            "MatrixConcentration/Verification/**, and .audit_work/**"
        ),
        "universe_count": len(paths),
        "universe": [relative(path) for path in paths],
        "all_textual_hits": len(rows),
        "active_hits": len(active),
        "textual_mentions": len(rows) - len(active),
        "active_hits_by_pattern": {
            name: active_by_pattern.get(name, 0) for name, _regex in PATTERNS
        },
        "active_hits_by_kind": dict(sorted(active_by_kind.items())),
        "prohibited_or_environment_mutation_hits": len(prohibited),
        "checking_disabling_set_options": len(disabling_options),
        "partial_def_hits": len(partials),
        "meta_syntax_hits_requiring_shadowing_review": len(meta),
        "set_option_total": len(options),
        "set_option_counts": dict(sorted(option_counts.items())),
        "autoimplicit": auto_facts,
    }
    (LOGS / "escape_hatch_scan.json").write_text(
        json.dumps(result, indent=2, sort_keys=True) + "\n", encoding="utf-8"
    )
    with (LOGS / "escape_hatch_summary.txt").open("w", encoding="utf-8") as out:
        out.write("V5 ESCAPE-HATCH AND TRUST-SURFACE SCAN\n")
        out.write(f"project_root\t{ROOT}\n")
        out.write(f"universe_files\t{len(paths)}\n")
        for path in paths:
            out.write(f"universe_file\t{relative(path)}\n")
        out.write(f"all_textual_hits\t{len(rows)}\n")
        out.write(f"active_hits\t{len(active)}\n")
        out.write(f"textual_mentions\t{len(rows) - len(active)}\n")
        out.write(f"prohibited_or_environment_mutation_hits\t{len(prohibited)}\n")
        out.write(f"checking_disabling_set_options\t{len(disabling_options)}\n")
        out.write(f"partial_def_hits\t{len(partials)}\n")
        out.write(f"meta_syntax_hits\t{len(meta)}\n")
        out.write(f"set_option_total\t{len(options)}\n")
        for option, count in sorted(option_counts.items()):
            out.write(f"set_option\t{option}\t{count}\n")
        for name, _regex in PATTERNS:
            out.write(f"active_pattern\t{name}\t{active_by_pattern.get(name, 0)}\n")
        out.write(
            "result\t"
            + ("CLEAN_TRUST_PATH\n" if not prohibited and not partials and not meta
               else "HITS_REQUIRE_REVIEW\n")
        )

    print(f"universe_files={len(paths)}")
    print(f"prohibited_or_environment_mutation_hits={len(prohibited)}")
    print(f"checking_disabling_set_options={len(disabling_options)}")
    print(f"partial_def_hits={len(partials)}")
    print(f"meta_syntax_hits={len(meta)}")
    print(f"set_option_total={len(options)}")
    print(f"evidence={relative(LOGS / 'escape_hatch_scan.tsv')}")
    return 0 if not prohibited and not partials and not meta else 1


def calibration() -> int:
    LOGS.mkdir(parents=True, exist_ok=True)
    plant = WORK / "EscapePlant.lean"
    if not plant.is_file():
        print(f"missing calibration plant: {plant}", file=sys.stderr)
        return 2
    rows = scan([plant])
    write_tsv(LOGS / "escape_hatch_calibration.tsv", rows)
    active = {
        str(row["pattern"])
        for row in rows
        if row["active"] == "yes"
    }
    required = {"native_decide", "axiom", "unsafe", "run_cmd"}
    missing = sorted(required - active)
    with (LOGS / "escape_hatch_calibration.txt").open(
        "w", encoding="utf-8"
    ) as out:
        out.write("V5 ESCAPE-HATCH SCANNER CALIBRATION\n")
        out.write(f"plant\t{relative(plant)}\n")
        out.write("required_patterns\t" + ",".join(sorted(required)) + "\n")
        out.write("observed_active_patterns\t" + ",".join(sorted(active)) + "\n")
        out.write("missing_required_patterns\t" + ",".join(missing) + "\n")
        for row in rows:
            if row["active"] == "yes":
                out.write(
                    f"hit\t{row['pattern']}\t{row['path']}:{row['line']}:"
                    f"{row['column']}\t{row['snippet']}\n"
                )
        out.write("result\t" + ("PASS\n" if not missing else "FAIL\n"))
    print("required_patterns=" + ",".join(sorted(required)))
    print("observed_active_patterns=" + ",".join(sorted(active)))
    print("missing_required_patterns=" + ",".join(missing))
    print(f"evidence={relative(LOGS / 'escape_hatch_calibration.tsv')}")
    return 0 if not missing else 1


def main() -> int:
    parser = argparse.ArgumentParser()
    parser.add_argument(
        "mode",
        choices=("production", "calibration"),
        nargs="?",
        default="production",
    )
    args = parser.parse_args()
    return calibration() if args.mode == "calibration" else production()


if __name__ == "__main__":
    raise SystemExit(main())
