#!/usr/bin/env python3
"""Validate and summarize the universal Lean.collectAxioms audit."""

from __future__ import annotations

from collections import Counter
import csv
import json
from pathlib import Path
import sys


SCRIPT = Path(__file__).resolve()
VERIFY = SCRIPT.parent.parent
ROOT = VERIFY.parent.parent
LOGS = VERIFY / "logs"
AUDIT = LOGS / "axiom_audit.tsv"
CALIBRATION = LOGS / "axiom_calibration.tsv"
MODULES = LOGS / "axiom_modules.txt"
IMPORT_GRAPH = LOGS / "import_graph.json"

ALLOWED = frozenset({"propext", "Classical.choice", "Quot.sound"})


def read_tsv(path: Path) -> list[dict[str, str]]:
    with path.open(encoding="utf-8", newline="") as handle:
        return list(csv.DictReader(handle, delimiter="\t"))


def axiom_set(text: str) -> frozenset[str]:
    return frozenset(part for part in text.split(",") if part)


def main() -> int:
    rows = read_tsv(AUDIT)
    calibration = read_tsv(CALIBRATION)
    module_names = {
        line.strip() for line in MODULES.read_text(encoding="utf-8").splitlines() if line.strip()
    }
    graph = json.loads(IMPORT_GRAPH.read_text(encoding="utf-8"))
    expected_modules = {item["module"] for item in graph["files"]}

    duplicate_names = [
        name for name, count in Counter(row["name"] for row in rows).items() if count > 1
    ]
    exceedances = [
        {
            **row,
            "unexpected": ",".join(sorted(axiom_set(row["axioms"]) - ALLOWED)),
        }
        for row in rows
        if not axiom_set(row["axioms"]).issubset(ALLOWED)
    ]
    sorry_rows = [row for row in rows if "sorryAx" in axiom_set(row["axioms"])]
    reduce_rows = [
        row
        for row in rows
        if axiom_set(row["axioms"])
        & {"Lean.ofReduceBool", "Lean.ofReduceNat", "Lean.trustCompiler"}
    ]
    declared_axioms = [row for row in rows if row["kind"] == "axiom"]
    declared_opaques = [row for row in rows if row["kind"] == "opaque"]
    private_rows = [row for row in rows if row["name"].startswith("_private.")]
    internal_rows = [
        row
        for row in rows
        if row["name"].startswith("_")
        or "._@" in row["name"]
        or ".match_" in row["name"]
        or ".proof_" in row["name"]
    ]
    distribution = Counter(
        tuple(sorted(axiom_set(row["axioms"]))) for row in rows
    )
    kind_counts = Counter(row["kind"] for row in rows)
    module_counts = Counter(row["module"] for row in rows)

    calibration_public = [
        row
        for row in calibration
        if row["user_name"] == "VerificationPublicAxiomCalibration"
        and "sorryAx" in axiom_set(row["axioms"])
    ]
    calibration_private = [
        row
        for row in calibration
        if row["user_name"] == "verificationPrivateAxiomCalibration"
        and row["name"].startswith("_private.")
        and "sorryAx" in axiom_set(row["axioms"])
    ]
    missing_modules = sorted(expected_modules - module_names)
    unexpected_modules = sorted(module_names - expected_modules)
    audited_modules = {row["module"] for row in rows}
    modules_without_constants = sorted(module_names - audited_modules)

    with (LOGS / "axiom_exceedances.tsv").open("w", encoding="utf-8", newline="") as handle:
        writer = csv.DictWriter(
            handle,
            delimiter="\t",
            fieldnames=("module", "name", "user_name", "kind", "axioms", "unexpected"),
        )
        writer.writeheader()
        writer.writerows(exceedances)

    with (LOGS / "axiom_distribution.tsv").open(
        "w", encoding="utf-8", newline=""
    ) as handle:
        writer = csv.writer(handle, delimiter="\t")
        writer.writerow(("axiom_set", "count"))
        for axioms, count in sorted(distribution.items(), key=lambda item: (len(item[0]), item[0])):
            writer.writerow((",".join(axioms) or "(none)", count))

    summary = {
        "allowed_axioms": sorted(ALLOWED),
        "total_declarations": len(rows),
        "module_count": len(module_names),
        "expected_module_count": len(expected_modules),
        "missing_modules": missing_modules,
        "unexpected_modules": unexpected_modules,
        "modules_without_constants": modules_without_constants,
        "private_declarations": len(private_rows),
        "internal_or_generated_declarations": len(internal_rows),
        "kind_counts": dict(sorted(kind_counts.items())),
        "module_declaration_counts": dict(sorted(module_counts.items())),
        "axiom_distribution": {
            ",".join(axioms) or "(none)": count
            for axioms, count in sorted(
                distribution.items(), key=lambda item: (len(item[0]), item[0])
            )
        },
        "exceedances": len(exceedances),
        "sorryAx_dependencies": len(sorry_rows),
        "reduce_or_trust_dependencies": len(reduce_rows),
        "declared_axioms": len(declared_axioms),
        "declared_opaques": len(declared_opaques),
        "duplicate_names": duplicate_names,
        "calibration_public_sorryAx": len(calibration_public),
        "calibration_private_sorryAx": len(calibration_private),
    }
    (LOGS / "axiom_summary.json").write_text(
        json.dumps(summary, indent=2, sort_keys=True) + "\n", encoding="utf-8"
    )
    lines = [
        "V4 UNIVERSAL AXIOM AUDIT",
        f"TOTAL_DECLARATIONS {len(rows)}",
        f"MODULES {len(module_names)}",
        f"EXPECTED_MODULES {len(expected_modules)}",
        f"MISSING_MODULES {len(missing_modules)}",
        *missing_modules,
        f"UNEXPECTED_MODULES {len(unexpected_modules)}",
        *unexpected_modules,
        f"MODULES_WITHOUT_CONSTANTS {len(modules_without_constants)}",
        *modules_without_constants,
        f"PRIVATE_DECLARATIONS {len(private_rows)}",
        f"INTERNAL_OR_GENERATED_DECLARATIONS {len(internal_rows)}",
        f"EXCEEDANCES {len(exceedances)}",
        f"SORRYAX_DEPENDENCIES {len(sorry_rows)}",
        f"REDUCE_OR_TRUST_DEPENDENCIES {len(reduce_rows)}",
        f"DECLARED_AXIOMS {len(declared_axioms)}",
        f"DECLARED_OPAQUES {len(declared_opaques)}",
        f"DUPLICATE_NAMES {len(duplicate_names)}",
        f"CALIBRATION_PUBLIC_SORRYAX {len(calibration_public)}",
        f"CALIBRATION_PRIVATE_SORRYAX {len(calibration_private)}",
        "",
        "KIND_COUNTS",
        *(f"{kind}\t{count}" for kind, count in sorted(kind_counts.items())),
        "",
        "AXIOM_SET_DISTRIBUTION",
        *(
            f"{','.join(axioms) or '(none)'}\t{count}"
            for axioms, count in sorted(
                distribution.items(), key=lambda item: (len(item[0]), item[0])
            )
        ),
        "",
        "MODULE_DECLARATION_COUNTS",
        *(f"{module}\t{count}" for module, count in sorted(module_counts.items())),
        "",
        "EXCEEDANCE_ROWS",
        *(
            f"{row['module']}\t{row['name']}\t{row['axioms']}\t{row['unexpected']}"
            for row in exceedances
        ),
    ]
    text = "\n".join(lines) + "\n"
    (LOGS / "axiom_summary.txt").write_text(text, encoding="utf-8")
    print(text, end="")

    passed = (
        bool(rows)
        and not missing_modules
        and not unexpected_modules
        and not exceedances
        and not sorry_rows
        and not reduce_rows
        and not declared_axioms
        and not declared_opaques
        and not duplicate_names
        and len(calibration_public) == 1
        and len(calibration_private) == 1
    )
    print(f"VERDICT {'PASS' if passed else 'FAIL'}")
    return 0 if passed else 1


if __name__ == "__main__":
    sys.exit(main())
