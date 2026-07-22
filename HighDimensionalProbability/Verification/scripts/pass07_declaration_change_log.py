#!/usr/bin/env python3
"""Generate and verify the Pass 07 declaration change log.

The command parser and token fingerprints are imported from
``scripts/verify_declaration_preservation.py``, as required by Task F.  The
historical inputs are authenticated consolidated source blobs in the sibling
Git repository:

* commit ``7ca7549...`` supplies the 25 core/Prelude files;
* commit ``f199612...`` supplies the pre-correction Exercise 8.31 file.

The second blob has the same SHA-256 as the independently reconstructed
successful Pass 07 patch predecessor.  The live tree is allowed to differ
from that historical Pass 07 population only by the exact later scope-removal
overlay recorded by V10 and by the independently certified Exercise-tree
reorganization.  No historical source is inferred from current line ranges.
"""

from __future__ import annotations

import argparse
import csv
import hashlib
import importlib.util
import json
import subprocess
import sys
import tempfile
from collections import Counter, defaultdict
from dataclasses import dataclass
from pathlib import Path
from typing import Iterable


SCRIPT = Path(__file__).resolve()
PROJECT = SCRIPT.parents[3]
SOURCE = PROJECT / "HighDimensionalProbability"
VERIFICATION = SOURCE / "Verification"
INVENTORY = VERIFICATION / "inventory"
SIBLING = PROJECT.parent / "LeanProbabilityFormalizations"
CORE_COMMIT = "7ca7549cbaa90990d790bb79f9c9a09087644e17"
EXERCISE_COMMIT = "f199612a6e0d7975a412ad15fbb781303b8badd8"
BASELINE_EXERCISE_PATH = (
    "HighDimensionalProbability/Chapter8/Exercise/Sec04.lean"
)
CURRENT_EXERCISE_PATH = (
    "HighDimensionalProbability/Exercise/Chapter8/Sec04.lean"
)
EXPECTED_EXERCISE_SHA256 = (
    "5a136f837f2d723f51506484bf391ea873c7dc6c7e10a6fe1b4b990d3f8b6fd1"
)
EXPECTED_KINDS = Counter(
    {
        "theorem": 64,
        "lemma": 4,
        "def": 23,
        "structure": 4,
        "instance": 3,
        "abbrev": 2,
    }
)
ADDED_PATH = INVENTORY / "pass07_declaration_changes.tsv"
MODIFIED_PATH = INVENTORY / "pass07_same_name_changes.tsv"
SUMMARY_PATH = INVENTORY / "pass07_declaration_changes_summary.json"
REMOVAL_LEDGER = VERIFICATION / "review" / "v10_ledger_reconciliation.tsv"
REORGANIZATION_CERTIFICATE = (
    VERIFICATION / "logs" / "exercise_reorganization_delta.log"
)
EXPECTED_POST_PASS_REMOVALS = {
    ("class", "GaussianChevetUpperPrinciple"),
    ("theorem", "exercise_8_39a_gaussian_chevet_arbitrary"),
    ("theorem", "exercise_8_39a_gaussian_chevet_arbitrary_envelope"),
    (
        "theorem",
        "gaussianChevetExpectationEnvelope_ne_top_of_isBounded",
    ),
    ("theorem", "remark_8_6_3_gaussian_chevet_arbitrary"),
    ("theorem", "remark_8_6_3_gaussian_chevet_arbitrary_envelope"),
}
EXPECTED_POST_PASS_REMOVAL_FQ_NAMES = {
    f"HDP.Chapter8.{name}" for _kind, name in EXPECTED_POST_PASS_REMOVALS
}
EXPECTED_POST_PASS_MODIFICATIONS = {
    ("theorem", "exercise_8_39a_gaussian_chevet"),
    ("theorem", "remark_8_6_3_gaussian_chevet"),
}
EXPECTED_POST_PASS_MODIFICATION_FQ_NAMES = {
    f"HDP.Chapter8.{name}" for _kind, name in EXPECTED_POST_PASS_MODIFICATIONS
}
EXPECTED_REMOVAL_LEDGER_DECLARATIONS = {
    "HDP.Chapter3.BorellConvexBodyPsiOnePrinciple",
    "HDP.Chapter3.convexBodyUniform_marginal_subExponential_of_borell",
    "HDP.Chapter5.positive_ricci_concentration",
    "HDP.Chapter5.positive_ricci_concentration_psi2",
    "HDP.Chapter5.positive_ricci_concentration_psi2_of_lipschitz",
    "HDP.Chapter8.GaussianChevetUpperPrinciple",
    "HDP.Chapter8.exercise_8_39a_gaussian_chevet_arbitrary",
    "HDP.Chapter8.exercise_8_39a_gaussian_chevet_arbitrary_envelope",
    "HDP.Chapter8.gaussianChevetExpectationEnvelope_ne_top_of_isBounded",
    "HDP.Chapter8.gaussianChevetUpperPrinciple_external",
    "HDP.Chapter8.remark_8_6_3_gaussian_chevet_arbitrary",
    "HDP.Chapter8.remark_8_6_3_gaussian_chevet_arbitrary_envelope",
}


def sha256_bytes(data: bytes) -> str:
    return hashlib.sha256(data).hexdigest()


def sha256_text(text: str) -> str:
    return sha256_bytes(text.encode("utf-8"))


def sha256_file(path: Path) -> str:
    return sha256_bytes(path.read_bytes())


def token_sha256(tokens: Iterable[str]) -> str:
    return sha256_text("\x1f".join(tokens))


def run(*args: str) -> str:
    result = subprocess.run(
        args, text=True, stdout=subprocess.PIPE, stderr=subprocess.PIPE
    )
    if result.returncode:
        raise RuntimeError(
            f"command failed ({result.returncode}): {' '.join(args)}\n"
            f"{result.stderr}"
        )
    return result.stdout


def load_preservation_module():
    path = PROJECT / "scripts" / "verify_declaration_preservation.py"
    spec = importlib.util.spec_from_file_location("pass07_preservation", path)
    if spec is None or spec.loader is None:
        raise RuntimeError(f"cannot import {path}")
    module = importlib.util.module_from_spec(spec)
    sys.modules[spec.name] = module
    spec.loader.exec_module(module)
    return module


PRESERVATION = load_preservation_module()


def load_reorganization_module():
    path = SCRIPT.with_name("verify_exercise_reorganization.py")
    spec = importlib.util.spec_from_file_location("pass07_reorganization", path)
    if spec is None or spec.loader is None:
        raise RuntimeError(f"cannot import {path}")
    module = importlib.util.module_from_spec(spec)
    sys.modules[spec.name] = module
    spec.loader.exec_module(module)
    return module


REORGANIZATION = load_reorganization_module()


@dataclass(frozen=True)
class Decl:
    kind: str
    name: str
    source: str
    line: int
    tokens: tuple[str, ...]
    signature_tokens: tuple[str, ...]
    body_tokens: tuple[str, ...]

    @classmethod
    def from_preservation(cls, item, source: str) -> "Decl":
        return cls(
            item.kind,
            item.name,
            source,
            item.line,
            item.tokens,
            item.signature_tokens,
            item.body_tokens,
        )

    @property
    def key(self) -> tuple[str, str]:
        return self.kind, self.name

    @property
    def command_sha256(self) -> str:
        return token_sha256(self.tokens)

    @property
    def signature_sha256(self) -> str:
        return token_sha256(self.signature_tokens)

    @property
    def body_sha256(self) -> str:
        return token_sha256(self.body_tokens)


@dataclass(frozen=True)
class Comparison:
    added: tuple[Decl, ...]
    removed: tuple[Decl, ...]
    modified: tuple[tuple[Decl, Decl], ...]


def extract(path: Path, source: str) -> list[Decl]:
    return [
        Decl.from_preservation(item, source)
        for item in PRESERVATION.extract_declarations(path)
    ]


def group(rows: Iterable[Decl]) -> dict[tuple[str, str], list[Decl]]:
    result: dict[tuple[str, str], list[Decl]] = defaultdict(list)
    for row in rows:
        result[row.key].append(row)
    return result


def compare(old: list[Decl], new: list[Decl]) -> Comparison:
    old_groups = group(old)
    new_groups = group(new)
    added: list[Decl] = []
    removed: list[Decl] = []
    modified: list[tuple[Decl, Decl]] = []
    for key in sorted(set(old_groups) | set(new_groups)):
        before = list(old_groups.get(key, []))
        after = list(new_groups.get(key, []))
        after_by_hash: dict[str, list[Decl]] = defaultdict(list)
        for item in after:
            after_by_hash[item.command_sha256].append(item)
        unmatched_before: list[Decl] = []
        matched_ids: set[int] = set()
        for item in before:
            candidates = after_by_hash.get(item.command_sha256, [])
            if candidates:
                matched_ids.add(id(candidates.pop(0)))
            else:
                unmatched_before.append(item)
        before = unmatched_before
        after = [item for item in after if id(item) not in matched_ids]
        if not before:
            added.extend(after)
        elif not after:
            removed.extend(before)
        elif len(before) == len(after) == 1:
            modified.append((before[0], after[0]))
        else:
            raise RuntimeError(f"ambiguous same-name declaration comparison: {key}")
    return Comparison(tuple(added), tuple(removed), tuple(modified))


def git_show(commit: str, path: str) -> str:
    return run("git", "-C", str(SIBLING), "show", f"{commit}:{path}")


def git_tree(commit: str) -> str:
    return run(
        "git", "-C", str(SIBLING), "rev-parse", f"{commit}^{{tree}}"
    ).strip()


def core_paths() -> list[str]:
    names = run(
        "git", "-C", str(SIBLING), "ls-tree", "-r", "--name-only", CORE_COMMIT
    ).splitlines()
    prefix = "HighDimensionalProbability/"
    selected = []
    for name in names:
        if not name.startswith(prefix) or not name.endswith(".lean"):
            continue
        tail = name.removeprefix(prefix)
        if "/" not in tail or (
            tail.startswith("Prelude/") and tail.count("/") == 1
        ):
            selected.append(name)
    if len(selected) != 25:
        raise RuntimeError(f"expected 25 core/Prelude files, found {len(selected)}")
    return sorted(selected)


def validate_scope_removal_overlay(
    removed: Iterable[Decl],
    modified: Iterable[tuple[Decl, Decl]],
) -> str:
    removed_rows = tuple(removed)
    actual = {(row.kind, row.name) for row in removed_rows}
    if actual != EXPECTED_POST_PASS_REMOVALS or len(actual) != len(removed_rows):
        raise RuntimeError(
            "current core delta has unexpected post-Pass-07 removals: "
            f"{sorted(actual)}"
        )
    if any(
        row.source != "HighDimensionalProbability/Chapter8_Chaining.lean"
        for row in removed_rows
    ):
        raise RuntimeError("authorized post-Pass-07 removals changed source file")

    modified_rows = tuple(modified)
    actual_modified = {(after.kind, after.name) for _before, after in modified_rows}
    if (
        actual_modified != EXPECTED_POST_PASS_MODIFICATIONS
        or len(actual_modified) != len(modified_rows)
        or any(
            after.source != "HighDimensionalProbability/Chapter8_Chaining.lean"
            for _before, after in modified_rows
        )
    ):
        raise RuntimeError(
            "current core delta has unexpected post-Pass-07 retained-interface "
            f"changes: {sorted(actual_modified)}"
        )

    with REMOVAL_LEDGER.open(encoding="utf-8", newline="") as handle:
        reader = csv.DictReader(handle, delimiter="\t")
        expected_columns = (
            "ledger_item",
            "semantic_condition",
            "detector_evidence",
            "classification",
            "direction",
            "result",
        )
        if tuple(reader.fieldnames or ()) != expected_columns:
            raise RuntimeError(f"{REMOVAL_LEDGER}: unexpected columns")
        ledger_rows = [
            row
            for row in reader
            if row["ledger_item"] == "REMOVED-DECLARATION-ABSENCE"
        ]
    ledger_names = {row["semantic_condition"] for row in ledger_rows}
    if (
        len(ledger_rows) != len(ledger_names)
        or ledger_names != EXPECTED_REMOVAL_LEDGER_DECLARATIONS
        or any(
            row["classification"] != "ABSENT"
            or row["direction"] != "exact source-and-environment absence"
            or row["result"] != "CONFIRMED"
            for row in ledger_rows
        )
    ):
        raise RuntimeError(
            f"{REMOVAL_LEDGER}: exact authorized-removal ledger changed"
        )
    if not EXPECTED_POST_PASS_REMOVAL_FQ_NAMES <= ledger_names:
        raise RuntimeError("core scope removals are not covered by the V10 ledger")
    with REMOVAL_LEDGER.open(encoding="utf-8", newline="") as handle:
        retained_rows = [
            row
            for row in csv.DictReader(handle, delimiter="\t")
            if row["ledger_item"] == "RETAINED-FINITE-CHEVET-HZERO"
        ]
    retained_names = {
        row["semantic_condition"].removesuffix("[hzero]")
        for row in retained_rows
    }
    if (
        len(retained_rows) != len(retained_names)
        or retained_names != EXPECTED_POST_PASS_MODIFICATION_FQ_NAMES
        or any(
            not row["semantic_condition"].endswith("[hzero]")
            or row["classification"] != "RETAINED-FINITE-ZERO-MEMBERSHIP"
            or row["direction"]
            != "source-to-environment signature visibility"
            or row["result"] != "CONFIRMED"
            for row in retained_rows
        )
    ):
        raise RuntimeError(
            f"{REMOVAL_LEDGER}: exact retained finite-Chevet overlay changed"
        )
    return sha256_file(REMOVAL_LEDGER)


def module_name(path: str) -> str:
    return path.removesuffix(".lean").replace("/", ".")


def compiled_name_resolver():
    audit = VERIFICATION / "logs" / "axiom_audit.tsv"
    by_module: dict[str, list[dict[str, str]]] = defaultdict(list)
    with audit.open(encoding="utf-8", newline="") as handle:
        for row in csv.DictReader(handle, delimiter="\t"):
            by_module[row["module"]].append(row)

    def resolve(path: str, short_name: str) -> str:
        candidates: set[str] = set()
        current_module = module_name(path)
        historical_path = REORGANIZATION.new_to_old_exercise_path(path)
        modules = {current_module, module_name(historical_path)}
        for module in modules:
            for row in by_module[module]:
                if row["is_private"] == "true":
                    name = row["private_user_name"]
                elif row["is_internal"] == "false":
                    name = row["name"]
                else:
                    continue
                if name and (
                    name == short_name or name.endswith("." + short_name)
                ):
                    candidates.add(name)
        if len(candidates) != 1:
            raise RuntimeError(
                f"cannot resolve {path}:{short_name}: {sorted(candidates)}"
            )
        return next(iter(candidates))

    return resolve


def source_manifest_digest() -> str:
    manifest = VERIFICATION / "logs" / "source_manifest.txt"
    for line in manifest.read_text(encoding="utf-8").splitlines():
        if line.startswith("# digest_of_digests: "):
            return line.removeprefix("# digest_of_digests: ")
    raise RuntimeError("source manifest has no digest_of_digests header")


def write_tsv_bytes(fields: tuple[str, ...], rows: list[dict[str, str]]) -> bytes:
    import io

    output = io.StringIO(newline="")
    writer = csv.DictWriter(
        output,
        fieldnames=fields,
        delimiter="\t",
        lineterminator="\n",
        extrasaction="raise",
    )
    writer.writeheader()
    writer.writerows(rows)
    return output.getvalue().encode("utf-8")


def generate() -> dict[Path, bytes]:
    certified_current_digest = REORGANIZATION.require_certificate(
        REORGANIZATION_CERTIFICATE
    )
    manifest_digest = source_manifest_digest()
    if manifest_digest != certified_current_digest:
        raise RuntimeError(
            "source manifest and Exercise-reorganization certificate disagree: "
            f"{manifest_digest} != {certified_current_digest}"
        )
    current_hashes: dict[str, str] = {}
    baseline_hashes: dict[str, str] = {}
    provenance: dict[str, tuple[str, str, str]] = {}
    added: list[Decl] = []
    removed: list[Decl] = []
    modified: list[tuple[Decl, Decl]] = []

    with tempfile.TemporaryDirectory(prefix="pass07-declarations-") as raw:
        temp = Path(raw)
        inputs = [(CORE_COMMIT, path, path) for path in core_paths()]
        inputs.append(
            (EXERCISE_COMMIT, BASELINE_EXERCISE_PATH, CURRENT_EXERCISE_PATH)
        )
        for index, (commit, baseline_path, current_path_text) in enumerate(inputs):
            old_text = git_show(commit, baseline_path)
            old_path = temp / f"{index:02d}.lean"
            old_path.write_text(old_text, encoding="utf-8")
            current_path = PROJECT / current_path_text
            new_text = current_path.read_text(encoding="utf-8")
            result = compare(
                extract(old_path, baseline_path),
                extract(current_path, current_path_text),
            )
            added.extend(result.added)
            removed.extend(result.removed)
            modified.extend(result.modified)
            baseline_hashes[current_path_text] = sha256_text(old_text)
            current_hashes[current_path_text] = sha256_text(new_text)
            provenance[current_path_text] = (
                commit,
                git_tree(commit),
                f"{SIBLING}@{commit}",
            )

    if baseline_hashes[CURRENT_EXERCISE_PATH] != EXPECTED_EXERCISE_SHA256:
        raise RuntimeError("Exercise 8.31 baseline blob hash changed")
    post_pass_modified = [
        pair
        for pair in modified
        if (pair[1].kind, pair[1].name) in EXPECTED_POST_PASS_MODIFICATIONS
    ]
    modified = [pair for pair in modified if pair not in post_pass_modified]
    removal_ledger_hash = validate_scope_removal_overlay(
        removed, post_pass_modified
    )
    if len(added) != 100 or Counter(item.kind for item in added) != EXPECTED_KINDS:
        raise RuntimeError(
            f"added declaration census changed: {len(added)}, "
            f"{Counter(item.kind for item in added)}"
        )
    if len(modified) != 23:
        raise RuntimeError(f"expected 23 same-name changes, found {len(modified)}")

    resolve = compiled_name_resolver()
    added_rows: list[dict[str, str]] = []
    for item in sorted(added, key=lambda row: (row.source, row.line, row.name)):
        commit, tree, reference = provenance[item.source]
        fq_name = resolve(item.source, item.name)
        change_id = "declchg-" + sha256_text(
            "\0".join(("ADDED", item.kind, fq_name, item.command_sha256))
        )[:16]
        added_rows.append(
            {
                "change_id": change_id,
                "change_kind": "ADDED",
                "command_kind": item.kind,
                "fq_name": fq_name,
                "source_name": item.name,
                "current_file": item.source,
                "current_line": str(item.line),
                "baseline_ref": reference,
                "baseline_commit": commit,
                "baseline_tree": tree,
                "baseline_file_sha256": baseline_hashes[item.source],
                "current_file_sha256": current_hashes[item.source],
                "new_signature_sha256": item.signature_sha256,
                "new_body_sha256": item.body_sha256,
                "new_command_sha256": item.command_sha256,
                "verification_status": "MECHANICALLY_VERIFIED_ADDED",
            }
        )

    modified_rows: list[dict[str, str]] = []
    for before, after in sorted(
        modified, key=lambda pair: (pair[1].source, pair[1].line, pair[1].name)
    ):
        signature_changed = before.signature_sha256 != after.signature_sha256
        body_changed = before.body_sha256 != after.body_sha256
        if signature_changed and body_changed:
            change_kind = "SIGNATURE_AND_BODY"
        elif signature_changed:
            change_kind = "SIGNATURE_ONLY"
        elif body_changed:
            change_kind = "BODY_ONLY"
        else:
            raise RuntimeError(f"empty same-name change: {after.key}")
        commit, tree, reference = provenance[after.source]
        fq_name = resolve(after.source, after.name)
        change_id = "declmod-" + sha256_text(
            "\0".join(
                (
                    change_kind,
                    after.kind,
                    fq_name,
                    before.command_sha256,
                    after.command_sha256,
                )
            )
        )[:16]
        modified_rows.append(
            {
                "change_id": change_id,
                "change_kind": change_kind,
                "command_kind": after.kind,
                "fq_name": fq_name,
                "source_name": after.name,
                "baseline_file": before.source,
                "baseline_line": str(before.line),
                "current_file": after.source,
                "current_line": str(after.line),
                "baseline_ref": reference,
                "baseline_commit": commit,
                "baseline_tree": tree,
                "baseline_file_sha256": baseline_hashes[after.source],
                "current_file_sha256": current_hashes[after.source],
                "old_signature_sha256": before.signature_sha256,
                "new_signature_sha256": after.signature_sha256,
                "old_body_sha256": before.body_sha256,
                "new_body_sha256": after.body_sha256,
                "old_command_sha256": before.command_sha256,
                "new_command_sha256": after.command_sha256,
                "verification_status": "MECHANICALLY_VERIFIED_SAME_NAME_CHANGE",
            }
        )

    added_fields = tuple(added_rows[0])
    modified_fields = tuple(modified_rows[0])
    added_bytes = write_tsv_bytes(added_fields, added_rows)
    modified_bytes = write_tsv_bytes(modified_fields, modified_rows)
    summary = {
        "schema_version": 2,
        "source_manifest_digest": manifest_digest,
        "parser": "scripts/verify_declaration_preservation.py",
        "baselines": {
            "core_commit": CORE_COMMIT,
            "core_tree": git_tree(CORE_COMMIT),
            "core_files": 25,
            "exercise_commit": EXERCISE_COMMIT,
            "exercise_tree": git_tree(EXERCISE_COMMIT),
            "exercise_baseline_file": BASELINE_EXERCISE_PATH,
            "exercise_current_file": CURRENT_EXERCISE_PATH,
            "exercise_file_sha256": baseline_hashes[CURRENT_EXERCISE_PATH],
        },
        "added": {
            "rows": len(added_rows),
            "target_kind_rows": sum(
                row["command_kind"] in {"theorem", "lemma", "def"}
                for row in added_rows
            ),
            "kind_counts": dict(
                sorted(Counter(row["command_kind"] for row in added_rows).items())
            ),
            "removed_rows": 0,
            "renamed_rows": 0,
        },
        "same_name_changes": {
            "rows": len(modified_rows),
            "kind_counts": dict(
                sorted(Counter(row["change_kind"] for row in modified_rows).items())
            ),
        },
        "post_pass_overlays": {
            "authorized_scope_removals": {
                "rows_in_core_comparison": len(removed),
                "fq_names": sorted(EXPECTED_POST_PASS_REMOVAL_FQ_NAMES),
                "retained_interface_change_rows": len(post_pass_modified),
                "retained_interface_fq_names": sorted(
                    EXPECTED_POST_PASS_MODIFICATION_FQ_NAMES
                ),
                "v10_removal_ledger": REMOVAL_LEDGER.relative_to(PROJECT).as_posix(),
                "v10_removal_ledger_sha256": removal_ledger_hash,
            },
            "exercise_reorganization": {
                "baseline_digest": REORGANIZATION.ROUND10_SOURCE_DIGEST,
                "current_digest": certified_current_digest,
                "certificate": REORGANIZATION_CERTIFICATE.relative_to(
                    PROJECT
                ).as_posix(),
                "certificate_sha256": sha256_file(REORGANIZATION_CERTIFICATE),
            },
        },
        "artifacts": {
            ADDED_PATH.name: sha256_bytes(added_bytes),
            MODIFIED_PATH.name: sha256_bytes(modified_bytes),
        },
        "checks": {
            "exact_100_added": True,
            "exact_91_theorem_lemma_def": True,
            "exact_kind_split": True,
            "exact_23_same_name_changes": True,
            "zero_removed": True,
            "zero_renamed": True,
            "fully_qualified_names_joined_to_axiom_audit": True,
            "exact_authorized_post_pass_scope_removal_overlay": True,
            "exact_authorized_post_pass_retained_interface_overlay": True,
            "exact_exercise_reorganization_certificate": True,
        },
    }
    summary_bytes = (
        json.dumps(summary, indent=2, sort_keys=True) + "\n"
    ).encode("utf-8")
    return {
        ADDED_PATH: added_bytes,
        MODIFIED_PATH: modified_bytes,
        SUMMARY_PATH: summary_bytes,
    }


def main() -> int:
    parser = argparse.ArgumentParser()
    mode = parser.add_mutually_exclusive_group(required=True)
    mode.add_argument("--write", action="store_true")
    mode.add_argument("--check", action="store_true")
    args = parser.parse_args()
    artifacts = generate()
    if args.write:
        INVENTORY.mkdir(parents=True, exist_ok=True)
        for path, content in artifacts.items():
            path.write_bytes(content)
            print(f"WROTE {path} sha256={sha256_bytes(content)}")
    else:
        for path, expected in artifacts.items():
            if not path.is_file() or path.read_bytes() != expected:
                print(f"DRIFT {path}", file=sys.stderr)
                return 1
            print(f"PASS {path} sha256={sha256_bytes(expected)}")
    print("PASS added=100 target_kinds=91 same_name_changes=23 removed=0 renamed=0")
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
