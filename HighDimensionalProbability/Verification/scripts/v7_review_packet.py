#!/usr/bin/env python3
"""Render a fail-closed static review packet for one V7 definition shard.

The packet is a reading aid only.  It joins one manual-review shard to the
canonical load-bearing inventory, theorem-candidate inventory, V4 axiom/type
TSVs, and physical Lean source.  It never invokes Lean or Lake and never
changes the shard or assigns a semantic review status.

Normal use:

    python3 -B HighDimensionalProbability/Verification/scripts/v7_review_packet.py \
      --shard HighDimensionalProbability/Verification/review/v7_definition_review_shard_01.tsv \
      --output HighDimensionalProbability/Verification/review/v7_definition_review_shard_01_packet.md

The renderer fails before writing output if any machine metadata, V4 join,
source module/path, declaration anchor, or candidate theorem check is
missing or ambiguous.
"""

from __future__ import annotations

import argparse
import csv
import hashlib
import re
import sys
import tempfile
from dataclasses import dataclass
from pathlib import Path
from typing import Callable, Iterable, Sequence

from definition_sanity import (
    CANDIDATE_COLUMNS,
    LOAD_BEARING_COLUMNS,
    LOAD_BEARING,
    NONTRIVIALITY_CANDIDATES,
    module_to_source_path,
)
from lean_source_scanner import mask_lean_noncode
from v7_definition_review import (
    CANDIDATE_DISPOSITION,
    CONTRACT_VERSION,
    REVIEW_COLUMNS,
)


ROOT = Path(__file__).resolve().parents[3]
LOGS = ROOT / "HighDimensionalProbability" / "Verification" / "logs"
DEFAULT_V4_AXIOMS = LOGS / "axiom_audit.tsv"
DEFAULT_V4_TYPES = LOGS / "axiom_declaration_types.tsv"

V4_AXIOM_COLUMNS = (
    "module",
    "name",
    "kind",
    "is_private",
    "private_user_name",
    "is_internal",
    "axioms",
)
V4_TYPE_COLUMNS = (
    "module",
    "name",
    "kind",
    "is_private",
    "private_user_name",
    "is_internal",
    "level_params",
    "binder_count",
    "type_raw",
    "conclusion_raw",
)
V4_COMMON_COLUMNS = V4_AXIOM_COLUMNS[:-1]

SOURCE_DECLARATION = re.compile(
    r"""(?x)
    ^[ \t]*
    (?:@\[[^\]\n]*\][ \t]*)*
    (?:(?:private|protected|noncomputable|unsafe|partial|local)[ \t]+)*
    (?P<keyword>
      theorem|lemma|def|abbrev|opaque|irreducible_def|
      structure|class|inductive|instance|alias
    )
    [ \t]+
    (?P<name>«[^»\n]+»|[^\s\(\{\[\:=>]+)
    """,
    re.MULTILINE,
)
SOURCE_ANONYMOUS_INSTANCE = re.compile(
    r"""(?x)
    ^[ \t]*
    (?:@\[[^\]\n]*\][ \t]*)*
    (?:(?:private|protected|noncomputable|unsafe|partial|local)[ \t]+)*
    (?P<keyword>instance)
    (?=[ \t]+(?:[\(\{\[]|:))
    """,
    re.MULTILINE,
)
NAMESPACE = re.compile(
    r"^[ \t]*namespace[ \t]+(?P<name>[^\s]+)[ \t]*$"
)
SECTION = re.compile(
    r"^[ \t]*(?:noncomputable[ \t]+)?section"
    r"(?:[ \t]+(?P<name>[^\s]+))?[ \t]*$"
)
MUTUAL = re.compile(r"^[ \t]*mutual[ \t]*$")
END = re.compile(r"^[ \t]*end(?:[ \t]+[^\s]+)?[ \t]*$")
SOURCE_DEFINITION_KEYWORDS = {
    "def",
    "abbrev",
    "opaque",
    "irreducible_def",
    "instance",
}
SOURCE_THEOREM_KEYWORDS = {"theorem", "lemma", "alias"}
SOURCE_CANDIDATE_KEYWORDS = SOURCE_THEOREM_KEYWORDS | {"instance"}
SOURCE_GENERATED_OWNER_KEYWORDS = {
    "theorem",
    "lemma",
    "def",
    "abbrev",
    "opaque",
    "irreducible_def",
    "structure",
    "class",
    "inductive",
    "instance",
    "alias",
}
SHARD_TO_SOURCE_KEYWORDS = {
    "definition": SOURCE_DEFINITION_KEYWORDS,
    "structure": {"structure"},
    "class": {"class"},
}


class PacketError(RuntimeError):
    """A fail-closed packet validation error."""


@dataclass(frozen=True)
class SourceDeclaration:
    path: str
    line: int
    keyword: str
    source_name: str
    qualified_names: tuple[str, ...]
    header: str
    source_type: str
    is_anonymous: bool


@dataclass(frozen=True)
class ResolvedSource:
    declaration: SourceDeclaration
    mode: str
    matched_name: str


@dataclass(frozen=True)
class CandidateEvidence:
    inventory: dict[str, str]
    axiom: dict[str, str]
    type_row: dict[str, str]
    source: ResolvedSource


@dataclass(frozen=True)
class DefinitionEvidence:
    shard: dict[str, str]
    load: dict[str, str]
    axiom: dict[str, str]
    type_row: dict[str, str]
    source: ResolvedSource
    candidates: tuple[CandidateEvidence, ...]


def _field_limit() -> None:
    """Permit the large raw-expression fields in the V4 type TSV."""

    try:
        csv.field_size_limit(100_000_000)
    except OverflowError:
        csv.field_size_limit(2_000_000_000)


def _read_tsv(path: Path, columns: Sequence[str]) -> list[dict[str, str]]:
    if path.is_symlink() or not path.is_file():
        raise PacketError(f"input is not a physical regular file: {path}")
    _field_limit()
    with path.open(encoding="utf-8", newline="") as handle:
        reader = csv.DictReader(handle, delimiter="\t")
        observed = tuple(reader.fieldnames or ())
        if observed != tuple(columns):
            raise PacketError(
                f"{path}: columns {observed!r}; expected {tuple(columns)!r}"
            )
        rows = list(reader)
    for index, row in enumerate(rows, start=2):
        if None in row or any(value is None for value in row.values()):
            raise PacketError(f"{path}:{index}: malformed TSV row")
        if any("\n" in value or "\t" in value for value in row.values()):
            raise PacketError(
                f"{path}:{index}: decoded field contains a tab or newline"
            )
    return rows


def _write_tsv(
    path: Path, columns: Sequence[str], rows: Iterable[dict[str, str]]
) -> None:
    path.parent.mkdir(parents=True, exist_ok=True)
    with path.open("w", encoding="utf-8", newline="") as handle:
        writer = csv.DictWriter(
            handle,
            fieldnames=columns,
            delimiter="\t",
            lineterminator="\n",
            extrasaction="raise",
        )
        writer.writeheader()
        writer.writerows(rows)


def _safe_source_path(project_root: Path, relative: str) -> Path:
    rel = Path(relative)
    if not relative or rel.is_absolute() or ".." in rel.parts:
        raise PacketError(f"unsafe source path: {relative!r}")
    root = project_root.resolve()
    # Build beneath the canonical root so macOS's /var -> /private/var
    # filesystem alias does not make a TemporaryDirectory fixture appear to
    # traverse a symlink outside the requested project root.
    path = root / rel
    if path.is_symlink() or not path.is_file():
        raise PacketError(f"source is not a physical regular file: {relative}")
    resolved = path.resolve()
    try:
        resolved.relative_to(root)
    except ValueError as error:
        raise PacketError(f"source escapes project root: {relative}") from error
    if resolved != path.absolute():
        raise PacketError(f"source path resolves through a symlink: {relative}")
    return path


def _review_id(name: str) -> str:
    return "v7-def-" + hashlib.sha256(name.encode("utf-8")).hexdigest()[:16]


def _positive_int(value: str, context: str) -> int:
    try:
        result = int(value)
    except ValueError as error:
        raise PacketError(f"{context}: expected integer, got {value!r}") from error
    if result <= 0:
        raise PacketError(f"{context}: expected positive integer, got {result}")
    return result


def _nonnegative_int(value: str, context: str) -> int:
    try:
        result = int(value)
    except ValueError as error:
        raise PacketError(f"{context}: expected integer, got {value!r}") from error
    if result < 0:
        raise PacketError(f"{context}: expected nonnegative integer, got {result}")
    return result


def _index_unique(
    rows: Sequence[dict[str, str]],
    *,
    key_fields: Sequence[str],
    context: str,
) -> dict[tuple[str, ...], dict[str, str]]:
    result: dict[tuple[str, ...], dict[str, str]] = {}
    for index, row in enumerate(rows, start=2):
        key = tuple(row[field] for field in key_fields)
        if any(not item for item in key):
            raise PacketError(f"{context} row {index}: empty key {key!r}")
        if key in result:
            raise PacketError(f"{context} row {index}: duplicate key {key!r}")
        result[key] = row
    return result


def _index_v4(
    axiom_rows: Sequence[dict[str, str]],
    type_rows: Sequence[dict[str, str]],
) -> tuple[
    dict[tuple[str, str], dict[str, str]],
    dict[tuple[str, str], dict[str, str]],
]:
    axioms = _index_unique(
        axiom_rows,
        key_fields=("module", "name"),
        context="V4 axiom inventory",
    )
    types = _index_unique(
        type_rows,
        key_fields=("module", "name"),
        context="V4 type inventory",
    )
    if set(axioms) != set(types):
        missing_types = sorted(set(axioms) - set(types))[:10]
        missing_axioms = sorted(set(types) - set(axioms))[:10]
        raise PacketError(
            "V4 axiom/type key sets differ: "
            f"missing_types={missing_types!r}, "
            f"missing_axioms={missing_axioms!r}"
        )
    for key in sorted(axioms):
        axiom = axioms[key]
        type_row = types[key]
        mismatches = [
            field
            for field in V4_COMMON_COLUMNS
            if axiom[field] != type_row[field]
        ]
        if mismatches:
            raise PacketError(
                f"V4 axiom/type metadata mismatch for {key}: {mismatches}"
            )
        if not type_row["type_raw"] or not type_row["conclusion_raw"]:
            raise PacketError(f"V4 type evidence is empty for {key}")
        _nonnegative_int(
            type_row["binder_count"],
            f"V4 binder_count for {key}",
        )
    return axioms, types


def _namespace_parts(stack: Sequence[tuple[str, tuple[str, ...]]]) -> tuple[str, ...]:
    result: list[str] = []
    for kind, parts in stack:
        if kind == "namespace":
            result.extend(parts)
    return tuple(result)


def _unquote_name(name: str) -> str:
    if name.startswith("«") and name.endswith("»"):
        return name[1:-1]
    return name


def _qualified_names(
    source_name: str, namespace_parts: Sequence[str]
) -> tuple[str, ...]:
    name = _unquote_name(source_name)
    if name.startswith("_root_."):
        return (name.removeprefix("_root_."),)
    variants = {name}
    if namespace_parts:
        variants.add(".".join((*namespace_parts, name)))
    return tuple(sorted(variants, key=lambda item: (-len(item), item)))


def _signature_end(code: str, start: int, name_end: int) -> tuple[int, str]:
    """Return the end of a declaration signature and its terminating mode."""

    round_depth = square_depth = curly_depth = 0
    index = name_end
    limit = min(len(code), start + 100_000)
    while index < limit:
        character = code[index]
        if character == "(":
            round_depth += 1
        elif character == ")":
            round_depth = max(0, round_depth - 1)
        elif character == "[":
            square_depth += 1
        elif character == "]":
            square_depth = max(0, square_depth - 1)
        elif character == "{":
            curly_depth += 1
        elif character == "}":
            curly_depth = max(0, curly_depth - 1)
        at_top = round_depth == square_depth == curly_depth == 0
        if at_top and code.startswith(":=", index):
            return index, "assignment"
        if (
            at_top
            and code.startswith("where", index)
            and (index == 0 or not (code[index - 1].isalnum() or code[index - 1] == "_"))
            and (
                index + 5 == len(code)
                or not (code[index + 5].isalnum() or code[index + 5] == "_")
            )
        ):
            return index + 5, "where"
        if at_top and character == "\n":
            cursor = index + 1
            while cursor < limit and code[cursor] in " \t\r":
                cursor += 1
            if cursor < limit and code[cursor] == "|":
                return index, "equations"
            next_line_end = code.find("\n", cursor, limit)
            if next_line_end < 0:
                next_line_end = limit
            next_line = code[cursor:next_line_end]
            if (
                SOURCE_DECLARATION.match(next_line)
                or SOURCE_ANONYMOUS_INSTANCE.match(next_line)
                or NAMESPACE.match(next_line)
                or END.match(next_line)
            ):
                return index, "next-command"
        index += 1
    raise PacketError("declaration signature exceeds the static scan limit")


def _source_type_from_header(
    code: str, name_end: int, signature_end: int
) -> str:
    round_depth = square_depth = curly_depth = 0
    index = name_end
    colon = -1
    while index < signature_end:
        character = code[index]
        if character == "(":
            round_depth += 1
        elif character == ")":
            round_depth = max(0, round_depth - 1)
        elif character == "[":
            square_depth += 1
        elif character == "]":
            square_depth = max(0, square_depth - 1)
        elif character == "{":
            curly_depth += 1
        elif character == "}":
            curly_depth = max(0, curly_depth - 1)
        elif (
            character == ":"
            and round_depth == square_depth == curly_depth == 0
            and not code.startswith(":=", index)
        ):
            colon = index
            break
        index += 1
    if colon < 0:
        return "(no explicit source result type)"
    return " ".join(code[colon + 1 : signature_end].split())


def _scan_source(project_root: Path, relative: str) -> list[SourceDeclaration]:
    path = _safe_source_path(project_root, relative)
    text = path.read_text(encoding="utf-8")
    code, diagnostics = mask_lean_noncode(text)
    if diagnostics:
        raise PacketError(
            f"{relative}: Lean lexical diagnostics: "
            + ", ".join(kind for kind, _ in diagnostics)
        )

    lines = code.splitlines(keepends=True)
    original_lines = text.splitlines(keepends=True)
    if len(lines) != len(original_lines):
        raise PacketError(f"{relative}: masked/source line count mismatch")
    stack: list[tuple[str, tuple[str, ...]]] = []
    declarations: list[SourceDeclaration] = []
    offset = 0
    for line_number, (line, original_line) in enumerate(
        zip(lines, original_lines, strict=True), start=1
    ):
        stripped = line.rstrip("\r\n")
        if END.fullmatch(stripped):
            if not stack:
                raise PacketError(
                    f"{relative}:{line_number}: unmatched static `end`"
                )
            stack.pop()
            offset += len(line)
            continue
        namespace_match = NAMESPACE.fullmatch(stripped)
        if namespace_match is not None:
            namespace_name = _unquote_name(namespace_match.group("name"))
            stack.append(("namespace", tuple(namespace_name.split("."))))
            offset += len(line)
            continue
        if SECTION.fullmatch(stripped):
            stack.append(("section", ()))
            offset += len(line)
            continue
        if MUTUAL.fullmatch(stripped):
            stack.append(("mutual", ()))
            offset += len(line)
            continue

        declaration_match = SOURCE_DECLARATION.match(stripped)
        anonymous_match = (
            None
            if declaration_match is not None
            else SOURCE_ANONYMOUS_INSTANCE.match(stripped)
        )
        if declaration_match is not None or anonymous_match is not None:
            match = (
                declaration_match
                if declaration_match is not None
                else anonymous_match
            )
            assert match is not None
            is_anonymous = declaration_match is None
            start = offset + match.start("keyword")
            name_end = offset + (
                match.end("keyword")
                if is_anonymous
                else match.end("name")
            )
            signature_end, _mode = _signature_end(code, start, name_end)
            header = " ".join(text[start:signature_end].split())
            if not header:
                raise PacketError(
                    f"{relative}:{line_number}: empty declaration header"
                )
            source_type = _source_type_from_header(
                code, name_end, signature_end
            )
            declarations.append(
                SourceDeclaration(
                    path=relative,
                    line=line_number,
                    keyword=match.group("keyword"),
                    source_name=(
                        "(anonymous instance)"
                        if is_anonymous
                        else match.group("name")
                    ),
                    qualified_names=(
                        ()
                        if is_anonymous
                        else _qualified_names(
                            match.group("name"),
                            _namespace_parts(stack),
                        )
                    ),
                    header=header,
                    source_type=source_type,
                    is_anonymous=is_anonymous,
                )
            )
        offset += len(line)
    # Lean permits a section to run to EOF; several exercise modules use
    # `noncomputable section` as a file-wide scope and close only their nested
    # namespace.  An unclosed namespace or `mutual` block is still rejected
    # because it would make static name resolution suspect.
    unclosed_nonsections = [kind for kind, _parts in stack if kind != "section"]
    if unclosed_nonsections:
        raise PacketError(
            f"{relative}: static non-section block stack is not closed: "
            f"{unclosed_nonsections}"
        )
    return declarations


def _identity_names(row: dict[str, str]) -> tuple[str, ...]:
    values: list[str] = []
    for value in (row.get("private_user_name", ""), row["name"]):
        if value and value not in values:
            values.append(value.removeprefix("_root_."))
    return tuple(values)


GENERATED_AUXILIARY_TAIL = re.compile(
    r"(?:"
    r"eq_\d+|congr_simp|"
    r"_proof_\d+(?:_\d+)*|"
    r"_simp_\d+(?:_\d+)*|"
    r"_abel_\d+(?:_\d+)*"
    r")"
)
GENERATED_STRUCTURE_TAIL = re.compile(
    r"(?:"
    r"[A-Za-z_][A-Za-z0-9_']*|"
    r"mk\.(?:inj|injEq|sizeOf_spec|_flat_ctor|noConfusion|congr_simp)"
    r")"
)


def _generated_tail(identity: str, owner: str) -> str | None:
    if identity.startswith(owner + "."):
        return identity[len(owner) + 1 :]
    marker = "." + owner + "."
    position = identity.rfind(marker)
    if position >= 0:
        return identity[position + len(marker) :]
    return None


def _allowed_generated_owner(
    *,
    identity: str,
    owner: str,
    declaration: SourceDeclaration,
    type_raw: str,
) -> bool:
    """Recognize only audited compiler-child shapes, never any prefix."""

    tail = _generated_tail(identity, owner)
    if tail is None:
        return False
    if GENERATED_AUXILIARY_TAIL.fullmatch(tail):
        return True
    return (
        declaration.keyword in {"structure", "class"}
        and GENERATED_STRUCTURE_TAIL.fullmatch(tail) is not None
        and owner in _raw_constants(type_raw)
    )


def _resolve_source(
    *,
    row: dict[str, str],
    declarations: Sequence[SourceDeclaration],
    expected_keywords: set[str],
    generated_owner_keywords: set[str] = SOURCE_GENERATED_OWNER_KEYWORDS,
    type_raw: str = "",
) -> ResolvedSource:
    identities = _identity_names(row)
    exact: list[tuple[SourceDeclaration, str]] = []
    private_suffix: list[tuple[SourceDeclaration, str]] = []
    generated: list[tuple[int, SourceDeclaration, str]] = []
    for declaration in declarations:
        for qualified in declaration.qualified_names:
            for identity in identities:
                if identity == qualified:
                    exact.append((declaration, qualified))
                elif identity.endswith("." + qualified):
                    private_suffix.append((declaration, qualified))
                elif _allowed_generated_owner(
                    identity=identity,
                    owner=qualified,
                    declaration=declaration,
                    type_raw=type_raw,
                ):
                    generated.append((len(qualified), declaration, qualified))

    def unique(
        values: Sequence[tuple[SourceDeclaration, str]],
        mode: str,
    ) -> ResolvedSource | None:
        deduplicated = {
            (item.path, item.line, item.keyword, matched): item
            for item, matched in values
        }
        if not deduplicated:
            return None
        if len(deduplicated) != 1:
            locations = sorted(
                f"{item.path}:{item.line}:{matched}"
                for item, matched in values
            )
            raise PacketError(
                f"{row['module']}::{row['name']}: ambiguous {mode} "
                f"source declarations {locations}"
            )
        (_key, declaration), = deduplicated.items()
        matched = next(iter(deduplicated))[3]
        allowed_keywords = (
            generated_owner_keywords
            if mode == "compiler-generated-owner"
            else expected_keywords
        )
        if declaration.keyword not in allowed_keywords:
            raise PacketError(
                f"{row['module']}::{row['name']}: source keyword "
                f"{declaration.keyword!r} is incompatible with V4 kind "
                f"{row['kind']!r}"
            )
        resolved_mode = mode
        if mode in {"exact", "private-name"} and declaration.keyword in {
            "alias",
            "instance",
        }:
            resolved_mode = f"{mode}-source-{declaration.keyword}"
        return ResolvedSource(declaration, resolved_mode, matched)

    resolved = unique(exact, "exact")
    if resolved is not None:
        return resolved
    resolved = unique(private_suffix, "private-name")
    if resolved is not None:
        return resolved
    if generated:
        longest = max(item[0] for item in generated)
        selected = [
            (declaration, matched)
            for length, declaration, matched in generated
            if length == longest
        ]
        resolved = unique(selected, "compiler-generated-owner")
        if resolved is not None:
            return resolved
    raise PacketError(
        f"{row['module']}::{row['name']}: no verifiable source declaration "
        f"for identities {identities!r}"
    )


GENERATED_CANDIDATE_OWNER = re.compile(
    r"^(?P<owner>.+)\.(?P<suffix>eq_\d+|congr_simp)$"
)
RAW_CONSTANT = re.compile(r"Lean\.Expr\.const\s+`([^\s\]\)]+)")
SOURCE_TYPE_IDENTIFIER = re.compile(
    r"[A-Za-z_][A-Za-z0-9_']*(?:\.[A-Za-z_][A-Za-z0-9_']*)*"
)


def _raw_constants(raw: str) -> tuple[str, ...]:
    """Return the distinct constant names recorded in one V4 raw type."""

    values: list[str] = []
    for match in RAW_CONSTANT.finditer(raw.replace("\\n", " ")):
        value = match.group(1)
        if value not in values:
            values.append(value)
    return tuple(values)


def _resolve_global_generated_owner(
    *,
    row: dict[str, str],
    type_row: dict[str, str],
    modules_by_name: dict[str, tuple[str, ...]],
    declarations_for_path: Callable[[str], list[SourceDeclaration]],
) -> ResolvedSource | None:
    """Bind a cross-module equation/simp theorem to its source owner."""

    match = GENERATED_CANDIDATE_OWNER.fullmatch(row["name"])
    if match is None:
        return None
    owner = match.group("owner")
    constants = _raw_constants(type_row["type_raw"])
    if owner not in constants:
        raise PacketError(
            f"{row['module']}::{row['name']}: generated owner {owner!r} "
            "is absent from the exact V4 type"
        )
    modules = modules_by_name.get(owner, ())
    if not modules:
        raise PacketError(
            f"{row['module']}::{row['name']}: generated owner {owner!r} "
            "is absent from V4"
        )
    matches: dict[
        tuple[str, int, str, str], tuple[SourceDeclaration, str]
    ] = {}
    for module in modules:
        try:
            path = module_to_source_path(module)
        except ValueError as error:
            raise PacketError(
                f"{row['module']}::{row['name']}: generated owner "
                f"module is invalid: {module!r}"
            ) from error
        for declaration in declarations_for_path(path):
            if (
                declaration.keyword in SOURCE_GENERATED_OWNER_KEYWORDS
                and owner in declaration.qualified_names
            ):
                key = (
                    declaration.path,
                    declaration.line,
                    declaration.keyword,
                    owner,
                )
                matches[key] = (declaration, owner)
    if not matches:
        raise PacketError(
            f"{row['module']}::{row['name']}: no physical source owner "
            f"for generated constant {owner!r}"
        )
    if len(matches) != 1:
        locations = sorted(
            f"{declaration.path}:{declaration.line}:{matched}"
            for declaration, matched in matches.values()
        )
        raise PacketError(
            f"{row['module']}::{row['name']}: ambiguous generated owner "
            f"{owner!r}: {locations}"
        )
    declaration, matched = next(iter(matches.values()))
    suffix = match.group("suffix")
    mode = (
        "generated-equation-owner"
        if suffix.startswith("eq_")
        else "generated-congr-simp-owner"
    )
    return ResolvedSource(declaration, mode, matched)


def _anonymous_instance_signals(
    declaration: SourceDeclaration,
    constants: Sequence[str],
) -> tuple[str, ...] | None:
    """Match a source instance type to V4 constants without elaboration."""

    identifiers = tuple(
        dict.fromkeys(SOURCE_TYPE_IDENTIFIER.findall(declaration.source_type))
    )
    if not identifiers:
        return None
    matched: list[str] = []
    for identifier in identifiers:
        possibilities = [
            constant
            for constant in constants
            if constant == identifier or constant.endswith("." + identifier)
        ]
        if possibilities:
            matched.extend(possibilities)
        elif "." in identifier or identifier[:1].isupper():
            return None
    project_matches = {
        constant
        for constant in matched
        if constant.startswith(("HDP.", "MatrixConcentration."))
    }
    if not project_matches:
        return None
    return tuple(sorted(set(matched)))


def _resolve_anonymous_instance_owner(
    *,
    row: dict[str, str],
    type_row: dict[str, str],
    declarations: Sequence[SourceDeclaration],
    types: dict[tuple[str, str], dict[str, str]],
) -> ResolvedSource | None:
    """Bind a compiler-named theorem to an ordered anonymous instance."""

    short_name = row["name"].rsplit(".", 1)[-1]
    if not short_name.startswith("inst"):
        return None
    constants = _raw_constants(type_row["type_raw"])
    compatible = [
        declaration
        for declaration in declarations
        if declaration.keyword == "instance"
        and declaration.is_anonymous
        and _anonymous_instance_signals(declaration, constants) is not None
    ]
    if not compatible:
        return None

    base_name = row["name"]
    suffix_match = re.fullmatch(r"(?P<base>.+)_(?P<ordinal>\d+)", row["name"])
    if suffix_match is not None:
        possible_base = suffix_match.group("base")
        base_row = types.get((row["module"], possible_base))
        if (
            base_row is not None
            and base_row["type_raw"] == type_row["type_raw"]
        ):
            base_name = possible_base

    sibling_names: list[str] = []
    index = 0
    while True:
        name = base_name if index == 0 else f"{base_name}_{index}"
        sibling = types.get((row["module"], name))
        if sibling is None or sibling["type_raw"] != type_row["type_raw"]:
            break
        sibling_names.append(name)
        index += 1
    if len(sibling_names) != len(compatible):
        locations = [
            f"{item.path}:{item.line}" for item in compatible
        ]
        raise PacketError(
            f"{row['module']}::{row['name']}: ambiguous anonymous instance "
            "anchors; source/V4 ordinal counts differ "
            f"({locations}, V4={sibling_names})"
        )
    if row["name"] not in sibling_names:
        raise PacketError(
            f"{row['module']}::{row['name']}: anonymous instance name is "
            f"not one of the verified V4 ordinals {sibling_names}"
        )
    ordinal = sibling_names.index(row["name"])
    declaration = compatible[ordinal]
    return ResolvedSource(
        declaration,
        "generated-anonymous-instance-owner"
        f"-{ordinal + 1}-of-{len(compatible)}",
        f"anonymous instance ordinal {ordinal + 1}",
    )


def _candidate_cells(
    rows: Sequence[dict[str, str]],
) -> tuple[str, str]:
    names = ";".join(row["candidate_theorem"] for row in rows)
    details = ";".join(
        "|".join(
            (
                row["candidate_theorem"],
                f"module={row['candidate_module']}",
                f"score={row['score']}",
                row["reasons"],
            )
        )
        for row in rows
    )
    return names, details


def _validate_candidates(
    rows: Sequence[dict[str, str]],
) -> dict[str, list[dict[str, str]]]:
    grouped: dict[str, list[dict[str, str]]] = {}
    seen: set[tuple[str, str]] = set()
    for index, row in enumerate(rows, start=2):
        context = f"candidate inventory row {index}"
        required = (
            "target_module",
            "target",
            "target_kind",
            "candidate_module",
            "candidate_theorem",
            "origin",
            "score",
        )
        missing = [field for field in required if not row[field]]
        if missing:
            raise PacketError(f"{context}: empty fields {missing}")
        if row["origin"] != "type":
            raise PacketError(f"{context}: origin must be `type`")
        if row["target_kind"] not in SHARD_TO_SOURCE_KEYWORDS:
            raise PacketError(
                f"{context}: unsupported target kind {row['target_kind']!r}"
            )
        _positive_int(row["score"], f"{context} score")
        try:
            module_to_source_path(row["target_module"])
            module_to_source_path(row["candidate_module"])
        except ValueError as error:
            raise PacketError(f"{context}: {error}") from error
        key = (row["target"], row["candidate_theorem"])
        if key in seen:
            raise PacketError(f"{context}: duplicate candidate key {key}")
        seen.add(key)
        grouped.setdefault(row["target"], []).append(row)
    for target in grouped:
        grouped[target].sort(
            key=lambda row: (
                -int(row["score"]),
                row["candidate_theorem"],
            )
        )
    return grouped


def _validate_load_and_shard(
    load_rows: Sequence[dict[str, str]],
    shard_rows: Sequence[dict[str, str]],
    candidates: dict[str, list[dict[str, str]]],
) -> list[tuple[dict[str, str], dict[str, str], list[dict[str, str]]]]:
    loads = _index_unique(
        load_rows,
        key_fields=("name",),
        context="load-bearing inventory",
    )
    seen_names: set[str] = set()
    seen_ids: set[str] = set()
    result = []
    for index, shard in enumerate(shard_rows, start=2):
        context = f"shard row {index}"
        name = shard["name"]
        if not name:
            raise PacketError(f"{context}: empty definition name")
        if name in seen_names:
            raise PacketError(f"{context}: duplicate definition name {name}")
        seen_names.add(name)
        review_id = shard["review_id"]
        if review_id in seen_ids:
            raise PacketError(f"{context}: duplicate review_id {review_id}")
        seen_ids.add(review_id)
        load = loads.get((name,))
        if load is None:
            raise PacketError(
                f"{context}: definition {name!r} is absent from "
                "definition_load_bearing.tsv"
            )
        if shard["contract_version"] != CONTRACT_VERSION:
            raise PacketError(f"{context}: contract_version changed")
        if shard["review_id"] != _review_id(name):
            raise PacketError(f"{context}: review_id/name mismatch")
        _positive_int(shard["shard"], f"{context} shard")
        if shard["candidate_disposition"] != CANDIDATE_DISPOSITION:
            raise PacketError(f"{context}: candidate disposition changed")

        comparisons = {
            "module": "module",
            "source_path": "source_path",
            "name": "name",
            "kind": "kind",
            "is_private": "is_private",
            "private_user_name": "private_user_name",
            "is_internal": "is_internal",
            "load_bearing_reason": "reason",
            "tier_b_endpoint_count": "tier_b_endpoint_count",
            "tier_b_type_endpoint_count": "tier_b_type_endpoint_count",
            "tier_b_value_endpoint_count": "tier_b_value_endpoint_count",
        }
        mismatches = [
            f"{shard_field}={shard[shard_field]!r} != {load_field}={load[load_field]!r}"
            for shard_field, load_field in comparisons.items()
            if shard[shard_field] != load[load_field]
        ]
        if mismatches:
            raise PacketError(
                f"{context}: shard/load-bearing metadata mismatch: "
                + "; ".join(mismatches)
            )
        try:
            expected_path = module_to_source_path(shard["module"])
        except ValueError as error:
            raise PacketError(f"{context}: {error}") from error
        if shard["source_path"] != expected_path:
            raise PacketError(
                f"{context}: source_path {shard['source_path']!r} does not "
                f"match module path {expected_path!r}"
            )
        if shard["kind"] not in SHARD_TO_SOURCE_KEYWORDS:
            raise PacketError(
                f"{context}: unsupported load-bearing kind {shard['kind']!r}"
            )
        for field in (
            "tier_b_endpoint_count",
            "tier_b_type_endpoint_count",
            "tier_b_value_endpoint_count",
        ):
            _nonnegative_int(shard[field], f"{context} {field}")

        candidate_rows = candidates.get(name, [])
        for candidate in candidate_rows:
            if (
                candidate["target_module"] != shard["module"]
                or candidate["target_kind"] != shard["kind"]
            ):
                raise PacketError(
                    f"{context}: candidate target metadata differs for "
                    f"{candidate['candidate_theorem']}"
                )
        expected_names, expected_details = _candidate_cells(candidate_rows)
        expected_candidate_metadata = {
            "candidate_count": str(len(candidate_rows)),
            "candidate_theorems": expected_names,
            "candidate_details": expected_details,
        }
        changed = [
            f"{field}={shard[field]!r} expected {expected!r}"
            for field, expected in expected_candidate_metadata.items()
            if shard[field] != expected
        ]
        if changed:
            raise PacketError(
                f"{context}: shard/candidate inventory mismatch: "
                + "; ".join(changed)
            )
        result.append((shard, load, candidate_rows))
    if not result:
        raise PacketError("review shard contains no rows")
    return result


def _require_v4(
    *,
    module: str,
    name: str,
    axioms: dict[tuple[str, str], dict[str, str]],
    types: dict[tuple[str, str], dict[str, str]],
) -> tuple[dict[str, str], dict[str, str]]:
    key = (module, name)
    axiom = axioms.get(key)
    type_row = types.get(key)
    if axiom is None or type_row is None:
        raise PacketError(f"{module}::{name}: declaration is absent from V4")
    return axiom, type_row


def _join_evidence(
    *,
    project_root: Path,
    joined_rows: Sequence[
        tuple[dict[str, str], dict[str, str], list[dict[str, str]]]
    ],
    axioms: dict[tuple[str, str], dict[str, str]],
    types: dict[tuple[str, str], dict[str, str]],
) -> list[DefinitionEvidence]:
    source_cache: dict[str, list[SourceDeclaration]] = {}
    module_sets_by_name: dict[str, set[str]] = {}
    for module, name in axioms:
        module_sets_by_name.setdefault(name, set()).add(module)
    modules_by_name = {
        name: tuple(sorted(modules))
        for name, modules in module_sets_by_name.items()
    }

    def declarations(relative: str) -> list[SourceDeclaration]:
        if relative not in source_cache:
            source_cache[relative] = _scan_source(project_root, relative)
        return source_cache[relative]

    evidence: list[DefinitionEvidence] = []
    for shard, load, candidate_rows in joined_rows:
        axiom, type_row = _require_v4(
            module=shard["module"],
            name=shard["name"],
            axioms=axioms,
            types=types,
        )
        metadata_mismatches = [
            field
            for field in (
                "module",
                "name",
                "is_private",
                "private_user_name",
                "is_internal",
            )
            if axiom[field] != shard[field]
        ]
        if metadata_mismatches:
            raise PacketError(
                f"{shard['module']}::{shard['name']}: shard/V4 metadata "
                f"mismatch in {metadata_mismatches}"
            )
        v4_kind_matches = axiom["kind"] == shard["kind"]
        v4_inductive_source_kind = (
            shard["kind"] in {"structure", "class"}
            and axiom["kind"] == "inductive"
        )
        if not (v4_kind_matches or v4_inductive_source_kind):
            raise PacketError(
                f"{shard['module']}::{shard['name']}: shard/V4 metadata "
                "mismatch in ['kind']"
            )
        definition_source = _resolve_source(
            row=axiom,
            declarations=declarations(shard["source_path"]),
            expected_keywords=SHARD_TO_SOURCE_KEYWORDS[shard["kind"]],
            type_raw=type_row["type_raw"],
        )
        if v4_inductive_source_kind:
            if definition_source.declaration.keyword != shard["kind"]:
                raise PacketError(
                    f"{shard['module']}::{shard['name']}: V4 `inductive` "
                    f"cannot be normalized to source {shard['kind']!r}"
                )
            definition_source = ResolvedSource(
                definition_source.declaration,
                f"v4-inductive-source-{shard['kind']}",
                definition_source.matched_name,
            )

        candidate_evidence: list[CandidateEvidence] = []
        for candidate in candidate_rows:
            candidate_axiom, candidate_type = _require_v4(
                module=candidate["candidate_module"],
                name=candidate["candidate_theorem"],
                axioms=axioms,
                types=types,
            )
            if candidate_axiom["kind"] != "theorem":
                raise PacketError(
                    f"{candidate['candidate_module']}::"
                    f"{candidate['candidate_theorem']}: candidate is "
                    f"{candidate_axiom['kind']!r} in V4, not theorem"
                )
            if candidate_type["kind"] != "theorem":
                raise PacketError(
                    f"{candidate['candidate_theorem']}: V4 type kind is not theorem"
                )
            candidate_constants = _raw_constants(candidate_type["type_raw"])
            if candidate["target"] not in candidate_constants:
                raise PacketError(
                    f"{candidate['candidate_module']}::"
                    f"{candidate['candidate_theorem']}: exact V4 type does "
                    f"not reference target {candidate['target']!r}"
                )
            candidate_path = module_to_source_path(
                candidate["candidate_module"]
            )
            candidate_declarations = declarations(candidate_path)
            try:
                candidate_source = _resolve_source(
                    row=candidate_axiom,
                    declarations=candidate_declarations,
                    expected_keywords=SOURCE_CANDIDATE_KEYWORDS,
                    type_raw=candidate_type["type_raw"],
                )
            except PacketError as direct_error:
                if "no verifiable source declaration" not in str(direct_error):
                    raise
                candidate_source = _resolve_global_generated_owner(
                    row=candidate_axiom,
                    type_row=candidate_type,
                    modules_by_name=modules_by_name,
                    declarations_for_path=declarations,
                )
                if candidate_source is None:
                    candidate_source = _resolve_anonymous_instance_owner(
                        row=candidate_axiom,
                        type_row=candidate_type,
                        declarations=candidate_declarations,
                        types=types,
                    )
                if candidate_source is None:
                    raise direct_error
            candidate_evidence.append(
                CandidateEvidence(
                    inventory=candidate,
                    axiom=candidate_axiom,
                    type_row=candidate_type,
                    source=candidate_source,
                )
            )
        evidence.append(
            DefinitionEvidence(
                shard=shard,
                load=load,
                axiom=axiom,
                type_row=type_row,
                source=definition_source,
                candidates=tuple(candidate_evidence),
            )
        )
    return evidence


def _markdown_cell(text: str) -> str:
    return text.replace("\\", "\\\\").replace("|", "\\|").replace("\n", " ")


def _code_fence(text: str, language: str = "text") -> str:
    fence = "```"
    while fence in text:
        fence += "`"
    return f"{fence}{language}\n{text}\n{fence}"


def _raw_expr_summary(raw: str, *, maximum: int = 600) -> str:
    compact = " ".join(
        raw.replace("\\n", " ").replace("\\t", " ").split()
    )
    constants: list[str] = []
    for match in re.finditer(r"Lean\.Expr\.const\s+`([^\s\]\)]+)", compact):
        value = match.group(1)
        if value not in constants:
            constants.append(value)
    literals: list[str] = []
    for match in re.finditer(r"Lean\.Literal\.natVal\s+(\d+)", compact):
        value = match.group(1)
        if value not in literals:
            literals.append(value)
    bvars = len(re.findall(r"Lean\.Expr\.bvar\s+\d+", compact))
    if len(compact) > maximum:
        omitted = len(compact) - maximum
        compact = compact[:maximum].rstrip() + f" … [truncated {omitted} chars]"
    metadata = [
        "constants=" + (", ".join(constants[:16]) if constants else "(none)"),
        "nat_literals=" + (", ".join(literals[:16]) if literals else "(none)"),
        f"bvar_occurrences={bvars}",
    ]
    return "; ".join(metadata) + "\nraw: " + compact


def _axioms(text: str) -> str:
    return text if text else "(none)"


def _render_packet(
    *,
    shard_path: Path,
    evidence: Sequence[DefinitionEvidence],
) -> str:
    shard_ids = sorted({item.shard["shard"] for item in evidence}, key=int)
    candidate_count = sum(len(item.candidates) for item in evidence)
    lines = [
        "# V7 load-bearing definition review packet",
        "",
        "This is a deterministic static reading aid. It copies current review "
        "fields but does not promote a candidate, decide nontriviality, or "
        "change any shard status. Candidate rows are discovery metadata only.",
        "",
        f"- Source shard: `{shard_path.as_posix()}`",
        f"- Shard ID(s): {', '.join(shard_ids)}",
        f"- Load-bearing definitions: {len(evidence)}",
        f"- Candidate theorem rows: {candidate_count}",
        "- Source locations are derived from physical, lexer-checked Lean files.",
        "- V4 joins require exact module/name keys and matching axiom/type metadata.",
        "",
    ]
    for ordinal, item in enumerate(evidence, start=1):
        shard = item.shard
        source = item.source.declaration
        lines.extend(
            (
                f"## {ordinal}. `{shard['name']}`",
                "",
                "| Field | Value |",
                "|---|---|",
                f"| Module | `{_markdown_cell(shard['module'])}` |",
                f"| Kind | `{_markdown_cell(shard['kind'])}` |",
                f"| Review ID | `{_markdown_cell(shard['review_id'])}` |",
                f"| Current shard status (copied, not evaluated) | "
                f"`{_markdown_cell(shard['review_status'])}` |",
                f"| Load-bearing reason | `{_markdown_cell(shard['load_bearing_reason'])}` |",
                f"| Tier-B endpoints (union/type/value) | "
                f"{shard['tier_b_endpoint_count']} / "
                f"{shard['tier_b_type_endpoint_count']} / "
                f"{shard['tier_b_value_endpoint_count']} |",
                f"| Private / internal | {shard['is_private']} / {shard['is_internal']} |",
                f"| Candidate disposition | `{_markdown_cell(shard['candidate_disposition'])}` |",
                "",
                "### Definition source and V4 record",
                "",
                f"- Canonical source location: `{source.path}:{source.line}`",
                f"- Source resolution: `{item.source.mode}` via "
                f"`{_markdown_cell(item.source.matched_name)}`",
                f"- V4 axioms: `{_markdown_cell(_axioms(item.axiom['axioms']))}`",
                f"- V4 binder count: {item.type_row['binder_count']}",
                f"- V4 level parameters: "
                f"`{_markdown_cell(item.type_row['level_params'] or '(none)')}`",
                "",
                "Canonical source declaration header:",
                "",
                _code_fence(source.header, "lean"),
                "",
                "Normalized source result type:",
                "",
                _code_fence(source.source_type, "lean"),
                "",
                "Simplified V4 type:",
                "",
                _code_fence(_raw_expr_summary(item.type_row["type_raw"])),
                "",
                "Simplified V4 conclusion:",
                "",
                _code_fence(
                    _raw_expr_summary(item.type_row["conclusion_raw"])
                ),
                "",
                "### Candidate theorems",
                "",
            )
        )
        if not item.candidates:
            lines.extend(
                (
                    "**NO CANDIDATE THEOREM RECORDED.** This is an explicit "
                    "inventory fact, not a semantic verdict. A reviewer may "
                    "need a compiled witness or an `UNVERIFIED_SANITY` finding.",
                    "",
                )
            )
        for candidate_index, candidate in enumerate(item.candidates, start=1):
            inventory = candidate.inventory
            candidate_source = candidate.source.declaration
            lines.extend(
                (
                    f"#### Candidate {candidate_index}: "
                    f"`{inventory['candidate_theorem']}`",
                    "",
                    f"- Candidate score: **{inventory['score']}**",
                    f"- Score reasons: "
                    f"`{_markdown_cell(inventory['reasons'] or '(none)')}`",
                    f"- Candidate module: "
                    f"`{_markdown_cell(inventory['candidate_module'])}`",
                    f"- Canonical source location: "
                    f"`{candidate_source.path}:{candidate_source.line}`",
                    f"- Source resolution: `{candidate.source.mode}` via "
                    f"`{_markdown_cell(candidate.source.matched_name)}`",
                    f"- V4 kind: `{candidate.axiom['kind']}`",
                    f"- V4 axioms: "
                    f"`{_markdown_cell(_axioms(candidate.axiom['axioms']))}`",
                    f"- V4 binder count: {candidate.type_row['binder_count']}",
                    "",
                    "Canonical source declaration header:",
                    "",
                    _code_fence(candidate_source.header, "lean"),
                    "",
                    "Normalized source declaration type:",
                    "",
                    _code_fence(candidate_source.source_type, "lean"),
                    "",
                    "Simplified V4 type:",
                    "",
                    _code_fence(
                        _raw_expr_summary(candidate.type_row["type_raw"])
                    ),
                    "",
                    "Simplified V4 conclusion:",
                    "",
                    _code_fence(
                        _raw_expr_summary(
                            candidate.type_row["conclusion_raw"]
                        )
                    ),
                    "",
                )
            )
        lines.extend(
            (
                "### Existing human-review fields (copied verbatim)",
                "",
                "| Field | Value |",
                "|---|---|",
            )
        )
        for field in REVIEW_COLUMNS[18:]:
            lines.append(
                f"| `{field}` | {_markdown_cell(shard[field]) or '*(empty)*'} |"
            )
        lines.append("")
    return "\n".join(lines).rstrip() + "\n"


def build_packet(
    *,
    project_root: Path,
    shard_path: Path,
    output_path: Path,
    load_path: Path,
    candidate_path: Path,
    v4_axiom_path: Path,
    v4_type_path: Path,
) -> str:
    inputs = {
        shard_path.resolve(),
        load_path.resolve(),
        candidate_path.resolve(),
        v4_axiom_path.resolve(),
        v4_type_path.resolve(),
    }
    if output_path.resolve() in inputs:
        raise PacketError("output path must differ from every input path")
    shard_rows = _read_tsv(shard_path, REVIEW_COLUMNS)
    load_rows = _read_tsv(load_path, LOAD_BEARING_COLUMNS)
    candidate_rows = _read_tsv(candidate_path, CANDIDATE_COLUMNS)
    axiom_rows = _read_tsv(v4_axiom_path, V4_AXIOM_COLUMNS)
    type_rows = _read_tsv(v4_type_path, V4_TYPE_COLUMNS)
    candidate_groups = _validate_candidates(candidate_rows)
    joined_rows = _validate_load_and_shard(
        load_rows, shard_rows, candidate_groups
    )
    axioms, types = _index_v4(axiom_rows, type_rows)
    evidence = _join_evidence(
        project_root=project_root,
        joined_rows=joined_rows,
        axioms=axioms,
        types=types,
    )
    rendered = _render_packet(shard_path=shard_path, evidence=evidence)
    output_path.parent.mkdir(parents=True, exist_ok=True)
    output_path.write_text(rendered, encoding="utf-8")
    return rendered


def _synthetic_rows(
    project_root: Path,
) -> tuple[
    Path,
    Path,
    Path,
    Path,
    Path,
]:
    source_relative = "HighDimensionalProbability/Prelude/SyntheticPacket.lean"
    source = project_root / source_relative
    source.parent.mkdir(parents=True, exist_ok=True)
    source.write_text(
        "\n".join(
            (
                "namespace HDP",
                "def syntheticPacketDef : Nat := 1",
                "theorem syntheticPacketDef_pos : 0 < syntheticPacketDef := by decide",
                "def syntheticNoCandidateDef : Nat := 2",
                "end HDP",
                "",
            )
        ),
        encoding="utf-8",
    )
    module = "HighDimensionalProbability.Prelude.SyntheticPacket"
    load_path = project_root / "definition_load_bearing.tsv"
    candidate_path = (
        project_root / "definition_nontriviality_candidates.tsv"
    )
    shard_path = project_root / "shard.tsv"
    axiom_path = project_root / "v4_axioms.tsv"
    type_path = project_root / "v4_types.tsv"
    load_rows = [
        {
            "module": module,
            "source_path": source_relative,
            "name": "HDP.syntheticPacketDef",
            "kind": "definition",
            "is_private": "false",
            "private_user_name": "",
            "is_internal": "false",
            "reason": "all_prelude_defs_structures_classes",
            "tier_b_endpoint_count": "3",
            "tier_b_type_endpoint_count": "3",
            "tier_b_value_endpoint_count": "0",
        },
        {
            "module": module,
            "source_path": source_relative,
            "name": "HDP.syntheticNoCandidateDef",
            "kind": "definition",
            "is_private": "false",
            "private_user_name": "",
            "is_internal": "false",
            "reason": "all_prelude_defs_structures_classes",
            "tier_b_endpoint_count": "0",
            "tier_b_type_endpoint_count": "0",
            "tier_b_value_endpoint_count": "0",
        },
    ]
    candidate_rows = [
        {
            "target_module": module,
            "target": "HDP.syntheticPacketDef",
            "target_kind": "definition",
            "candidate_module": module,
            "candidate_theorem": "HDP.syntheticPacketDef_pos",
            "origin": "type",
            "score": "12",
            "reasons": "statement-direct,public-name,nontriviality-lexeme",
        }
    ]
    _write_tsv(load_path, LOAD_BEARING_COLUMNS, load_rows)
    _write_tsv(candidate_path, CANDIDATE_COLUMNS, candidate_rows)

    shard_rows = []
    for load in load_rows:
        candidates = [
            row for row in candidate_rows if row["target"] == load["name"]
        ]
        names, details = _candidate_cells(candidates)
        shard_rows.append(
            {
                "contract_version": CONTRACT_VERSION,
                "review_id": _review_id(load["name"]),
                "shard": "1",
                "module": load["module"],
                "source_path": load["source_path"],
                "name": load["name"],
                "kind": load["kind"],
                "is_private": load["is_private"],
                "private_user_name": load["private_user_name"],
                "is_internal": load["is_internal"],
                "load_bearing_reason": load["reason"],
                "tier_b_endpoint_count": load["tier_b_endpoint_count"],
                "tier_b_type_endpoint_count": load[
                    "tier_b_type_endpoint_count"
                ],
                "tier_b_value_endpoint_count": load[
                    "tier_b_value_endpoint_count"
                ],
                "candidate_count": str(len(candidates)),
                "candidate_theorems": names,
                "candidate_details": details,
                "candidate_disposition": CANDIDATE_DISPOSITION,
                "review_status": "UNREVIEWED",
                **{field: "" for field in REVIEW_COLUMNS[19:]},
            }
        )
    _write_tsv(shard_path, REVIEW_COLUMNS, shard_rows)

    common = {
        "module": module,
        "is_private": "false",
        "private_user_name": "",
        "is_internal": "false",
    }
    axiom_rows = [
        {
            **common,
            "name": "HDP.syntheticPacketDef",
            "kind": "definition",
            "axioms": "",
        },
        {
            **common,
            "name": "HDP.syntheticPacketDef_pos",
            "kind": "theorem",
            "axioms": "propext",
        },
        {
            **common,
            "name": "HDP.syntheticNoCandidateDef",
            "kind": "definition",
            "axioms": "",
        },
    ]
    _write_tsv(axiom_path, V4_AXIOM_COLUMNS, axiom_rows)
    type_rows = [
        {
            **{field: row[field] for field in V4_COMMON_COLUMNS},
            "level_params": "",
            "binder_count": "0",
            "type_raw": "Lean.Expr.const `Nat []",
            "conclusion_raw": "Lean.Expr.const `Nat []",
        }
        for row in axiom_rows
    ]
    theorem_type = next(
        row
        for row in type_rows
        if row["name"] == "HDP.syntheticPacketDef_pos"
    )
    theorem_type["type_raw"] = (
        "Lean.Expr.app (Lean.Expr.const `LT.lt []) "
        "(Lean.Expr.const `HDP.syntheticPacketDef [])"
    )
    theorem_type["conclusion_raw"] = theorem_type["type_raw"]
    _write_tsv(type_path, V4_TYPE_COLUMNS, type_rows)
    return load_path, candidate_path, shard_path, axiom_path, type_path


def _expect_rejection(
    action,
    *,
    contains: str,
    label: str,
) -> None:
    try:
        action()
    except PacketError as error:
        if contains not in str(error):
            raise AssertionError(
                f"{label}: wrong rejection: {error}"
            ) from error
    else:
        raise AssertionError(f"{label}: invalid evidence was accepted")


def self_test() -> int:
    with tempfile.TemporaryDirectory(
        prefix="hdp-v7-review-packet-"
    ) as temporary:
        project_root = Path(temporary)

        def fresh():
            return _synthetic_rows(project_root)

        load, candidates, shard, axioms, types = fresh()
        output = project_root / "packet.md"
        rendered = build_packet(
            project_root=project_root,
            shard_path=shard,
            output_path=output,
            load_path=load,
            candidate_path=candidates,
            v4_axiom_path=axioms,
            v4_type_path=types,
        )
        required_fragments = (
            "HDP.syntheticPacketDef",
            "HDP.syntheticPacketDef_pos",
            f"{load.parent.name}/Prelude/SyntheticPacket.lean:3",
            "Candidate score: **12**",
            "V4 axioms: `propext`",
            "NO CANDIDATE THEOREM RECORDED",
            "Simplified V4 conclusion",
        )
        # The synthetic root directory has no stable basename contract, so
        # source locations are checked separately below.
        required_fragments = tuple(
            fragment
            for fragment in required_fragments
            if not fragment.endswith("SyntheticPacket.lean:3")
        )
        if not all(fragment in rendered for fragment in required_fragments):
            raise AssertionError("baseline packet lacks required review fields")
        if (
            "HighDimensionalProbability/Prelude/SyntheticPacket.lean:2"
            not in rendered
            or "HighDimensionalProbability/Prelude/SyntheticPacket.lean:3"
            not in rendered
        ):
            raise AssertionError("baseline source locations are not exact")

        synthetic_module = (
            "HighDimensionalProbability.Prelude.SyntheticPacket"
        )
        synthetic_source = (
            "HighDimensionalProbability/Prelude/SyntheticPacket.lean"
        )
        generated_row = {
            "module": synthetic_module,
            "name": "HDP.syntheticPacketDef.eq_1",
        }
        generated_type = {
            "type_raw": (
                "Lean.Expr.const `HDP.syntheticNoCandidateDef []"
            )
        }
        _expect_rejection(
            lambda: _resolve_global_generated_owner(
                row=generated_row,
                type_row=generated_type,
                modules_by_name={
                    "HDP.syntheticPacketDef": (synthetic_module,)
                },
                declarations_for_path=lambda path: _scan_source(
                    project_root, path
                ),
            ),
            contains="absent from the exact V4 type",
            label="wrong generated owner",
        )

        duplicate_module = (
            "HighDimensionalProbability.Prelude.SyntheticPacketDuplicate"
        )
        duplicate_source = (
            project_root
            / "HighDimensionalProbability"
            / "Prelude"
            / "SyntheticPacketDuplicate.lean"
        )
        duplicate_source.write_text(
            "\n".join(
                (
                    "namespace HDP",
                    "def syntheticPacketDef : Nat := 7",
                    "end HDP",
                    "",
                )
            ),
            encoding="utf-8",
        )
        generated_type["type_raw"] = (
            "Lean.Expr.const `HDP.syntheticPacketDef []"
        )
        _expect_rejection(
            lambda: _resolve_global_generated_owner(
                row=generated_row,
                type_row=generated_type,
                modules_by_name={
                    "HDP.syntheticPacketDef": (
                        synthetic_module,
                        duplicate_module,
                    )
                },
                declarations_for_path=lambda path: _scan_source(
                    project_root, path
                ),
            ),
            contains="ambiguous generated owner",
            label="ambiguous generated owner",
        )

        load, candidates, shard, axioms, types = fresh()
        load_rows = _read_tsv(load, LOAD_BEARING_COLUMNS)
        candidate_rows = _read_tsv(candidates, CANDIDATE_COLUMNS)
        shard_rows = _read_tsv(shard, REVIEW_COLUMNS)
        axiom_rows = _read_tsv(axioms, V4_AXIOM_COLUMNS)
        type_rows = _read_tsv(types, V4_TYPE_COLUMNS)
        load_rows[0]["kind"] = "structure"
        candidate_rows[0]["target_kind"] = "structure"
        shard_rows[0]["kind"] = "structure"
        for row in axiom_rows:
            if row["name"] == "HDP.syntheticPacketDef":
                row["kind"] = "inductive"
        for row in type_rows:
            if row["name"] == "HDP.syntheticPacketDef":
                row["kind"] = "inductive"
        _write_tsv(load, LOAD_BEARING_COLUMNS, load_rows)
        _write_tsv(candidates, CANDIDATE_COLUMNS, candidate_rows)
        _write_tsv(shard, REVIEW_COLUMNS, shard_rows)
        _write_tsv(axioms, V4_AXIOM_COLUMNS, axiom_rows)
        _write_tsv(types, V4_TYPE_COLUMNS, type_rows)
        _expect_rejection(
            lambda: build_packet(
                project_root=project_root,
                shard_path=shard,
                output_path=output,
                load_path=load,
                candidate_path=candidates,
                v4_axiom_path=axioms,
                v4_type_path=types,
            ),
            contains="source keyword 'def' is incompatible",
            label="wrong normalized source kind",
        )

        load, candidates, shard, axioms, types = fresh()
        axiom_rows = _read_tsv(axioms, V4_AXIOM_COLUMNS)
        _write_tsv(
            axioms,
            V4_AXIOM_COLUMNS,
            [
                row
                for row in axiom_rows
                if row["name"] != "HDP.syntheticPacketDef_pos"
            ],
        )
        _expect_rejection(
            lambda: build_packet(
                project_root=project_root,
                shard_path=shard,
                output_path=output,
                load_path=load,
                candidate_path=candidates,
                v4_axiom_path=axioms,
                v4_type_path=types,
            ),
            contains="V4 axiom/type key sets differ",
            label="missing V4 candidate",
        )

        load, candidates, shard, axioms, types = fresh()
        axiom_rows = _read_tsv(axioms, V4_AXIOM_COLUMNS)
        type_rows = _read_tsv(types, V4_TYPE_COLUMNS)
        for row in axiom_rows:
            if row["name"] == "HDP.syntheticPacketDef_pos":
                row["kind"] = "definition"
        for row in type_rows:
            if row["name"] == "HDP.syntheticPacketDef_pos":
                row["kind"] = "definition"
        _write_tsv(axioms, V4_AXIOM_COLUMNS, axiom_rows)
        _write_tsv(types, V4_TYPE_COLUMNS, type_rows)
        _expect_rejection(
            lambda: build_packet(
                project_root=project_root,
                shard_path=shard,
                output_path=output,
                load_path=load,
                candidate_path=candidates,
                v4_axiom_path=axioms,
                v4_type_path=types,
            ),
            contains="not theorem",
            label="wrong V4 candidate kind",
        )

        load, candidates, shard, axioms, types = fresh()
        shard_rows = _read_tsv(shard, REVIEW_COLUMNS)
        shard_rows[0]["candidate_count"] = "0"
        _write_tsv(shard, REVIEW_COLUMNS, shard_rows)
        _expect_rejection(
            lambda: build_packet(
                project_root=project_root,
                shard_path=shard,
                output_path=output,
                load_path=load,
                candidate_path=candidates,
                v4_axiom_path=axioms,
                v4_type_path=types,
            ),
            contains="shard/candidate inventory mismatch",
            label="shard metadata mismatch",
        )

        load, candidates, shard, axioms, types = fresh()
        source = (
            project_root
            / "HighDimensionalProbability"
            / "Prelude"
            / "SyntheticPacket.lean"
        )
        source.write_text(
            source.read_text(encoding="utf-8").replace(
                "theorem syntheticPacketDef_pos : "
                "0 < syntheticPacketDef := by decide\n",
                "",
            ),
            encoding="utf-8",
        )
        _expect_rejection(
            lambda: build_packet(
                project_root=project_root,
                shard_path=shard,
                output_path=output,
                load_path=load,
                candidate_path=candidates,
                v4_axiom_path=axioms,
                v4_type_path=types,
            ),
            contains="no verifiable source declaration",
            label="missing source theorem",
        )

    print(
        "PASS: V7 review-packet synthetic calibration; baseline definition, "
        "candidate, no-candidate, source-location, simplified type/conclusion, "
        "V4 axiom, and score fields rendered; missing V4, shard metadata "
        "mismatch, wrong candidate kind, wrong generated owner, wrong "
        "normalized source kind, ambiguous generated owner, and missing "
        "source declaration were rejected"
    )
    return 0


def _resolve(path: Path) -> Path:
    return path if path.is_absolute() else ROOT / path


def _parse_args(argv: Sequence[str]) -> argparse.Namespace:
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--self-test", action="store_true")
    parser.add_argument("--shard", type=Path)
    parser.add_argument("--output", type=Path)
    args = parser.parse_args(argv)
    if args.self_test:
        if args.shard is not None or args.output is not None:
            parser.error("--self-test cannot be combined with --shard/--output")
    elif args.shard is None or args.output is None:
        parser.error("--shard and --output are both required")
    return args


def main(argv: Sequence[str] | None = None) -> int:
    args = _parse_args(sys.argv[1:] if argv is None else argv)
    if args.self_test:
        return self_test()
    assert args.shard is not None and args.output is not None
    try:
        rendered = build_packet(
            project_root=ROOT,
            shard_path=_resolve(args.shard),
            output_path=_resolve(args.output),
            load_path=LOAD_BEARING,
            candidate_path=NONTRIVIALITY_CANDIDATES,
            v4_axiom_path=DEFAULT_V4_AXIOMS,
            v4_type_path=DEFAULT_V4_TYPES,
        )
    except (PacketError, OSError, UnicodeError, ValueError) as error:
        print(f"V7 review packet FAILED: {error}", file=sys.stderr)
        return 1
    print(
        f"V7 review packet PASS: wrote {_resolve(args.output)} "
        f"({len(rendered.encode('utf-8'))} bytes)"
    )
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
