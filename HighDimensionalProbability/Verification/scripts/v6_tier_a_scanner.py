#!/usr/bin/env python3
"""Source-level V6 Tier-A theorem-statement vacuity triage.

The extractor enumerates every source ``theorem`` and ``lemma`` command in the
selected FILE-WALK scope.  It is deliberately a triage scanner, not a proof of
vacuity: every reason is a syntactic red flag that must be reviewed in Tier B.
The JSON output retains all declarations, including unflagged statements and
parse diagnostics, so coverage cannot be silently narrowed.
"""

from __future__ import annotations

import argparse
import csv
import json
import re
import sys
from dataclasses import asdict, dataclass, field
from decimal import Decimal, InvalidOperation
from pathlib import Path
from typing import Iterable, Sequence

from file_universe import ROOT
from lean_source_scanner import mask_lean_noncode, paths_for_scope


DECLARATION_START = re.compile(
    r"""(?mx)
    ^[ \t]*
    (?:
      @\[[^\r\n]*\][ \t]*
    )?
    (?:
      (?:private|protected|noncomputable|unsafe|local)[ \t]+
    )*
    (?P<kind>theorem|lemma)[ \t]+
    (?P<name>«[^»]+»|[^\s(\[{:="]+)
    """
)

SCOPE_COMMAND_START = re.compile(
    r"(?m)^[ \t]*(?P<kind>namespace|section|end|variable)\b"
)
LEAN_IDENTIFIER = re.compile(r"«[^»]+»|[^\W\d][\w'₀-₉]*|_", re.UNICODE)

OPEN_TO_CLOSE = {
    "(": ")",
    "[": "]",
    "{": "}",
    "⦃": "⦄",
    "⟨": "⟩",
}
CLOSE_TO_OPEN = {value: key for key, value in OPEN_TO_CLOSE.items()}

NUMERIC_COMPARISON = re.compile(
    r"""(?x)
    (?:
      (?P<num_left>-?\d+(?:\.\d+)?)
      \s*(?P<op_left><|≤|<=|>|≥|>=)\s*
      (?P<var_right>[A-Za-z_][A-Za-z0-9_'.]*)
    )
    |
    (?:
      (?P<var_left>[A-Za-z_][A-Za-z0-9_'.]*)
      \s*(?P<op_right><|≤|<=|>|≥|>=)\s*
      (?P<num_right>-?\d+(?:\.\d+)?)
    )
    """
)


@dataclass(frozen=True)
class TriageReason:
    reason_id: str
    detail: str


@dataclass(frozen=True)
class V4Binder:
    """Compact V4 binder evidence retained by Tier A.

    The 50 MB V4 binder dump is used as input, but only implicit,
    single-letter Sort/Prop binders can affect this triage.  In particular,
    ``binder_type_raw`` is classified and discarded rather than copied into
    the V6 report.
    """

    binder_index: int
    binder_name: str
    binder_info: str
    type_class: str


@dataclass
class SourceDeclaration:
    path: str
    module: str
    kind: str
    name: str
    start_line: int
    end_line: int
    parsed: bool
    statement: str
    conclusion: str
    triage_reasons: list[TriageReason] = field(default_factory=list)
    parse_diagnostic: str = ""
    source_namespace: str = ""
    source_theorem_binders: list[str] = field(default_factory=list)
    source_variable_binders: list[str] = field(default_factory=list)
    v4_match_count: int = 0
    v4_name: str = ""
    v4_type_present: bool = False
    v4_expected_binder_count: int = -1
    v4_binder_match_count: int = 0
    v4_binder_row_count: int = 0
    v4_implicit_single_letter_sort_or_prop: list[V4Binder] = field(
        default_factory=list
    )
    auto_bound_candidates: list[str] = field(default_factory=list)


def module_for_path(relative_path: str) -> str:
    if relative_path.startswith("MatrixConcentration/"):
        suffix = relative_path[len("MatrixConcentration/") : -len(".lean")]
        return "MatrixConcentration." + suffix.replace("/", ".")
    if relative_path.startswith("HighDimensionalProbability/"):
        return relative_path[: -len(".lean")].replace("/", ".")
    return ""


def _line_number(text: str, offset: int) -> int:
    return text.count("\n", 0, offset) + 1


def _normalized(text: str) -> str:
    return re.sub(r"\s+", " ", text).strip()


def _strip_outer_parentheses(text: str) -> str:
    result = text.strip()
    changed = True
    while changed and len(result) >= 2 and result[0] == "(" and result[-1] == ")":
        changed = False
        stack: list[str] = []
        for index, character in enumerate(result):
            if character in OPEN_TO_CLOSE:
                stack.append(character)
            elif character in CLOSE_TO_OPEN:
                if not stack or stack[-1] != CLOSE_TO_OPEN[character]:
                    return result
                stack.pop()
                if not stack and index != len(result) - 1:
                    return result
        if not stack:
            result = result[1:-1].strip()
            changed = True
    return result


def _find_statement_boundary(
    code: str, start: int, limit: int
) -> tuple[int | None, int | None, str]:
    """Find the top-level type colon and proof boundary for one declaration.

    Besides the usual ``:=`` assignment, Lean's equation-compiler syntax
    begins with a top-level ``|`` after the declaration's type colon.
    """

    def starts_equation_clause(pipe: int) -> bool:
        # Equation-compiler clauses in the audited tree start a line and have
        # a top-level `=>` after their pattern.  A bare top-level pipe is not
        # sufficient: it can be either side of real absolute-value notation,
        # including inside an integral in the theorem statement.
        line_start = code.rfind("\n", start, pipe) + 1
        if code[line_start:pipe].strip():
            return False
        clause_stack: list[str] = []
        cursor = pipe + 1
        while cursor < limit:
            clause_character = code[cursor]
            if clause_character in OPEN_TO_CLOSE:
                clause_stack.append(clause_character)
            elif clause_character in CLOSE_TO_OPEN:
                if (
                    not clause_stack
                    or clause_stack[-1]
                    != CLOSE_TO_OPEN[clause_character]
                ):
                    return False
                clause_stack.pop()
            elif not clause_stack:
                if code.startswith("=>", cursor):
                    return True
                if code.startswith(":=", cursor):
                    return False
                if clause_character == "|":
                    return False
            cursor += 1
        return False

    stack: list[str] = []
    type_colon: int | None = None
    index = start
    while index < limit:
        character = code[index]
        if character in OPEN_TO_CLOSE:
            stack.append(character)
        elif character in CLOSE_TO_OPEN:
            if not stack or stack[-1] != CLOSE_TO_OPEN[character]:
                return (
                    type_colon,
                    None,
                    f"unbalanced closing delimiter {character!r}",
                )
            stack.pop()
        elif character == ":" and not stack:
            if index + 1 < limit and code[index + 1] == "=":
                if type_colon is not None:
                    return type_colon, index, ""
            elif type_colon is None:
                type_colon = index
        elif (
            character == "|"
            and not stack
            and type_colon is not None
            and starts_equation_clause(index)
        ):
            return type_colon, index, ""
        index += 1
    if stack:
        return type_colon, None, "unclosed delimiter before next declaration"
    if type_colon is None:
        return None, None, "no top-level theorem type colon found"
    return (
        type_colon,
        None,
        "no top-level proof assignment ':=' or equation clause '|' found",
    )


def _declaration_starts(code: str) -> list[re.Match[str]]:
    return list(DECLARATION_START.finditer(code))


def _unique(items: Iterable[str]) -> list[str]:
    result: list[str] = []
    seen: set[str] = set()
    for item in items:
        if item not in seen:
            seen.add(item)
            result.append(item)
    return result


def _top_level_colon(text: str) -> int | None:
    stack: list[str] = []
    for index, character in enumerate(text):
        if character in OPEN_TO_CLOSE:
            stack.append(character)
        elif character in CLOSE_TO_OPEN:
            if stack and stack[-1] == CLOSE_TO_OPEN[character]:
                stack.pop()
        elif character == ":" and not stack:
            return index
    return None


def _binder_names(text: str) -> list[str]:
    """Extract declared names from Lean binder groups in source syntax."""

    names: list[str] = []
    index = 0
    while index < len(text):
        opener = text[index]
        if opener not in {"(", "[", "{", "⦃"}:
            index += 1
            continue
        stack = [opener]
        end = index + 1
        while end < len(text) and stack:
            character = text[end]
            if character in OPEN_TO_CLOSE:
                stack.append(character)
            elif character in CLOSE_TO_OPEN:
                if stack[-1] == CLOSE_TO_OPEN[character]:
                    stack.pop()
                else:
                    break
            end += 1
        if stack:
            break
        content = text[index + 1 : end - 1]
        colon = _top_level_colon(content)
        if colon is not None:
            declared = content[:colon]
            names.extend(LEAN_IDENTIFIER.findall(declared))
        elif opener != "[":
            # ``{α}`` and ``(x)`` still explicitly declare binders.  A
            # colon-free ``[Foo α]`` is instead an anonymous instance binder.
            names.extend(LEAN_IDENTIFIER.findall(content))
        index = end
    return _unique(names)


def _variable_command_end(code: str, start: int) -> int:
    """Return the end of a possibly multiline ``variable`` command."""

    stack: list[str] = []
    index = start
    while index < len(code):
        character = code[index]
        if character in OPEN_TO_CLOSE:
            stack.append(character)
        elif character in CLOSE_TO_OPEN:
            if stack and stack[-1] == CLOSE_TO_OPEN[character]:
                stack.pop()
        elif character == "\n" and not stack:
            next_line_start = index + 1
            next_line_end = code.find("\n", next_line_start)
            if next_line_end < 0:
                next_line_end = len(code)
            next_line = code[next_line_start:next_line_end].lstrip()
            if not next_line or next_line[0] in {"(", "[", "{", "⦃"}:
                index += 1
                continue
            return index
        index += 1
    return len(code)


def _active_source_variables(
    code: str, starts: Sequence[re.Match[str]]
) -> dict[int, list[str]]:
    """Compute active preceding ``variable`` binders at each declaration."""

    events: list[tuple[int, int, str, object]] = []
    events.extend(
        (match.start(), 0, match.group("kind"), match)
        for match in SCOPE_COMMAND_START.finditer(code)
    )
    events.extend(
        (match.start(), 1, "declaration", match)
        for match in starts
    )
    frames: list[set[str]] = [set()]
    active: dict[int, list[str]] = {}
    for _, _, kind, payload in sorted(events, key=lambda event: event[:2]):
        match = payload
        assert isinstance(match, re.Match)
        if kind in {"namespace", "section"}:
            frames.append(set())
        elif kind == "end":
            if len(frames) > 1:
                frames.pop()
        elif kind == "variable":
            command_end = _variable_command_end(code, match.end())
            frames[-1].update(_binder_names(code[match.end() : command_end]))
        else:
            active[match.start()] = sorted(set().union(*frames))
    return active


def _active_source_namespaces(
    code: str, starts: Sequence[re.Match[str]]
) -> dict[int, str]:
    """Compute the namespace prefix at every source declaration."""

    events: list[tuple[int, int, str, re.Match[str]]] = []
    events.extend(
        (match.start(), 0, match.group("kind"), match)
        for match in SCOPE_COMMAND_START.finditer(code)
    )
    events.extend(
        (match.start(), 1, "declaration", match)
        for match in starts
    )
    frames: list[tuple[str, str]] = []
    active: dict[int, str] = {}
    for _, _, kind, match in sorted(events, key=lambda event: event[:2]):
        if kind in {"namespace", "section"}:
            line_end = code.find("\n", match.end())
            if line_end < 0:
                line_end = len(code)
            command_tail = code[match.end() : line_end].strip()
            scope_name = command_tail.split(maxsplit=1)[0] if command_tail else ""
            frames.append((kind, _unquote_identifier(scope_name)))
        elif kind == "end":
            if frames:
                frames.pop()
        elif kind == "declaration":
            active[match.start()] = ".".join(
                name for frame_kind, name in frames
                if frame_kind == "namespace" and name
            )
    return active


def extract_declarations(path: Path) -> list[SourceDeclaration]:
    if path.is_symlink() or path.resolve() != path.absolute() or not path.is_file():
        raise ValueError(f"V6 input is not a physical regular file: {path}")
    text = path.read_text(encoding="utf-8")
    code, lexical_diagnostics = mask_lean_noncode(text)
    relative = path.relative_to(ROOT).as_posix()
    starts = _declaration_starts(code)
    active_variables = _active_source_variables(code, starts)
    active_namespaces = _active_source_namespaces(code, starts)
    declarations: list[SourceDeclaration] = []

    for position, match in enumerate(starts):
        limit = starts[position + 1].start() if position + 1 < len(starts) else len(code)
        type_colon, proof_start, diagnostic = _find_statement_boundary(
            code, match.end(), limit
        )
        if lexical_diagnostics:
            lexical_text = ", ".join(kind for kind, _ in lexical_diagnostics)
            diagnostic = "; ".join(
                part for part in (diagnostic, lexical_text) if part
            )
        if type_colon is None or proof_start is None:
            statement_end = min(limit, match.end() + 500)
            statement = _normalized(code[match.start() : statement_end])
            conclusion = ""
            parsed = False
            end_line = _line_number(text, statement_end)
        else:
            statement = _normalized(code[match.start() : proof_start])
            conclusion = _normalized(code[type_colon + 1 : proof_start])
            parsed = True
            end_line = _line_number(text, proof_start)
        declarations.append(
            SourceDeclaration(
                path=relative,
                module=module_for_path(relative),
                kind=match.group("kind"),
                name=match.group("name"),
                start_line=_line_number(text, match.start()),
                end_line=end_line,
                parsed=parsed,
                statement=statement,
                conclusion=conclusion,
                parse_diagnostic=diagnostic,
                source_namespace=active_namespaces.get(match.start(), ""),
                source_theorem_binders=(
                    _binder_names(code[match.end() : type_colon])
                    if type_colon is not None
                    else []
                ),
                source_variable_binders=active_variables.get(match.start(), []),
            )
        )
    return declarations


def _canonical_bound(
    match: re.Match[str],
) -> tuple[str, str, Decimal, bool] | None:
    """Return ``(variable, lower/upper, value, strict)``."""

    try:
        if match.group("num_left") is not None:
            value = Decimal(match.group("num_left"))
            variable = match.group("var_right")
            operator = match.group("op_left")
            if operator in ("<",):
                return variable, "lower", value, True
            if operator in ("≤", "<="):
                return variable, "lower", value, False
            if operator in (">",):
                return variable, "upper", value, True
            return variable, "upper", value, False
        value = Decimal(match.group("num_right"))
        variable = match.group("var_left")
        operator = match.group("op_right")
        if operator in ("<",):
            return variable, "upper", value, True
        if operator in ("≤", "<="):
            return variable, "upper", value, False
        if operator in (">",):
            return variable, "lower", value, True
        return variable, "lower", value, False
    except (InvalidOperation, TypeError):
        return None


def _numeric_bound_reasons(statement: str) -> list[TriageReason]:
    bounds: dict[str, dict[str, list[tuple[Decimal, bool, str]]]] = {}
    for match in NUMERIC_COMPARISON.finditer(statement):
        canonical = _canonical_bound(match)
        if canonical is None:
            continue
        variable, direction, value, strict = canonical
        bounds.setdefault(variable, {"lower": [], "upper": []})[direction].append(
            (value, strict, match.group(0))
        )

    reasons: list[TriageReason] = []
    for variable, directions in bounds.items():
        for lower, lower_strict, lower_text in directions["lower"]:
            for upper, upper_strict, upper_text in directions["upper"]:
                if lower > upper or (
                    lower == upper and (lower_strict or upper_strict)
                ):
                    reasons.append(
                        TriageReason(
                            "contradictory_numeric_bounds",
                            f"{variable}: {lower_text.strip()} conflicts with "
                            f"{upper_text.strip()}",
                        )
                    )
                elif lower == upper:
                    reasons.append(
                        TriageReason(
                            "near_degenerate_numeric_bounds",
                            f"{variable}: inclusive bounds force the singleton "
                            f"value {lower}",
                        )
                    )
    return reasons


def _split_top_level(text: str, operator: str) -> tuple[str, str] | None:
    stack: list[str] = []
    index = 0
    while index <= len(text) - len(operator):
        character = text[index]
        if character in OPEN_TO_CLOSE:
            stack.append(character)
            index += 1
            continue
        if character in CLOSE_TO_OPEN:
            if stack and stack[-1] == CLOSE_TO_OPEN[character]:
                stack.pop()
            index += 1
            continue
        if not stack and text.startswith(operator, index):
            return text[:index], text[index + len(operator) :]
        index += 1
    return None


def _looks_syntactically_nonnegative(text: str) -> bool:
    value = _strip_outer_parentheses(text)
    return bool(
        value in {"0", "0.0"}
        or (value.startswith("|") and value.endswith("|"))
        or (value.startswith("‖") and value.endswith("‖"))
        or re.search(r"\^\s*(?:2|[2468])$", value)
        or re.match(r"(?:Real\.)?sqrt\b", value)
        or re.match(r"(?:Real\.)?abs\b", value)
        or re.match(r"(?:norm|nndist|edist)\b", value)
        or re.match(r"max\b.*\b0$", value)
    )


def triage_declaration(declaration: SourceDeclaration) -> list[TriageReason]:
    if not declaration.parsed:
        return [
            TriageReason(
                "unparsed_statement",
                declaration.parse_diagnostic or "statement extraction failed",
            )
        ]

    statement = declaration.statement
    conclusion = _strip_outer_parentheses(declaration.conclusion)
    reasons = _numeric_bound_reasons(statement)

    structural_patterns = (
        (
            "is_empty_domain",
            re.compile(r"\bIsEmpty\b"),
            "statement contains an IsEmpty hypothesis or binder",
        ),
        (
            "fin_zero_domain",
            re.compile(r"\bFin\s*(?:\(\s*)?0\b"),
            "statement mentions the empty type Fin 0",
        ),
        (
            "zero_fintype_card",
            re.compile(r"\bFintype\.card\b[^,;→]*=\s*0\b"),
            "statement forces a finite type to have cardinality zero",
        ),
        (
            "collapsed_domain_typeclass",
            re.compile(r"\b(?:Subsingleton|Unique)\b"),
            "statement contains a Subsingleton or Unique domain constraint",
        ),
        (
            "empty_set_quantifier",
            re.compile(
                r"∀[^,→]*?(?:∈\s*(?:∅|Set\.empty)|:\s*Fin\s+0)"
            ),
            "universal quantifier is syntactically over an empty set/type",
        ),
        (
            "false_antecedent",
            re.compile(r"\bFalse\s*→"),
            "statement has a syntactically false antecedent",
        ),
    )
    for reason_id, pattern, detail in structural_patterns:
        if pattern.search(statement):
            reasons.append(TriageReason(reason_id, detail))

    if conclusion == "True":
        reasons.append(
            TriageReason("trivial_true_conclusion", "conclusion is syntactically True")
        )

    for operator, reason_id in (
        ("↔", "reflexive_iff_conclusion"),
        ("=", "reflexive_equality_conclusion"),
        ("≤", "reflexive_order_conclusion"),
        ("<=", "reflexive_order_conclusion"),
        ("→", "reflexive_implication_conclusion"),
    ):
        split = _split_top_level(conclusion, operator)
        if split is None:
            continue
        left = _strip_outer_parentheses(split[0])
        right = _strip_outer_parentheses(split[1])
        if left and left == right:
            reasons.append(
                TriageReason(
                    reason_id,
                    f"both sides of top-level {operator!r} normalize to {left!r}",
                )
            )

    if re.search(r"(?:≤|<=)\s*⊤\s*$", conclusion):
        reasons.append(
            TriageReason(
                "top_upper_bound_conclusion",
                "conclusion is syntactically bounded above by top",
            )
        )

    nonnegative = (
        _split_top_level(conclusion, "≤")
        or _split_top_level(conclusion, "<=")
    )
    if nonnegative is not None:
        left = _strip_outer_parentheses(nonnegative[0])
        right = _strip_outer_parentheses(nonnegative[1])
        if left in {"0", "(0)"} and _looks_syntactically_nonnegative(right):
            reasons.append(
                TriageReason(
                    "syntactic_nonnegative_conclusion",
                    f"conclusion has the shape 0 ≤ {right}",
                )
            )

    deduplicated: list[TriageReason] = []
    seen: set[tuple[str, str]] = set()
    for reason in reasons:
        key = (reason.reason_id, reason.detail)
        if key not in seen:
            seen.add(key)
            deduplicated.append(reason)
    return deduplicated


def _iter_v4_rows(path: Path) -> Iterable[dict[str, str]]:
    """Stream a V4 TSV so large raw expression fields are never retained."""

    csv.field_size_limit(sys.maxsize)
    with path.open(newline="", encoding="utf-8") as handle:
        reader = csv.DictReader(handle, delimiter="\t")
        if reader.fieldnames is None:
            raise ValueError(f"V4 TSV has no header: {path}")
        for row in reader:
            yield dict(row)


def _row_value(row: dict[str, str], keys: Sequence[str]) -> str:
    return next((row.get(key, "") for key in keys if row.get(key)), "")


def _unquote_identifier(name: str) -> str:
    stripped = name.strip()
    if stripped.startswith("«") and stripped.endswith("»"):
        return stripped[1:-1]
    return stripped


def _name_matches(source_name: str, environment_name: str) -> bool:
    source = _unquote_identifier(source_name)
    environment = _unquote_identifier(environment_name)
    return environment == source or environment.endswith("." + source)


def _matching_declaration_indices(
    declarations: Sequence[SourceDeclaration],
    *,
    module: str,
    aliases: Sequence[str],
    by_module: dict[str, list[int]],
) -> set[int]:
    pool: Iterable[int]
    if module:
        pool = by_module.get(module, [])
    else:
        pool = range(len(declarations))
    qualified_matches = {
        index
        for index in pool
        if declarations[index].source_namespace
        and any(
            alias
            and _name_matches(
                (
                    declarations[index].source_namespace
                    + "."
                    + declarations[index].name
                ),
                alias,
            )
            for alias in aliases
        )
    }
    if qualified_matches:
        return qualified_matches
    return {
        index
        for index in pool
        if any(
            alias and _name_matches(declarations[index].name, alias)
            for alias in aliases
        )
    }


def attach_v4_types(
    declarations: Sequence[SourceDeclaration],
    rows: Iterable[dict[str, str]],
) -> None:
    """Attach compact name/presence metadata from the V4 type dump.

    ``type_raw`` is intentionally reduced to a boolean at the streaming
    boundary.  Copying it would inflate V6 output by hundreds of megabytes.
    """

    name_keys = ("name", "declaration", "declaration_name", "decl_name")
    module_keys = ("module", "module_name")
    type_keys = ("type_raw", "type", "declaration_type", "type_repr")
    private_name_keys = ("private_user_name", "user_name")
    by_module: dict[str, list[int]] = {}
    for index, declaration in enumerate(declarations):
        by_module.setdefault(declaration.module, []).append(index)
        declaration.v4_match_count = 0
        declaration.v4_name = ""
        declaration.v4_type_present = False
        declaration.v4_expected_binder_count = -1
    candidates: list[dict[str, tuple[bool, int]]] = [
        {} for _ in declarations
    ]

    for row in rows:
        name = _row_value(row, name_keys)
        module = _row_value(row, module_keys)
        private_name = _row_value(row, private_name_keys)
        type_present = bool(_row_value(row, type_keys))
        raw_binder_count = row.get("binder_count", "")
        try:
            binder_count = (
                int(raw_binder_count) if raw_binder_count != "" else -1
            )
        except ValueError as error:
            raise ValueError(
                f"invalid V4 binder_count {raw_binder_count!r} for {name!r}"
            ) from error
        if not name:
            continue
        for index in _matching_declaration_indices(
            declarations,
            module=module,
            aliases=(name, private_name),
            by_module=by_module,
        ):
            candidates[index][name] = (type_present, binder_count)

    for declaration, matches in zip(declarations, candidates):
        declaration.v4_match_count = len(matches)
        if len(matches) == 1:
            name, (type_present, binder_count) = next(iter(matches.items()))
            declaration.v4_name = name
            declaration.v4_type_present = type_present
            declaration.v4_expected_binder_count = binder_count


@dataclass
class _V4BinderGroup:
    row_count: int = 0
    relevant_binders: list[V4Binder] = field(default_factory=list)


def _classify_sort_or_prop(raw_type: str) -> str:
    normalized = _normalized(raw_type.replace("\\n", " "))
    if normalized == "Lean.Expr.sort (Lean.Level.zero)":
        return "Prop"
    if normalized.startswith("Lean.Expr.sort"):
        return "Sort"
    return ""


def _relevant_v4_binder(row: dict[str, str]) -> V4Binder | None:
    binder_name = _row_value(row, ("binder_name", "name"))
    binder_info = _row_value(row, ("binder_info", "info"))
    # Reject the overwhelmingly common irrelevant rows before touching the
    # potentially very large serialized binder-type expression.
    if (
        binder_info != "implicit"
        or len(binder_name) != 1
        or not binder_name.isalpha()
    ):
        return None
    raw_type = _row_value(
        row, ("binder_type_raw", "binder_type", "type_raw", "type")
    )
    type_class = _classify_sort_or_prop(raw_type)
    if not type_class:
        return None
    raw_index = _row_value(row, ("binder_index", "index"))
    try:
        binder_index = int(raw_index)
    except ValueError as error:
        raise ValueError(
            f"invalid V4 binder index {raw_index!r} for {binder_name!r}"
        ) from error
    return V4Binder(
        binder_index=binder_index,
        binder_name=binder_name,
        binder_info=binder_info,
        type_class=type_class,
    )


def attach_v4_binders(
    declarations: Sequence[SourceDeclaration],
    rows: Iterable[dict[str, str]],
) -> None:
    """Attach only compact binder evidence relevant to auto-bound triage."""

    name_keys = ("name", "declaration", "declaration_name", "decl_name")
    module_keys = ("module", "module_name")
    private_name_keys = ("private_user_name", "user_name")
    by_module: dict[str, list[int]] = {}
    by_exact_v4_name: dict[tuple[str, str], list[int]] = {}
    groups: list[dict[str, _V4BinderGroup]] = [
        {} for _ in declarations
    ]
    match_cache: dict[tuple[str, str, str], set[int]] = {}
    for index, declaration in enumerate(declarations):
        by_module.setdefault(declaration.module, []).append(index)
        if declaration.v4_name:
            by_exact_v4_name.setdefault(
                (declaration.module, declaration.v4_name), []
            ).append(index)
        declaration.v4_binder_match_count = 0
        declaration.v4_binder_row_count = 0
        declaration.v4_implicit_single_letter_sort_or_prop = []

    for row in rows:
        name = _row_value(row, name_keys)
        module = _row_value(row, module_keys)
        private_name = _row_value(row, private_name_keys)
        if not name:
            continue
        cache_key = (module, name, private_name)
        matched = match_cache.get(cache_key)
        if matched is None:
            matched = set(by_exact_v4_name.get((module, name), []))
            matched.update(
                _matching_declaration_indices(
                    declarations,
                    module=module,
                    aliases=(name, private_name),
                    by_module=by_module,
                )
            )
            match_cache[cache_key] = matched
        relevant = _relevant_v4_binder(row)
        for index in matched:
            group = groups[index].setdefault(name, _V4BinderGroup())
            group.row_count += 1
            if relevant is not None:
                group.relevant_binders.append(relevant)

    for declaration, matches in zip(declarations, groups):
        declaration.v4_binder_match_count = len(matches)
        selected: _V4BinderGroup | None = None
        if declaration.v4_name and declaration.v4_name in matches:
            selected = matches[declaration.v4_name]
        elif len(matches) == 1:
            selected = next(iter(matches.values()))
        if selected is None:
            continue
        declaration.v4_binder_row_count = selected.row_count
        declaration.v4_implicit_single_letter_sort_or_prop = sorted(
            set(selected.relevant_binders),
            key=lambda binder: (
                binder.binder_index,
                binder.binder_name,
                binder.type_class,
            ),
        )


AUTO_BOUND_REASON_ID = "auto_bound_single_letter_sort_or_prop"


def apply_v4_auto_bound_triage(
    declarations: Sequence[SourceDeclaration],
) -> None:
    """Flag V4 implicit Sort/Prop binders absent from source declarations."""

    for declaration in declarations:
        declaration.triage_reasons = [
            reason
            for reason in declaration.triage_reasons
            if reason.reason_id != AUTO_BOUND_REASON_ID
        ]
        declared_in_source = {
            _unquote_identifier(name)
            for name in (
                declaration.source_theorem_binders
                + declaration.source_variable_binders
            )
        }
        candidates = [
            binder
            for binder in declaration.v4_implicit_single_letter_sort_or_prop
            if _unquote_identifier(binder.binder_name) not in declared_in_source
        ]
        declaration.auto_bound_candidates = _unique(
            binder.binder_name for binder in candidates
        )
        declaration.triage_reasons.extend(
            TriageReason(
                AUTO_BOUND_REASON_ID,
                f"V4 implicit binder {binder.binder_name!r} is "
                f"{binder.type_class}; absent from theorem binders and active "
                "source variable commands",
            )
            for binder in candidates
        )


def scan_paths(
    paths: Iterable[Path],
    *,
    v4_types_tsv: Path | None = None,
    v4_binders_tsv: Path | None = None,
) -> list[SourceDeclaration]:
    declarations: list[SourceDeclaration] = []
    for path in sorted({item.absolute() for item in paths}):
        declarations.extend(extract_declarations(path))
    for declaration in declarations:
        declaration.triage_reasons = triage_declaration(declaration)
    if v4_types_tsv is not None:
        attach_v4_types(declarations, _iter_v4_rows(v4_types_tsv))
    if v4_binders_tsv is not None:
        attach_v4_binders(declarations, _iter_v4_rows(v4_binders_tsv))
        apply_v4_auto_bound_triage(declarations)
    declarations.sort(
        key=lambda declaration: (
            declaration.path,
            declaration.start_line,
            declaration.name,
        )
    )
    return declarations


def summary(
    declarations: Sequence[SourceDeclaration],
    *,
    scope: str,
    scanned_file_count: int,
    v4_types_tsv: Path | None = None,
    v4_binders_tsv: Path | None = None,
) -> dict[str, object]:
    by_reason: dict[str, int] = {}
    for declaration in declarations:
        for reason in declaration.triage_reasons:
            by_reason[reason.reason_id] = by_reason.get(reason.reason_id, 0) + 1

    def report_path(path: Path | None) -> str:
        if path is None:
            return ""
        absolute = path.absolute()
        try:
            return absolute.relative_to(ROOT).as_posix()
        except ValueError:
            return absolute.as_posix()

    return {
        "profile": "V6-Tier-A",
        "scope": scope,
        "scanned_file_count": scanned_file_count,
        "declaration_count": len(declarations),
        "parsed_declaration_count": sum(
            declaration.parsed for declaration in declarations
        ),
        "unparsed_declaration_count": sum(
            not declaration.parsed for declaration in declarations
        ),
        "flagged_declaration_count": sum(
            bool(declaration.triage_reasons) for declaration in declarations
        ),
        "unflagged_declaration_count": sum(
            not declaration.triage_reasons for declaration in declarations
        ),
        "reason_counts": dict(sorted(by_reason.items())),
        "v4_metadata": {
            "types_tsv": report_path(v4_types_tsv),
            "binders_tsv": report_path(v4_binders_tsv),
            "raw_type_fields_embedded": False,
            "unique_type_match_count": sum(
                declaration.v4_match_count == 1
                for declaration in declarations
            ),
            "ambiguous_type_match_count": sum(
                declaration.v4_match_count > 1
                for declaration in declarations
            ),
            "unmatched_type_count": sum(
                declaration.v4_match_count == 0
                for declaration in declarations
            ),
            "joined_type_telescope_count": sum(
                declaration.v4_match_count == 1
                and declaration.v4_expected_binder_count >= 0
                for declaration in declarations
            ),
            "complete_binder_telescope_count": sum(
                declaration.v4_match_count == 1
                and declaration.v4_expected_binder_count >= 0
                and declaration.v4_expected_binder_count
                == declaration.v4_binder_row_count
                for declaration in declarations
            ),
            "incomplete_binder_telescope_count": sum(
                declaration.v4_match_count == 1
                and declaration.v4_expected_binder_count >= 0
                and declaration.v4_expected_binder_count
                != declaration.v4_binder_row_count
                for declaration in declarations
            ),
            "matched_binder_telescope_count": sum(
                declaration.v4_binder_row_count > 0
                for declaration in declarations
            ),
            "auto_bound_candidate_count": sum(
                len(declaration.auto_bound_candidates)
                for declaration in declarations
            ),
        },
        "interpretation": (
            "Every reason is Tier-A triage only. A hit does not establish "
            "semantic vacuity; Tier-B review is required."
        ),
    }


def _declaration_dict(declaration: SourceDeclaration) -> dict[str, object]:
    data = asdict(declaration)
    data["triage_reasons"] = [
        asdict(reason) for reason in declaration.triage_reasons
    ]
    return data


def render_json(
    report_summary: dict[str, object],
    declarations: Sequence[SourceDeclaration],
) -> str:
    return (
        json.dumps(
            {
                "summary": report_summary,
                "declarations": [
                    _declaration_dict(declaration)
                    for declaration in declarations
                ],
            },
            indent=2,
            sort_keys=True,
        )
        + "\n"
    )


def _tsv(value: object) -> str:
    return str(value).replace("\\", "\\\\").replace("\t", "\\t").replace(
        "\n", "\\n"
    )


def render_tsv(declarations: Sequence[SourceDeclaration]) -> str:
    lines = [
        "path\tmodule\tline\tend_line\tkind\tname\tsource_namespace\tparsed"
        "\treasons\tstatement\tconclusion"
        "\tsource_theorem_binders\tsource_variable_binders\tv4_match_count\tv4_name"
        "\tv4_type_present\tv4_expected_binder_count\tv4_binder_match_count"
        "\tv4_binder_row_count"
        "\tv4_implicit_single_letter_sort_or_prop\tauto_bound_candidates"
    ]
    for declaration in declarations:
        reasons = "; ".join(
            f"{reason.reason_id}: {reason.detail}"
            for reason in declaration.triage_reasons
        )
        values = (
            declaration.path,
            declaration.module,
            declaration.start_line,
            declaration.end_line,
            declaration.kind,
            declaration.name,
            declaration.source_namespace,
            str(declaration.parsed).lower(),
            reasons,
            declaration.statement,
            declaration.conclusion,
            ",".join(declaration.source_theorem_binders),
            ",".join(declaration.source_variable_binders),
            declaration.v4_match_count,
            declaration.v4_name,
            str(declaration.v4_type_present).lower(),
            declaration.v4_expected_binder_count,
            declaration.v4_binder_match_count,
            declaration.v4_binder_row_count,
            ",".join(
                f"{binder.binder_index}:{binder.binder_name}:{binder.type_class}"
                for binder
                in declaration.v4_implicit_single_letter_sort_or_prop
            ),
            ",".join(declaration.auto_bound_candidates),
        )
        lines.append("\t".join(_tsv(value) for value in values))
    return "\n".join(lines) + "\n"


def render_text(
    report_summary: dict[str, object],
    declarations: Sequence[SourceDeclaration],
) -> str:
    lines = [
        f"{key}: {value}"
        for key, value in report_summary.items()
        if key != "reason_counts"
    ]
    lines.append(f"reason_counts: {report_summary['reason_counts']}")
    lines.append("")
    for declaration in declarations:
        reasons = ", ".join(
            reason.reason_id for reason in declaration.triage_reasons
        )
        lines.append(
            f"{declaration.path}:{declaration.start_line}: "
            f"{declaration.kind} {declaration.name} "
            f"parsed={str(declaration.parsed).lower()} "
            f"reasons={reasons or '-'}"
        )
    return "\n".join(lines) + "\n"


def validate_v4_join_contract(
    report: dict[str, object],
    *,
    expected_types_tsv: str,
    expected_binders_tsv: str,
    expected_declaration_count: int | None = None,
) -> dict[str, object]:
    """Validate and compact the V4 metadata evidence in a V6 JSON report."""

    report_summary = report.get("summary")
    declarations = report.get("declarations")
    if not isinstance(report_summary, dict) or not isinstance(declarations, list):
        raise ValueError("V6 report lacks summary/declarations")
    metadata = report_summary.get("v4_metadata")
    reason_counts = report_summary.get("reason_counts")
    if not isinstance(metadata, dict) or not isinstance(reason_counts, dict):
        raise ValueError("V6 report lacks V4 metadata/reason counts")
    if metadata.get("types_tsv") != expected_types_tsv:
        raise ValueError(
            "V6 report used unexpected V4 type TSV: "
            f"{metadata.get('types_tsv')!r}"
        )
    if metadata.get("binders_tsv") != expected_binders_tsv:
        raise ValueError(
            "V6 report used unexpected V4 binder TSV: "
            f"{metadata.get('binders_tsv')!r}"
        )
    if metadata.get("raw_type_fields_embedded") is not False:
        raise ValueError("V6 report does not certify compact V4 metadata")

    declaration_count = report_summary.get("declaration_count")
    parsed_count = report_summary.get("parsed_declaration_count")
    unparsed_count = report_summary.get("unparsed_declaration_count")
    if (
        not isinstance(declaration_count, int)
        or parsed_count != declaration_count
        or unparsed_count != 0
        or len(declarations) != declaration_count
    ):
        raise ValueError(
            "V6 source parse coverage is not complete: "
            f"declarations={declaration_count!r}, parsed={parsed_count!r}, "
            f"unparsed={unparsed_count!r}, rows={len(declarations)}"
        )
    if (
        expected_declaration_count is not None
        and declaration_count != expected_declaration_count
    ):
        raise ValueError(
            "V6 source declaration census changed: "
            f"{declaration_count} != {expected_declaration_count}"
        )

    integer_keys = (
        "unique_type_match_count",
        "ambiguous_type_match_count",
        "unmatched_type_count",
        "joined_type_telescope_count",
        "complete_binder_telescope_count",
        "incomplete_binder_telescope_count",
        "matched_binder_telescope_count",
        "auto_bound_candidate_count",
    )
    if any(not isinstance(metadata.get(key), int) for key in integer_keys):
        raise ValueError("V6 V4 metadata has missing/non-integer coverage counts")
    if (
        metadata["unique_type_match_count"]
        + metadata["ambiguous_type_match_count"]
        + metadata["unmatched_type_count"]
        != declaration_count
    ):
        raise ValueError("V6 V4 type-join partition does not cover source rows")
    if (
        metadata["unique_type_match_count"] != declaration_count
        or metadata["ambiguous_type_match_count"] != 0
        or metadata["unmatched_type_count"] != 0
    ):
        raise ValueError(
            "V6 V4 type join is not declaration-complete: "
            f"unique={metadata['unique_type_match_count']}, "
            f"ambiguous={metadata['ambiguous_type_match_count']}, "
            f"unmatched={metadata['unmatched_type_count']}, "
            f"source={declaration_count}"
        )
    if metadata["joined_type_telescope_count"] <= 0:
        raise ValueError("V6 V4 type rows expose no binder-count coverage")
    if (
        metadata["incomplete_binder_telescope_count"] != 0
        or metadata["complete_binder_telescope_count"]
        != metadata["joined_type_telescope_count"]
        or metadata["matched_binder_telescope_count"] <= 0
    ):
        raise ValueError(
            "V6 V4 binder telescope join is incomplete: "
            f"joined={metadata['joined_type_telescope_count']}, "
            f"complete={metadata['complete_binder_telescope_count']}, "
            f"incomplete={metadata['incomplete_binder_telescope_count']}, "
            f"nonempty={metadata['matched_binder_telescope_count']}"
        )

    candidate_count = 0
    auto_reason_count = 0
    auto_flagged_declarations = 0
    forbidden_keys = {"v4_type", "type_raw", "binder_type_raw"}
    for raw in declarations:
        if not isinstance(raw, dict):
            raise ValueError("V6 declaration row is not an object")
        present_forbidden = forbidden_keys.intersection(raw)
        if present_forbidden:
            raise ValueError(
                "V6 declaration embeds forbidden raw V4 fields: "
                f"{sorted(present_forbidden)!r}"
            )
        candidates = raw.get("auto_bound_candidates")
        reasons = raw.get("triage_reasons")
        if not isinstance(candidates, list) or not isinstance(reasons, list):
            raise ValueError("V6 declaration lacks compact binder diagnostics")
        row_auto_reasons = sum(
            isinstance(reason, dict)
            and reason.get("reason_id") == AUTO_BOUND_REASON_ID
            for reason in reasons
        )
        if bool(candidates) != bool(row_auto_reasons):
            raise ValueError(
                "V6 auto-bound candidate/reason mismatch for "
                f"{raw.get('path')}:{raw.get('name')}"
            )
        candidate_count += len(candidates)
        auto_reason_count += row_auto_reasons
        auto_flagged_declarations += bool(row_auto_reasons)

    if candidate_count != auto_reason_count:
        raise ValueError(
            "V6 auto-bound candidate/reason totals differ: "
            f"{candidate_count} != {auto_reason_count}"
        )
    if metadata["auto_bound_candidate_count"] != candidate_count:
        raise ValueError("V6 summary auto-bound candidate count is stale")
    reported_auto_reason_count = reason_counts.get(
        AUTO_BOUND_REASON_ID, 0
    )
    if (
        not isinstance(reported_auto_reason_count, int)
        or reported_auto_reason_count < 0
    ):
        raise ValueError("V6 summary auto-bound reason count is invalid")
    if reported_auto_reason_count != auto_reason_count:
        raise ValueError("V6 summary auto-bound reason count is stale")

    return {
        "types_tsv": expected_types_tsv,
        "binders_tsv": expected_binders_tsv,
        "parsed_declarations": declaration_count,
        "unique_type_matches": metadata["unique_type_match_count"],
        "ambiguous_type_matches": metadata["ambiguous_type_match_count"],
        "unmatched_source_declarations": metadata["unmatched_type_count"],
        "complete_binder_telescopes": metadata[
            "complete_binder_telescope_count"
        ],
        "auto_bound_candidate_count": candidate_count,
        "auto_bound_flagged_declaration_count": auto_flagged_declarations,
        "raw_type_fields_embedded": False,
    }


def main(argv: Sequence[str] | None = None) -> int:
    parser = argparse.ArgumentParser(
        description="Enumerate and triage every source theorem/lemma statement"
    )
    parser.add_argument(
        "--scope",
        choices=("library", "scratch", "all"),
        default="library",
    )
    parser.add_argument(
        "--path",
        action="append",
        type=Path,
        help="explicit planted/source path; repeatable and overrides --scope",
    )
    parser.add_argument("--format", choices=("json", "tsv", "text"), default="json")
    parser.add_argument("--output", type=Path)
    parser.add_argument(
        "--v4-types-tsv",
        type=Path,
        help=(
            "optional V4 type TSV used only for compact module/name coverage; "
            "raw types are never copied"
        ),
    )
    parser.add_argument(
        "--v4-binders-tsv",
        type=Path,
        help=(
            "optional V4 binder TSV used for implicit single-letter Sort/Prop "
            "binder triage"
        ),
    )
    parser.add_argument(
        "--fail-on-unparsed",
        action="store_true",
        help="return nonzero unless every detected declaration was parsed",
    )
    parser.add_argument(
        "--require-complete-v4-join",
        action="store_true",
        help=(
            "fail unless every source declaration has one complete V4 "
            "type/binder telescope join"
        ),
    )
    args = parser.parse_args(argv)

    if args.path:
        selected = [
            path if path.is_absolute() else ROOT / path for path in args.path
        ]
        scope = "explicit-paths"
    else:
        selected = paths_for_scope(args.scope)
        scope = args.scope
    v4_path = args.v4_types_tsv
    if v4_path is not None and not v4_path.is_absolute():
        v4_path = ROOT / v4_path
    v4_binders_path = args.v4_binders_tsv
    if v4_binders_path is not None and not v4_binders_path.is_absolute():
        v4_binders_path = ROOT / v4_binders_path

    declarations = scan_paths(
        selected,
        v4_types_tsv=v4_path,
        v4_binders_tsv=v4_binders_path,
    )
    report_summary = summary(
        declarations,
        scope=scope,
        scanned_file_count=len(set(selected)),
        v4_types_tsv=v4_path,
        v4_binders_tsv=v4_binders_path,
    )
    if args.require_complete_v4_join:
        if v4_path is None or v4_binders_path is None:
            parser.error(
                "--require-complete-v4-join needs both V4 TSV arguments"
            )
        validation_report = {
            "summary": report_summary,
            "declarations": [
                _declaration_dict(declaration)
                for declaration in declarations
            ],
        }
        validate_v4_join_contract(
            validation_report,
            expected_types_tsv=str(
                report_summary["v4_metadata"]["types_tsv"]  # type: ignore[index]
            ),
            expected_binders_tsv=str(
                report_summary["v4_metadata"]["binders_tsv"]  # type: ignore[index]
            ),
            expected_declaration_count=len(declarations),
        )
        report_summary["v4_join_contract"] = "PASS"
    if args.format == "json":
        output = render_json(report_summary, declarations)
    elif args.format == "tsv":
        output = render_tsv(declarations)
    else:
        output = render_text(report_summary, declarations)

    if args.output:
        output_path = args.output if args.output.is_absolute() else ROOT / args.output
        output_path.parent.mkdir(parents=True, exist_ok=True)
        output_path.write_text(output, encoding="utf-8")
    else:
        sys.stdout.write(output)
    if args.fail_on_unparsed and report_summary["unparsed_declaration_count"]:
        return 1
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
