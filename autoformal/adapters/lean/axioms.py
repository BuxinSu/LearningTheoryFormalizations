from __future__ import annotations

import re
from pathlib import Path

from .build import run_command
from .placeholders import _mask_comments_and_strings

DECLARATION_RE = re.compile(r"^\s*(?:theorem|lemma|corollary|proposition)\s+([^\s(:\[{]+)", re.MULTILINE)


def public_declarations(root: Path) -> list[str]:
    declarations: list[str] = []
    namespace_re = re.compile(r"^\s*namespace\s+([^\s(:\[{]+)")
    section_re = re.compile(r"^\s*section(?:\s+([^\s(:\[{]+))?\s*$")
    end_re = re.compile(r"^\s*end(?:\s+([^\s(:\[{]+))?\s*$")
    declaration_re = re.compile(
        r"^\s*(?:theorem|lemma|corollary|proposition)\s+([^\s(:\[{]+)"
    )
    for path in root.rglob("*.lean"):
        if ".lake" in path.parts:
            continue
        scopes: list[tuple[str, str | None]] = []
        text = path.read_text(encoding="utf-8", errors="replace")
        for line in _mask_comments_and_strings(text).splitlines():
            if match := namespace_re.match(line):
                for component in match.group(1).split("."):
                    scopes.append(("namespace", component))
                continue
            if match := section_re.match(line):
                scopes.append(("section", match.group(1))); continue
            if end_re.match(line):
                if scopes: scopes.pop()
                continue
            if match := declaration_re.match(line):
                name = match.group(1)
                namespaces = [value for kind, value in scopes if kind == "namespace" and value]
                prefix = ".".join(namespaces)
                declarations.append(
                    name if not prefix or name == prefix or name.startswith(prefix + ".")
                    else f"{prefix}.{name}"
                )
    return sorted(set(declarations))


def print_axioms(project: Path, module: str | list[str], declarations: list[str], diagnostic_dir: Path):
    diagnostic_dir.mkdir(parents=True, exist_ok=True)
    source = diagnostic_dir / "PrintAxioms.lean"
    modules = [module] if isinstance(module, str) else module
    source.write_text(
        "\n".join(f"import {item}" for item in modules) + "\n\n"
        + "\n".join(f"#print axioms {decl}" for decl in declarations) + "\n",
        encoding="utf-8",
    )
    return run_command(["lake", "env", "lean", str(source)], project, 1800)

