from __future__ import annotations

import re
from pathlib import Path

IMPORT_RE = re.compile(r"^\s*import\s+(.+?)\s*$", re.MULTILINE)


def import_graph(project: Path) -> dict[str, list[str]]:
    graph: dict[str, list[str]] = {}
    for path in sorted(project.rglob("*.lean")):
        if ".lake" in path.parts:
            continue
        relative = path.relative_to(project).with_suffix("")
        module = ".".join(relative.parts)
        text = path.read_text(encoding="utf-8", errors="replace")
        imports: list[str] = []
        for match in IMPORT_RE.finditer(text):
            imports.extend(part.strip() for part in match.group(1).split() if part.strip())
        graph[module] = imports
    return graph


def detect_cycles(graph: dict[str, list[str]]) -> list[list[str]]:
    cycles: list[list[str]] = []
    visiting: list[str] = []
    visited: set[str] = set()

    def visit(node: str) -> None:
        if node in visiting:
            cycles.append(visiting[visiting.index(node):] + [node])
            return
        if node in visited:
            return
        visiting.append(node)
        for child in graph.get(node, []):
            if child in graph:
                visit(child)
        visiting.pop()
        visited.add(node)

    for node in graph:
        visit(node)
    return cycles

