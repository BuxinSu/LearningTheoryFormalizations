from __future__ import annotations

import re
from dataclasses import dataclass
from pathlib import Path

from ...domain import ChapterRecord, SectionRecord

COMMAND_RE = re.compile(r"\\(chapter|section)(\*)?(?:\[([^\]]*)\])?\{")


@dataclass(frozen=True)
class StructuralCommand:
    kind: str
    title: str
    start: int
    end: int


def _balanced_argument(text: str, opening_brace: int) -> tuple[str, int]:
    depth = 0
    index = opening_brace
    while index < len(text):
        char = text[index]
        preceding = 0
        cursor = index - 1
        while cursor >= 0 and text[cursor] == "\\":
            preceding += 1
            cursor -= 1
        escaped = preceding % 2 == 1
        if char == "{" and not escaped:
            depth += 1
        elif char == "}" and not escaped:
            depth -= 1
            if depth == 0:
                return text[opening_brace + 1:index], index + 1
        index += 1
    raise ValueError(f"unclosed structural command argument at character {opening_brace}")


def _commands(text: str, kind: str | None = None, offset: int = 0) -> list[StructuralCommand]:
    commands: list[StructuralCommand] = []
    for match in COMMAND_RE.finditer(text):
        if kind and match.group(1) != kind:
            continue
        opening = match.end() - 1
        title, end = _balanced_argument(text, opening)
        commands.append(StructuralCommand(match.group(1), title.strip(), offset + match.start(), offset + end))
    return commands


def discover_structure(
    tex_root: Path, starts_at: int = 1, split_root: Path | None = None
) -> list[ChapterRecord]:
    chapters: list[ChapterRecord] = []
    if split_root is not None:
        split_root.mkdir(parents=True, exist_ok=True)
    next_id = starts_at
    for path in sorted(tex_root.rglob("*.tex")):
        text = path.read_text(encoding="utf-8", errors="replace")
        mainmatter = text.find(r"\mainmatter")
        backmatter = text.find(r"\backmatter")
        scope_start = mainmatter + len(r"\mainmatter") if mainmatter >= 0 else 0
        scope_end = backmatter if backmatter >= 0 and backmatter > scope_start else len(text)
        scope = text[scope_start:scope_end]
        chapter_commands = _commands(scope, "chapter", scope_start)
        if not chapter_commands:
            continue
        for index, command in enumerate(chapter_commands):
            content_end = chapter_commands[index + 1].start if index + 1 < len(chapter_commands) else scope_end
            fragment_start = command.end
            fragment = text[fragment_start:content_end]
            section_commands = _commands(fragment, "section", fragment_start)
            chapter_path = path
            if split_root is not None:
                chapter_path = split_root / f"chapter-{next_id:02d}.tex"
                chapter_path.write_text(text[command.start:content_end].strip() + "\n", encoding="utf-8")
            sections: list[SectionRecord] = []
            for section_index, section in enumerate(section_commands, start=1):
                section_end = (
                    section_commands[section_index].start
                    if section_index < len(section_commands) else content_end
                )
                section_path = path
                if split_root is not None:
                    section_path = split_root / f"chapter-{next_id:02d}-section-{section_index:02d}.tex"
                    section_path.write_text(
                        f"% Parent chapter: {command.title}\n" + text[section.start:section_end].strip() + "\n",
                        encoding="utf-8",
                    )
                sections.append(SectionRecord(
                    id=f"{next_id}.{section_index}", title=section.title,
                    tex_path=str(section_path),
                ))
            chapters.append(ChapterRecord(
                id=str(next_id), title=command.title, tex_path=str(chapter_path), sections=sections
            ))
            next_id += 1
    if chapters:
        return chapters

    tex_files = sorted(tex_root.rglob("*.tex"))
    for path in tex_files:
        text = path.read_text(encoding="utf-8", errors="replace")
        section_commands = _commands(text, "section")
        if section_commands:
            sections = [
                SectionRecord(
                    id=f"{starts_at}.{index}", title=section.title, tex_path=str(path)
                )
                for index, section in enumerate(section_commands, start=1)
            ]
            return [ChapterRecord(id=str(starts_at), title="Document", tex_path=str(path), sections=sections)]
    return []
