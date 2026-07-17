from __future__ import annotations

from pathlib import Path
from typing import Any

from jinja2 import Environment, FileSystemLoader, StrictUndefined


class PromptRenderer:
    def __init__(self, prompt_root: Path) -> None:
        self.prompt_root = prompt_root.resolve()
        self.environment = Environment(
            loader=FileSystemLoader(str(self.prompt_root)),
            undefined=StrictUndefined,
            autoescape=False,
            keep_trailing_newline=True,
        )

    def render(self, template: Path, values: dict[str, Any]) -> str:
        template = template.resolve()
        try:
            relative = template.relative_to(self.prompt_root).as_posix()
        except ValueError as error:
            raise ValueError(f"prompt template must be under {self.prompt_root}: {template}") from error
        output = self.environment.get_template(relative).render(**values)
        if "{{" in output or "{%" in output:
            raise ValueError(f"unresolved template marker in rendered prompt: {template}")
        return output


def verify_prompt_paths(paths: list[Path]) -> None:
    missing = [str(path) for path in paths if not path.exists()]
    if missing:
        raise FileNotFoundError("missing prompt inputs: " + ", ".join(missing))

