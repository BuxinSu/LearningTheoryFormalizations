from __future__ import annotations

from copy import deepcopy
from pathlib import Path
from typing import Any

import yaml

from .models import BookConfig


def repository_root(start: Path | None = None) -> Path:
    current = (start or Path.cwd()).resolve()
    for candidate in (current, *current.parents):
        stable_source = candidate / "src" / "autoformal"
        clean_source = candidate / "code" / "src" / "autoformal"
        has_assets = (candidate / "configs").is_dir() and (candidate / "prompts").is_dir()
        if has_assets and (stable_source.is_dir() or clean_source.is_dir()):
            return candidate
    raise FileNotFoundError("could not locate AutoFormal repository root")


def _read_yaml(path: Path) -> dict[str, Any]:
    data = yaml.safe_load(path.read_text(encoding="utf-8")) or {}
    if not isinstance(data, dict):
        raise ValueError(f"configuration must be a mapping: {path}")
    return data


def _merge(base: dict[str, Any], override: dict[str, Any]) -> dict[str, Any]:
    result = deepcopy(base)
    for key, value in override.items():
        if isinstance(value, dict) and isinstance(result.get(key), dict):
            result[key] = _merge(result[key], value)
        else:
            result[key] = deepcopy(value)
    return result


def load_book_config(path: Path, root: Path | None = None) -> BookConfig:
    root = (root or repository_root()).resolve()
    path = path.resolve()
    defaults = _read_yaml(root / "configs" / "defaults.yaml")
    local = _read_yaml(path)
    extends = local.pop("extends", None)
    profile: dict[str, Any] = {}
    if extends:
        profile_path = (path.parent / str(extends)).resolve()
        profile = _read_yaml(profile_path)
    merged = _merge(_merge(defaults, profile), local)
    config = BookConfig.model_validate(merged)

    path_fields = [
        "input_pdf", "runtime_dir", "output_dir",
        "prompts.formalization_policy", "prompts.source_conventions",
        "prompts.draft_template", "prompts.review_template", "prompts.revision_template",
    ]
    for field in path_fields:
        owner: Any = config
        parts = field.split(".")
        for part in parts[:-1]:
            owner = getattr(owner, part)
        value = getattr(owner, parts[-1])
        if not value.is_absolute():
            setattr(owner, parts[-1], (root / value).resolve())
    for field in ("required_paths", "exercise_paths", "hint_paths", "report_paths"):
        values = getattr(config.policy, field)
        setattr(config.policy, field, [
            value if value.is_absolute() else (root / value).resolve() for value in values
        ])
    return config

