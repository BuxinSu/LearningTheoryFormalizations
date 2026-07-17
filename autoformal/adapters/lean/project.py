from __future__ import annotations

from pathlib import Path

from ...artifacts import atomic_write_text
from ...infrastructure.git_worktree import GitWorkspace
from ...domain import LeanConfig


def ensure_lean_project(path: Path, config: LeanConfig) -> GitWorkspace:
    workspace = GitWorkspace(path)
    workspace.ensure()
    toolchain = path / "lean-toolchain"
    lakefile = path / "lakefile.toml"
    namespace_dir = path / config.namespace
    namespace_dir.mkdir(parents=True, exist_ok=True)
    if not toolchain.exists():
        atomic_write_text(toolchain, config.toolchain + "\n")
    if not lakefile.exists():
        atomic_write_text(lakefile, f'''name = "{config.project_name}"
version = "0.1.0"
defaultTargets = ["{config.namespace}"]

[[require]]
name = "mathlib"
git = "https://github.com/leanprover-community/mathlib4.git"
rev = "{config.mathlib_revision}"

[[lean_lib]]
name = "{config.namespace}"
''')
    root = path / f"{config.namespace}.lean"
    if not root.exists():
        atomic_write_text(root, f"/-! Root aggregator for {config.project_name}. -/\n\nnamespace {config.namespace}\n\nend {config.namespace}\n")
    gitignore = path / ".gitignore"
    if not gitignore.exists():
        atomic_write_text(gitignore, ".lake/\n")
    try:
        workspace.commit_green("Initialize pinned Lean project")
    except Exception:
        # A scaffold remains usable even when Git is not available for an initial commit.
        pass
    return workspace

