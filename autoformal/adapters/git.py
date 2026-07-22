from __future__ import annotations

import subprocess
from pathlib import Path


class GitWorkspace:
    def __init__(self, path: Path) -> None:
        self.path = path

    def ensure(self) -> None:
        self.path.mkdir(parents=True, exist_ok=True)
        if not (self.path / ".git").exists():
            subprocess.run(["git", "init", "--quiet"], cwd=self.path, check=True)
            subprocess.run(["git", "config", "user.name", "AutoFormal"], cwd=self.path, check=True)
            subprocess.run(["git", "config", "user.email", "autoformal@localhost"], cwd=self.path, check=True)

    def diff(self) -> str:
        result = subprocess.run(
            ["git", "diff", "--no-ext-diff", "--", "."], cwd=self.path,
            text=True, capture_output=True, check=False,
        )
        untracked = subprocess.run(
            ["git", "ls-files", "--others", "--exclude-standard"], cwd=self.path,
            text=True, capture_output=True, check=False,
        ).stdout.splitlines()
        additions = []
        for relative in untracked:
            path = self.path / relative
            if path.is_file() and path.stat().st_size <= 2_000_000:
                additions.append(f"\n--- /dev/null\n+++ b/{relative}\n" + path.read_text(errors="replace"))
        return result.stdout + "".join(additions)

    def commit_green(self, message: str) -> str:
        subprocess.run(["git", "add", "-A"], cwd=self.path, check=True)
        staged = subprocess.run(["git", "diff", "--cached", "--quiet"], cwd=self.path, check=False)
        if staged.returncode != 0:
            subprocess.run(["git", "commit", "--quiet", "-m", message], cwd=self.path, check=True)
        return subprocess.run(
            ["git", "rev-parse", "HEAD"], cwd=self.path, text=True, capture_output=True, check=True
        ).stdout.strip()

