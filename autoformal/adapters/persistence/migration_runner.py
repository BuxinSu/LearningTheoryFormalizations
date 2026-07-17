"""Transactional runner for packaged, numbered SQLite migrations."""

from __future__ import annotations

import shutil
import sqlite3
from dataclasses import dataclass
from datetime import datetime, timezone
from pathlib import Path

from .connection import SQLiteDatabase


@dataclass(frozen=True, slots=True)
class Migration:
    version: int
    path: Path


STATE_COLUMN_MIGRATIONS: dict[int, dict[str, tuple[str, ...]]] = {
    3: {
        "chapters": (
            "last_green_attempt_id TEXT",
            "latest_attempt_id TEXT",
            "pass_budgets_json TEXT NOT NULL DEFAULT '{}'",
        ),
        "findings": (
            "semantic_key TEXT",
            "review_run_id TEXT",
            "origin TEXT",
        ),
    }
}


def _now() -> str:
    return datetime.now(timezone.utc).isoformat()


def _statements(sql: str) -> list[str]:
    statements: list[str] = []
    buffer = ""
    for line in sql.splitlines(keepends=True):
        buffer += line
        if sqlite3.complete_statement(buffer):
            statement = buffer.strip()
            if statement:
                statements.append(statement)
            buffer = ""
    if buffer.strip():
        raise ValueError("incomplete SQL migration statement")
    return statements


class MigrationRunner:
    def __init__(
        self,
        database: SQLiteDatabase,
        migration_dir: Path,
        target_version: int,
        column_migrations: dict[int, dict[str, tuple[str, ...]]] | None = None,
    ) -> None:
        self.database = database
        self.migration_dir = migration_dir
        self.target_version = target_version
        self.column_migrations = column_migrations or {}

    def discover(self) -> list[Migration]:
        migrations: list[Migration] = []
        for path in sorted(self.migration_dir.glob("[0-9][0-9][0-9]_*.sql")):
            version = int(path.name.split("_", 1)[0])
            if version <= self.target_version:
                migrations.append(Migration(version, path))
        versions = [item.version for item in migrations]
        expected = list(range(1, self.target_version + 1))
        if versions != expected:
            raise RuntimeError(f"migration sequence mismatch: expected={expected}, found={versions}")
        return migrations

    @staticmethod
    def _columns(connection: sqlite3.Connection, table: str) -> set[str]:
        return {str(row[1]) for row in connection.execute(f"PRAGMA table_info({table})")}

    def _apply_columns(self, connection: sqlite3.Connection, version: int) -> None:
        for table, declarations in self.column_migrations.get(version, {}).items():
            existing = self._columns(connection, table)
            for declaration in declarations:
                name = declaration.split()[0]
                if name not in existing:
                    connection.execute(f"ALTER TABLE {table} ADD COLUMN {declaration}")
                    existing.add(name)

    def current_version(self) -> int:
        if not self.database.path.exists() or self.database.path.stat().st_size == 0:
            return 0
        connection = self.database.open()
        try:
            return int(connection.execute("PRAGMA user_version").fetchone()[0])
        finally:
            connection.close()

    def backup(self, version: int) -> Path:
        stamp = datetime.now(timezone.utc).strftime("%Y%m%dT%H%M%SZ")
        destination = self.database.path.with_name(
            f"{self.database.path.name}.v{version}.{stamp}.bak"
        )
        if not destination.exists():
            shutil.copy2(self.database.path, destination)
        return destination

    def migrate(self) -> None:
        migrations = self.discover()
        current = self.current_version()
        if current > self.target_version:
            raise RuntimeError(
                f"database schema {current} is newer than supported schema {self.target_version}"
            )
        if current < self.target_version and self.database.path.exists() and self.database.path.stat().st_size:
            self.backup(current)
        connection = self.database.open()
        try:
            connection.execute("PRAGMA journal_mode = WAL")
            for migration in migrations:
                if migration.version <= current:
                    continue
                try:
                    connection.execute("BEGIN IMMEDIATE")
                    connection.execute(
                        "CREATE TABLE IF NOT EXISTS schema_migrations "
                        "(version INTEGER PRIMARY KEY, applied_at TEXT NOT NULL)"
                    )
                    self._apply_columns(connection, migration.version)
                    for statement in _statements(migration.path.read_text(encoding="utf-8")):
                        connection.execute(statement)
                    connection.execute(
                        "INSERT OR REPLACE INTO schema_migrations(version, applied_at) VALUES (?, ?)",
                        (migration.version, _now()),
                    )
                    connection.execute(f"PRAGMA user_version = {migration.version}")
                    connection.commit()
                except Exception:
                    connection.rollback()
                    raise
        finally:
            connection.close()
