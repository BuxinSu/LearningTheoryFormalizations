from __future__ import annotations

import hashlib
import json
import re
import shutil
import sqlite3
import uuid
from datetime import datetime, timezone
from pathlib import Path

from ...infrastructure.hashing import sha256_file, sha256_json
from ...domain import MemoryDeclaration, TrustLevel
from .connection import SQLiteDatabase
from .migration_runner import MigrationRunner
from .memory_repositories import MemoryRepositories


def _now() -> str:
    return datetime.now(timezone.utc).isoformat()


def normalize_lean_type(value: str) -> str:
    return re.sub(r"\s+", " ", value).strip()


class KnowledgeStore:
    """Global structured memory plus content-addressed immutable blobs."""

    def __init__(self, database: Path, blob_root: Path | None = None) -> None:
        self.database = database
        self._database = SQLiteDatabase(database)
        self.blob_root = blob_root or database.parent / "blobs"
        self.blob_root.mkdir(parents=True, exist_ok=True)
        MigrationRunner(
            self._database,
            Path(__file__).with_name("migrations") / "memory",
            1,
        ).migrate()
        self._initialize_fts()
        self.repositories = MemoryRepositories.from_store(self)

    def _initialize_fts(self) -> None:
        with self.connect() as db:
            try:
                db.execute(
                    "CREATE VIRTUAL TABLE IF NOT EXISTS memory_fts "
                    "USING fts5(object_id, kind, name, body)"
                )
                self.fts_available = True
            except sqlite3.OperationalError:
                db.execute(
                    "CREATE TABLE IF NOT EXISTS memory_fts"
                    "(object_id TEXT, kind TEXT, name TEXT, body TEXT)"
                )
                self.fts_available = False

    def connect(self):
        """Compatibility transaction context backed by the shared SQLite adapter."""
        return self._database.connect()

    def put_blob(self, path: Path) -> str:
        digest = sha256_file(path)
        destination = self.blob_root / digest[:2] / digest[2:]
        destination.parent.mkdir(parents=True, exist_ok=True)
        if not destination.exists():
            shutil.copyfile(path, destination)
        with self.connect() as db:
            db.execute("INSERT OR IGNORE INTO blobs VALUES (?, ?, ?, ?)",
                       (digest, path.stat().st_size, path.suffix.lower() or "application/octet-stream", _now()))
        return digest

    def ingest_reference(self, path: Path, name: str, version: str, license: str) -> dict[str, str]:
        if not path.is_file():
            raise FileNotFoundError(path)
        blob_hash = self.put_blob(path)
        reference_id = f"ref-{sha256_json([name, version, blob_hash])[:24]}"
        text = path.read_text(encoding="utf-8", errors="replace") if path.suffix.lower() not in {".pdf"} else ""
        summary = normalize_lean_type(text[:1000])
        with self.connect() as db:
            db.execute(
                "INSERT OR IGNORE INTO reference_snapshots VALUES (?, ?, ?, ?, ?, ?, ?, ?)",
                (reference_id, name, version, license, blob_hash, str(path.resolve()), summary, _now()),
            )
            db.execute("DELETE FROM memory_fts WHERE object_id=?", (reference_id,))
            db.execute("INSERT INTO memory_fts VALUES (?, 'reference', ?, ?)", (reference_id, name, text))
        return {"id": reference_id, "blob_hash": blob_hash, "name": name, "version": version}

    def ingest_lean_module(self, path: Path, module: str, version: str, license: str,
                           toolchain: str | None = None, build_hash: str | None = None) -> list[MemoryDeclaration]:
        reference = self.ingest_reference(path, module, version, license)
        text = path.read_text(encoding="utf-8", errors="replace")
        pattern = re.compile(
            r"^\s*(?:theorem|lemma|corollary|proposition)\s+([A-Za-z0-9_'.]+)\b"
            r"(.*?)(?::=\s*(?:by|fun)|\bwhere\b)", re.MULTILINE | re.DOTALL,
        )
        declarations: list[MemoryDeclaration] = []
        for match in pattern.finditer(text):
            signature = normalize_lean_type(match.group(2))
            type_hash = hashlib.sha256(signature.encode()).hexdigest()
            declaration = MemoryDeclaration(
                id=f"decl-{sha256_json([module, match.group(1), type_hash])[:24]}",
                name=match.group(1), module=module, lean_type=signature,
                normalized_type=signature, type_hash=type_hash,
                documentation=f"Reference snapshot {reference['id']}",
                axiom_output="not yet independently checked",
                build_hash=build_hash, toolchain=toolchain,
            )
            self.save_declaration(declaration); declarations.append(declaration)
        return declarations

    def verify_blobs(self) -> list[str]:
        failures: list[str] = []
        with self.connect() as db:
            rows = db.execute("SELECT blob_hash FROM reference_snapshots").fetchall()
        for row in rows:
            digest = str(row["blob_hash"]); path = self.blob_root / digest[:2] / digest[2:]
            if not path.is_file() or sha256_file(path) != digest: failures.append(digest)
        return failures

    def save_declaration(self, declaration: MemoryDeclaration) -> None:
        with self.connect() as db:
            db.execute(
                "INSERT INTO declarations VALUES (?, ?, ?, ?, ?, ?, ?, ?) ON CONFLICT(id) DO UPDATE SET "
                "trust_level=excluded.trust_level, payload_json=excluded.payload_json",
                (declaration.id, declaration.name, declaration.module, declaration.normalized_type,
                 declaration.type_hash, declaration.trust_level, declaration.model_dump_json(), _now()),
            )
            db.execute("DELETE FROM declaration_dependencies WHERE declaration_id=?", (declaration.id,))
            db.executemany(
                "INSERT OR IGNORE INTO declaration_dependencies VALUES (?, ?)",
                [(declaration.id, dep) for dep in declaration.dependencies],
            )
            db.execute("DELETE FROM memory_fts WHERE object_id=?", (declaration.id,))
            db.execute("INSERT INTO memory_fts VALUES (?, 'declaration', ?, ?)",
                       (declaration.id, declaration.name, f"{declaration.lean_type}\n{declaration.documentation}"))

    def declaration(self, declaration_id: str) -> MemoryDeclaration:
        with self.connect() as db:
            row = db.execute("SELECT payload_json FROM declarations WHERE id=?", (declaration_id,)).fetchone()
        if not row: raise KeyError(declaration_id)
        return MemoryDeclaration.model_validate_json(row[0])

    def promote(self, declaration_id: str, trust: TrustLevel) -> MemoryDeclaration:
        order = list(TrustLevel)
        with self.connect() as db:
            row = db.execute("SELECT payload_json FROM declarations WHERE id=?", (declaration_id,)).fetchone()
        if not row: raise KeyError(declaration_id)
        declaration = MemoryDeclaration.model_validate_json(row[0])
        if order.index(trust) < order.index(declaration.trust_level):
            raise ValueError("memory trust cannot be downgraded")
        declaration.trust_level = trust; self.save_declaration(declaration); return declaration

    def link_source_declaration(self, source_claim_id: str, declaration_id: str,
                                coverage_status: str, evidence_hash: str | None = None) -> None:
        with self.connect() as db:
            db.execute(
                "INSERT OR REPLACE INTO source_declaration_correspondence VALUES (?, ?, ?, ?)",
                (source_claim_id, declaration_id, coverage_status, evidence_hash),
            )

    def save_literature_dossier(self, theorem_name: str, citation: str, strategy: str,
                                status: str, payload: dict[str, object],
                                source_blob_hash: str | None = None) -> str:
        dossier_id = f"dossier-{sha256_json([theorem_name, citation])[:24]}"
        with self.connect() as db:
            db.execute(
                "INSERT OR REPLACE INTO literature_dossiers VALUES (?, ?, ?, ?, ?, ?, ?, ?)",
                (dossier_id, theorem_name, citation, source_blob_hash, strategy, status,
                 json.dumps(payload, sort_keys=True, default=str), _now()),
            )
        return dossier_id

    def record_proof_strategy(self, declaration_id: str | None, title: str, strategy: str,
                              *, successful: bool, failure: str | None = None) -> str:
        record_id = f"strategy-{uuid.uuid4().hex}"
        with self.connect() as db:
            if successful:
                db.execute(
                    "INSERT INTO proof_strategies VALUES (?, ?, ?, ?, 1, ?, ?)",
                    (record_id, declaration_id, title, strategy,
                     json.dumps({"successful": True}), _now()),
                )
            else:
                db.execute(
                    "INSERT INTO failed_approaches VALUES (?, ?, ?, ?, ?, ?)",
                    (record_id, declaration_id, strategy, failure or "unspecified failure",
                     json.dumps({"title": title}), _now()),
                )
        return record_id

    def trust_counts(self) -> dict[str, int]:
        with self.connect() as db:
            rows = db.execute("SELECT trust_level, COUNT(*) AS count FROM declarations GROUP BY trust_level").fetchall()
        return {str(row["trust_level"]): int(row["count"]) for row in rows}

    def search(self, query: str, limit: int = 20) -> list[dict[str, object]]:
        normalized = normalize_lean_type(query)
        type_hash = hashlib.sha256(normalized.encode()).hexdigest()
        results: list[dict[str, object]] = []
        seen: set[str] = set()
        with self.connect() as db:
            exact = db.execute(
                "SELECT id, name, module, normalized_type, trust_level, payload_json FROM declarations "
                "WHERE name=? OR type_hash=? ORDER BY CASE WHEN name=? THEN 0 ELSE 1 END",
                (query, type_hash, query),
            ).fetchall()
            for row in exact:
                results.append({"id": row["id"], "kind": "declaration", "name": row["name"],
                                "module": row["module"], "type": row["normalized_type"],
                                "trust_level": row["trust_level"], "rank": "exact"}); seen.add(row["id"])
            deps = db.execute(
                "SELECT d.payload_json FROM declarations d JOIN declaration_dependencies e ON e.declaration_id=d.id "
                "WHERE e.dependency_name=?", (query,),
            ).fetchall()
            for row in deps:
                item = MemoryDeclaration.model_validate_json(row[0])
                if item.id not in seen:
                    results.append({"id": item.id, "kind": "declaration", "name": item.name,
                                    "module": item.module, "type": item.normalized_type,
                                    "trust_level": item.trust_level, "rank": "dependency"}); seen.add(item.id)
            try:
                fts = db.execute(
                    "SELECT object_id, kind, name, body FROM memory_fts WHERE memory_fts MATCH ? LIMIT ?",
                    (query, limit),
                ).fetchall() if self.fts_available else db.execute(
                    "SELECT object_id, kind, name, body FROM memory_fts WHERE name LIKE ? OR body LIKE ? LIMIT ?",
                    (f"%{query}%", f"%{query}%", limit),
                ).fetchall()
            except sqlite3.OperationalError:
                fts = []
            for row in fts:
                if row["object_id"] not in seen:
                    results.append({"id": row["object_id"], "kind": row["kind"], "name": row["name"],
                                    "snippet": str(row["body"])[:500], "rank": "full_text"}); seen.add(row["object_id"])
        return results[:limit]
