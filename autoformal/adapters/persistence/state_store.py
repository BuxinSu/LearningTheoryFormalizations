from __future__ import annotations

import json
import uuid
from datetime import datetime, timedelta, timezone
from pathlib import Path
from typing import Any

from ...domain import (
    AgentJob, BookConfig, FindingValidation, FormalizationPlan, HumanDecision,
    ObligationStatus, PathLease, PolicyProfile, PreflightManifest, ProofObligation,
    ReviewRun, SourceClaim, Stage,
)
from .connection import SQLiteDatabase
from .migration_runner import MigrationRunner, STATE_COLUMN_MIGRATIONS
from .state_repositories import StateRepositories

SCHEMA_VERSION = 3


def _now() -> str:
    return datetime.now(timezone.utc).isoformat()


def _json(value: Any) -> str:
    if hasattr(value, "model_dump"):
        value = value.model_dump(mode="json")
    return json.dumps(value, sort_keys=True, default=str)


class StateStore:
    """Transactional operational state.

    Artifacts remain immutable files; this database contains resumable indexes,
    lifecycle state, and hashes.  Migrations are additive so existing runs are
    indexed without rewriting their artifacts.
    """

    def __init__(self, database: Path) -> None:
        self.database = database
        self._database = SQLiteDatabase(database)
        MigrationRunner(
            self._database,
            Path(__file__).with_name("migrations") / "state",
            SCHEMA_VERSION,
            STATE_COLUMN_MIGRATIONS,
        ).migrate()
        self.repositories = StateRepositories.from_store(self)

    def connect(self):
        """Compatibility transaction context; new repositories receive SQLiteDatabase."""
        return self._database.connect()

    def register_book(self, config: BookConfig, config_path: Path, run_dir: Path) -> str:
        run_id = f"{datetime.now(timezone.utc):%Y%m%dT%H%M%SZ}-{uuid.uuid4().hex[:8]}"
        now = _now()
        with self.connect() as db:
            if db.execute("SELECT 1 FROM books WHERE book_id = ?", (config.book_id,)).fetchone():
                raise ValueError(f"book already registered: {config.book_id}")
            db.execute(
                "INSERT INTO books VALUES (?, ?, ?, ?, ?, ?, ?, ?)",
                (config.book_id, config.title, str(config_path), config.model_dump_json(),
                 Stage.REGISTERED, run_id, now, now),
            )
            db.execute("INSERT INTO runs VALUES (?, ?, ?, ?)", (run_id, config.book_id, str(run_dir / run_id), now))
        return run_id

    def update_book_config(self, config: BookConfig, config_path: Path) -> None:
        self.book(config.book_id)
        with self.connect() as db:
            db.execute(
                "UPDATE books SET title=?, config_path=?, config_json=?, updated_at=? WHERE book_id=?",
                (config.title, str(config_path), config.model_dump_json(), _now(), config.book_id),
            )
        self.event(config.book_id, None, "book_config_updated", {"config_path": str(config_path)})

    def book(self, book_id: str) -> dict[str, Any]:
        with self.connect() as db:
            row = db.execute("SELECT * FROM books WHERE book_id = ?", (book_id,)).fetchone()
        if not row:
            raise KeyError(f"unknown book: {book_id}")
        result = dict(row)
        result["config"] = json.loads(result.pop("config_json"))
        return result

    def config(self, book_id: str) -> BookConfig:
        return BookConfig.model_validate(self.book(book_id)["config"])

    def active_run_dir(self, book_id: str) -> Path:
        book = self.book(book_id)
        with self.connect() as db:
            row = db.execute("SELECT run_dir FROM runs WHERE run_id = ?", (book["active_run_id"],)).fetchone()
        if not row:
            raise RuntimeError(f"active run missing for {book_id}")
        return Path(row["run_dir"])

    def invalidate_chapters(self, book_id: str, reason: str) -> None:
        with self.connect() as db:
            db.execute(
                "UPDATE chapters SET stage=?, draft_session_id=NULL, revision_session_id=NULL, "
                "revision_cycle=0, last_green_attempt_id=NULL, latest_attempt_id=NULL, updated_at=? WHERE book_id=?",
                (Stage.REGISTERED, _now(), book_id),
            )
            db.execute("UPDATE findings SET active=0 WHERE book_id=?", (book_id,))
            db.execute("UPDATE formalization_plans SET active=0 WHERE book_id=?", (book_id,))
            db.execute("DELETE FROM human_decisions WHERE book_id=?", (book_id,))
        self.event(book_id, None, "downstream_invalidated", {"reason": reason})

    def set_book_stage(self, book_id: str, stage: Stage) -> None:
        with self.connect() as db:
            db.execute("UPDATE books SET stage=?, updated_at=? WHERE book_id=?", (stage, _now(), book_id))
        self.event(book_id, None, "book_stage", {"stage": stage})

    def chapter(self, book_id: str, chapter_id: str) -> dict[str, Any]:
        with self.connect() as db:
            row = db.execute("SELECT * FROM chapters WHERE book_id=? AND chapter_id=?", (book_id, chapter_id)).fetchone()
        if row:
            result = dict(row)
            result["pass_budgets"] = json.loads(result.get("pass_budgets_json") or "{}")
            return result
        with self.connect() as db:
            db.execute(
                "INSERT INTO chapters(book_id, chapter_id, stage, updated_at) VALUES (?, ?, ?, ?)",
                (book_id, chapter_id, Stage.REGISTERED, _now()),
            )
        return self.chapter(book_id, chapter_id)

    def set_chapter_stage(self, book_id: str, chapter_id: str, stage: Stage, **fields: Any) -> None:
        self.chapter(book_id, chapter_id)
        allowed = {
            "draft_session_id", "revision_session_id", "revision_cycle", "last_green_attempt_id",
            "latest_attempt_id", "pass_budgets_json",
        }
        assignments = ["stage=?", "updated_at=?"]
        values: list[Any] = [stage, _now()]
        for key, value in fields.items():
            if key == "pass_budgets":
                key, value = "pass_budgets_json", _json(value)
            if key not in allowed:
                raise ValueError(f"invalid chapter field: {key}")
            assignments.append(f"{key}=?")
            values.append(value)
        values.extend([book_id, chapter_id])
        with self.connect() as db:
            db.execute(f"UPDATE chapters SET {', '.join(assignments)} WHERE book_id=? AND chapter_id=?", values)
        self.event(book_id, chapter_id, "chapter_stage", {"stage": stage, **fields})

    def save_policy_profile(self, profile: PolicyProfile) -> None:
        with self.connect() as db:
            db.execute("UPDATE policy_profiles SET active=0 WHERE book_id=?", (profile.book_id,))
            db.execute(
                "INSERT INTO policy_profiles(book_id, policy_hash, payload_json, active, created_at) VALUES (?, ?, ?, 1, ?) "
                "ON CONFLICT(book_id, policy_hash) DO UPDATE SET payload_json=excluded.payload_json, active=1",
                (profile.book_id, profile.policy_hash, profile.model_dump_json(), _now()),
            )

    def active_policy_profile(self, book_id: str) -> PolicyProfile | None:
        with self.connect() as db:
            row = db.execute(
                "SELECT payload_json FROM policy_profiles WHERE book_id=? AND active=1 ORDER BY id DESC LIMIT 1", (book_id,)
            ).fetchone()
        return PolicyProfile.model_validate_json(row[0]) if row else None

    def save_preflight(self, manifest: PreflightManifest) -> None:
        with self.connect() as db:
            db.execute(
                "INSERT INTO preflight_checks(book_id, policy_hash, passed, payload_json, created_at) VALUES (?, ?, ?, ?, ?)",
                (manifest.book_id, manifest.policy_hash, int(manifest.passed), manifest.model_dump_json(), _now()),
            )

    def latest_preflight(self, book_id: str) -> PreflightManifest | None:
        with self.connect() as db:
            row = db.execute(
                "SELECT payload_json FROM preflight_checks WHERE book_id=? ORDER BY id DESC LIMIT 1", (book_id,)
            ).fetchone()
        return PreflightManifest.model_validate_json(row[0]) if row else None

    def save_plan(self, plan: FormalizationPlan) -> None:
        with self.connect() as db:
            db.execute("UPDATE formalization_plans SET active=0 WHERE book_id=?", (plan.book_id,))
            db.execute(
                "INSERT OR REPLACE INTO formalization_plans VALUES (?, ?, ?, ?, 1, ?)",
                (plan.id, plan.book_id, plan.policy_hash, plan.model_dump_json(), _now()),
            )

    def active_plan(self, book_id: str) -> FormalizationPlan | None:
        with self.connect() as db:
            row = db.execute(
                "SELECT payload_json FROM formalization_plans WHERE book_id=? AND active=1 ORDER BY created_at DESC LIMIT 1",
                (book_id,),
            ).fetchone()
        return FormalizationPlan.model_validate_json(row[0]) if row else None

    def save_source_claim(self, claim: SourceClaim) -> None:
        with self.connect() as db:
            db.execute(
                "INSERT INTO source_claims VALUES (?, ?, ?, ?, ?) ON CONFLICT(claim_id) DO UPDATE SET "
                "payload_json=excluded.payload_json, updated_at=excluded.updated_at",
                (claim.id, claim.book_id, claim.chapter_id, claim.model_dump_json(), _now()),
            )

    def source_claims(self, book_id: str, chapter_id: str | None = None) -> list[SourceClaim]:
        query, args = "SELECT payload_json FROM source_claims WHERE book_id=?", [book_id]
        if chapter_id is not None:
            query += " AND chapter_id=?"; args.append(chapter_id)
        query += " ORDER BY claim_id"
        with self.connect() as db:
            rows = db.execute(query, args).fetchall()
        return [SourceClaim.model_validate_json(row[0]) for row in rows]

    def save_obligation(self, obligation: ProofObligation) -> None:
        obligation.updated_at = datetime.now(timezone.utc)
        with self.connect() as db:
            db.execute(
                "INSERT INTO obligations VALUES (?, ?, ?, ?, ?, ?, ?, ?, ?) ON CONFLICT(obligation_id) DO UPDATE SET "
                "status=excluded.status, marker=excluded.marker, isolated=excluded.isolated, "
                "payload_json=excluded.payload_json, updated_at=excluded.updated_at",
                (obligation.id, obligation.book_id, obligation.chapter_id, obligation.kind,
                 obligation.status, obligation.marker, int(obligation.isolated), obligation.model_dump_json(), _now()),
            )

    def obligation(self, obligation_id: str) -> ProofObligation:
        with self.connect() as db:
            row = db.execute("SELECT payload_json FROM obligations WHERE obligation_id=?", (obligation_id,)).fetchone()
        if not row:
            raise KeyError(f"unknown obligation: {obligation_id}")
        return ProofObligation.model_validate_json(row[0])

    def obligations(self, book_id: str, chapter_id: str | None = None) -> list[ProofObligation]:
        query, args = "SELECT payload_json FROM obligations WHERE book_id=?", [book_id]
        if chapter_id is not None:
            query += " AND chapter_id=?"; args.append(chapter_id)
        query += " ORDER BY obligation_id"
        with self.connect() as db:
            rows = db.execute(query, args).fetchall()
        return [ProofObligation.model_validate_json(row[0]) for row in rows]

    def transition_obligation(self, obligation_id: str, status: ObligationStatus, **evidence: Any) -> ProofObligation:
        obligation = self.obligation(obligation_id)
        if status == ObligationStatus.WAIVED and (not evidence.get("approver") or not evidence.get("reason")):
            raise ValueError("waiving an obligation requires approver and reason evidence")
        if obligation.status == ObligationStatus.DISCHARGED and status == ObligationStatus.OPEN:
            raise ValueError("a discharged obligation cannot be reopened without creating a new obligation")
        obligation.status = status
        if "approver" in evidence: obligation.waiver_approver = str(evidence["approver"])
        if "reason" in evidence: obligation.waiver_reason = str(evidence["reason"])
        self.save_obligation(obligation)
        self.event(obligation.book_id, obligation.chapter_id, "obligation_transition", {"id": obligation_id, "status": status, **evidence})
        return obligation

    def save_job(self, job: AgentJob) -> None:
        job.updated_at = datetime.now(timezone.utc)
        with self.connect() as db:
            existing_row = db.execute(
                "SELECT payload_json FROM agent_jobs WHERE job_id=?", (job.id,)
            ).fetchone()
            if existing_row:
                existing = AgentJob.model_validate_json(existing_row[0])
                job.latest_attempt_id = job.latest_attempt_id or existing.latest_attempt_id
                job.last_green_attempt_id = (
                    job.last_green_attempt_id or existing.last_green_attempt_id
                )
                job.checkpoint = job.checkpoint or existing.checkpoint
            db.execute(
                "INSERT INTO agent_jobs VALUES (?, ?, ?, ?, ?, ?, ?, ?, ?, ?) ON CONFLICT(job_id) DO UPDATE SET "
                "status=excluded.status, payload_json=excluded.payload_json, updated_at=excluded.updated_at",
                (job.id, job.book_id, job.chapter_id, job.role, job.pass_name, int(job.read_only),
                 job.status, job.input_snapshot_hash, job.model_dump_json(), _now()),
            )

    def jobs(self, book_id: str) -> list[AgentJob]:
        with self.connect() as db:
            rows = db.execute("SELECT payload_json FROM agent_jobs WHERE book_id=? ORDER BY updated_at DESC", (book_id,)).fetchall()
        return [AgentJob.model_validate_json(row[0]) for row in rows]

    def active_job(self, book_id: str, chapter_id: str | None, roles: set[str]) -> AgentJob | None:
        return next((job for job in self.jobs(book_id)
                     if job.chapter_id == chapter_id and job.role in roles and job.status == "running"), None)

    def save_agent_session(self, session_id: str, job_id: str, provider: str,
                           metadata: Any | None = None, ended: bool = False) -> None:
        with self.connect() as db:
            db.execute(
                "INSERT INTO agent_sessions VALUES (?, ?, ?, ?, ?, ?) ON CONFLICT(session_id) DO UPDATE SET "
                "ended_at=excluded.ended_at, metadata_json=excluded.metadata_json",
                (session_id, job_id, provider, _now(), _now() if ended else None,
                 _json(metadata or {})),
            )

    @staticmethod
    def _paths_overlap(first: str, second: str) -> bool:
        a, b = Path(first).resolve(), Path(second).resolve()
        return a == b or a in b.parents or b in a.parents

    def acquire_lease(self, book_id: str, job_id: str, scope: str, path: str, ttl_seconds: int = 3600) -> PathLease:
        now = datetime.now(timezone.utc)
        expires = now + timedelta(seconds=ttl_seconds)
        with self.connect() as db:
            rows = db.execute(
                "SELECT path, job_id FROM path_leases WHERE book_id=? AND released_at IS NULL AND expires_at>?",
                (book_id, now.isoformat()),
            ).fetchall()
            conflicts = [row for row in rows if row["job_id"] != job_id and self._paths_overlap(path, row["path"])]
            if conflicts:
                raise ValueError(f"path lease conflict with job {conflicts[0]['job_id']}: {conflicts[0]['path']}")
            lease = PathLease(
                id=f"lease-{uuid.uuid4().hex}", book_id=book_id, job_id=job_id,
                scope=scope, path=str(Path(path).resolve()), acquired_at=now, expires_at=expires,
            )
            db.execute(
                "INSERT INTO path_leases VALUES (?, ?, ?, ?, ?, ?, ?, NULL, ?)",
                (lease.id, book_id, job_id, scope, lease.path, now.isoformat(), expires.isoformat(), lease.model_dump_json()),
            )
        return lease

    def release_lease(self, lease_id: str) -> None:
        released = _now()
        with self.connect() as db:
            row = db.execute("SELECT payload_json FROM path_leases WHERE lease_id=?", (lease_id,)).fetchone()
            if not row: raise KeyError(f"unknown lease: {lease_id}")
            lease = PathLease.model_validate_json(row[0]); lease.released_at = datetime.fromisoformat(released)
            db.execute("UPDATE path_leases SET released_at=?, payload_json=? WHERE lease_id=?", (released, lease.model_dump_json(), lease_id))

    def leases(self, book_id: str, active_only: bool = True) -> list[PathLease]:
        query = "SELECT payload_json FROM path_leases WHERE book_id=?"
        args: list[Any] = [book_id]
        if active_only:
            query += " AND released_at IS NULL AND expires_at>?"; args.append(_now())
        query += " ORDER BY acquired_at"
        with self.connect() as db:
            rows = db.execute(query, args).fetchall()
        return [PathLease.model_validate_json(row[0]) for row in rows]

    def create_attempt(self, job_id: str, status: str, session_id: str | None = None, checkpoint: str | None = None, green_commit: str | None = None, payload: Any = None) -> str:
        attempt_id = f"attempt-{uuid.uuid4().hex}"
        with self.connect() as db:
            ordinal = int(db.execute("SELECT COUNT(*) FROM attempts WHERE job_id=?", (job_id,)).fetchone()[0]) + 1
            db.execute(
                "INSERT INTO attempts VALUES (?, ?, ?, ?, ?, ?, ?, ?, ?)",
                (attempt_id, job_id, session_id, ordinal, status, checkpoint, green_commit, _json(payload or {}), _now()),
            )
            row = db.execute("SELECT payload_json FROM agent_jobs WHERE job_id=?", (job_id,)).fetchone()
            if row:
                job = AgentJob.model_validate_json(row[0]); job.latest_attempt_id = attempt_id
                if green_commit: job.last_green_attempt_id = attempt_id; job.checkpoint = green_commit
                job.updated_at = datetime.now(timezone.utc)
                db.execute("UPDATE agent_jobs SET status=?, payload_json=?, updated_at=? WHERE job_id=?",
                           (job.status, job.model_dump_json(), _now(), job_id))
                if green_commit and job.chapter_id is not None:
                    db.execute("UPDATE findings SET active=0 WHERE book_id=? AND chapter_id=?",
                               (job.book_id, job.chapter_id))
                    db.execute(
                        "INSERT INTO events(book_id, chapter_id, kind, payload_json, created_at) VALUES (?, ?, ?, ?, ?)",
                        (job.book_id, job.chapter_id, "review_findings_invalidated",
                         _json({"reason": f"new green attempt {attempt_id}"}), _now()),
                    )
        return attempt_id

    def invalidate_review_findings(self, book_id: str, chapter_id: str, reason: str) -> None:
        with self.connect() as db:
            db.execute("UPDATE findings SET active=0 WHERE book_id=? AND chapter_id=?",
                       (book_id, chapter_id))
        self.event(book_id, chapter_id, "review_findings_invalidated", {"reason": reason})

    @staticmethod
    def semantic_finding_key(finding: dict[str, Any]) -> str:
        import hashlib, re
        difference = re.sub(r"\s+", " ", str(finding.get("difference", "")).strip().lower())
        raw = "|".join((str(finding.get("audit_unit_id") or finding.get("source_location", "")), str(finding.get("category", "")), difference))
        return hashlib.sha256(raw.encode()).hexdigest()

    def replace_findings(self, book_id: str, chapter_id: str, findings: list[dict[str, Any]], review_run_id: str | None = None, origin: str = "proofread") -> None:
        deduplicated: dict[str, dict[str, Any]] = {}
        for finding in findings:
            deduplicated[self.semantic_finding_key(finding)] = finding
        with self.connect() as db:
            db.execute("UPDATE findings SET active=0 WHERE book_id=? AND chapter_id=?", (book_id, chapter_id))
            for semantic_key, finding in deduplicated.items():
                finding_id = str(finding["id"])
                # Avoid collision with an older local ID that represented a different semantic finding.
                collision = db.execute(
                    "SELECT semantic_key FROM findings WHERE book_id=? AND chapter_id=? AND finding_id=?",
                    (book_id, chapter_id, finding_id),
                ).fetchone()
                if collision and collision[0] not in {None, semantic_key}:
                    finding_id = f"{finding_id}:{semantic_key[:12]}"; finding = {**finding, "id": finding_id}
                db.execute(
                    "INSERT INTO findings(book_id, chapter_id, finding_id, payload_json, active, created_at, semantic_key, review_run_id, origin) "
                    "VALUES (?, ?, ?, ?, 1, ?, ?, ?, ?) ON CONFLICT(book_id, chapter_id, finding_id) DO UPDATE SET "
                    "payload_json=excluded.payload_json, active=1, created_at=excluded.created_at, semantic_key=excluded.semantic_key, "
                    "review_run_id=excluded.review_run_id, origin=excluded.origin",
                    (book_id, chapter_id, finding_id, _json(finding), _now(), semantic_key, review_run_id, origin),
                )

    def active_findings(self, book_id: str, chapter_id: str) -> list[dict[str, Any]]:
        with self.connect() as db:
            rows = db.execute("SELECT payload_json FROM findings WHERE book_id=? AND chapter_id=? AND active=1 ORDER BY finding_id", (book_id, chapter_id)).fetchall()
        return [json.loads(row[0]) for row in rows]

    def save_review_run(self, run: ReviewRun) -> None:
        with self.connect() as db:
            db.execute(
                "INSERT OR REPLACE INTO review_runs VALUES (?, ?, ?, ?, ?, ?, ?)",
                (run.id, run.book_id, run.chapter_id, run.semantic_fingerprint, run.status, run.model_dump_json(), _now()),
            )

    def review_runs(self, book_id: str, chapter_id: str | None = None) -> list[ReviewRun]:
        query, args = "SELECT payload_json FROM review_runs WHERE book_id=?", [book_id]
        if chapter_id is not None: query += " AND chapter_id=?"; args.append(chapter_id)
        query += " ORDER BY created_at DESC"
        with self.connect() as db: rows = db.execute(query, args).fetchall()
        return [ReviewRun.model_validate_json(row[0]) for row in rows]

    def save_finding_validation(self, validation: FindingValidation) -> None:
        with self.connect() as db:
            db.execute(
                "INSERT OR REPLACE INTO finding_validations VALUES (?, ?, ?, ?, ?, ?)",
                (validation.id, validation.finding_id, validation.review_run_id, validation.disposition,
                 validation.model_dump_json(), _now()),
            )

    def finding_validations(self, review_run_id: str) -> list[FindingValidation]:
        with self.connect() as db:
            rows = db.execute("SELECT payload_json FROM finding_validations WHERE review_run_id=? ORDER BY created_at", (review_run_id,)).fetchall()
        return [FindingValidation.model_validate_json(row[0]) for row in rows]

    def save_decision(self, book_id: str, chapter_id: str, decision: HumanDecision) -> None:
        with self.connect() as db:
            db.execute(
                "INSERT INTO human_decisions VALUES (?, ?, ?, ?, ?) ON CONFLICT(book_id, chapter_id, audit_unit_id) DO UPDATE SET "
                "payload_json=excluded.payload_json, updated_at=excluded.updated_at",
                (book_id, chapter_id, decision.audit_unit_id, decision.model_dump_json(), _now()),
            )
        self.event(book_id, chapter_id, "human_decision", decision.model_dump(mode="json"))

    def decisions(self, book_id: str, chapter_id: str) -> dict[str, HumanDecision]:
        with self.connect() as db:
            rows = db.execute("SELECT audit_unit_id, payload_json FROM human_decisions WHERE book_id=? AND chapter_id=?", (book_id, chapter_id)).fetchall()
        return {row[0]: HumanDecision.model_validate_json(row[1]) for row in rows}

    def event(self, book_id: str, chapter_id: str | None, kind: str, payload: Any) -> None:
        with self.connect() as db:
            db.execute("INSERT INTO events(book_id, chapter_id, kind, payload_json, created_at) VALUES (?, ?, ?, ?, ?)", (book_id, chapter_id, kind, _json(payload), _now()))

    def status(self, book_id: str) -> dict[str, Any]:
        book = self.book(book_id)
        with self.connect() as db:
            chapters = [dict(row) for row in db.execute("SELECT * FROM chapters WHERE book_id=? ORDER BY chapter_id", (book_id,)).fetchall()]
        for chapter in chapters:
            chapter["pass_budgets"] = json.loads(chapter.pop("pass_budgets_json", None) or "{}")
        book["chapters"] = chapters
        book["policy_profile"] = (profile.model_dump(mode="json") if (profile := self.active_policy_profile(book_id)) else None)
        book["preflight"] = (manifest.model_dump(mode="json") if (manifest := self.latest_preflight(book_id)) else None)
        book["plan_id"] = (plan.id if (plan := self.active_plan(book_id)) else None)
        book["obligation_counts"] = {}
        for obligation in self.obligations(book_id):
            key = f"{obligation.kind}:{obligation.status}"
            book["obligation_counts"][key] = book["obligation_counts"].get(key, 0) + 1
        book["jobs"] = [job.model_dump(mode="json") for job in self.jobs(book_id)]
        book["leases"] = [lease.model_dump(mode="json") for lease in self.leases(book_id)]
        return book
