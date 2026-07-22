CREATE TABLE IF NOT EXISTS agent_sessions (
    session_id TEXT PRIMARY KEY,
    job_id TEXT NOT NULL,
    provider TEXT NOT NULL,
    started_at TEXT NOT NULL,
    ended_at TEXT,
    metadata_json TEXT NOT NULL
);
CREATE TABLE IF NOT EXISTS attempts (
    attempt_id TEXT PRIMARY KEY,
    job_id TEXT NOT NULL,
    session_id TEXT,
    ordinal INTEGER NOT NULL,
    status TEXT NOT NULL,
    checkpoint TEXT,
    green_commit TEXT,
    payload_json TEXT NOT NULL,
    created_at TEXT NOT NULL
);
CREATE TABLE IF NOT EXISTS review_runs (
    review_run_id TEXT PRIMARY KEY,
    book_id TEXT NOT NULL,
    chapter_id TEXT,
    semantic_fingerprint TEXT NOT NULL,
    status TEXT NOT NULL,
    payload_json TEXT NOT NULL,
    created_at TEXT NOT NULL
);
CREATE TABLE IF NOT EXISTS finding_validations (
    validation_id TEXT PRIMARY KEY,
    finding_id TEXT NOT NULL,
    review_run_id TEXT NOT NULL,
    disposition TEXT NOT NULL,
    payload_json TEXT NOT NULL,
    created_at TEXT NOT NULL
);
CREATE INDEX IF NOT EXISTS idx_review_runs_book
    ON review_runs(book_id, chapter_id, created_at);
CREATE UNIQUE INDEX IF NOT EXISTS idx_findings_semantic_active
    ON findings(book_id, chapter_id, semantic_key)
    WHERE semantic_key IS NOT NULL AND active = 1;
