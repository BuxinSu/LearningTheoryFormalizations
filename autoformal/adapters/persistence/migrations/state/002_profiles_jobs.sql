CREATE TABLE IF NOT EXISTS policy_profiles (
    id INTEGER PRIMARY KEY AUTOINCREMENT,
    book_id TEXT NOT NULL,
    policy_hash TEXT NOT NULL,
    payload_json TEXT NOT NULL,
    active INTEGER NOT NULL DEFAULT 1,
    created_at TEXT NOT NULL,
    UNIQUE(book_id, policy_hash)
);
CREATE TABLE IF NOT EXISTS preflight_checks (
    id INTEGER PRIMARY KEY AUTOINCREMENT,
    book_id TEXT NOT NULL,
    policy_hash TEXT NOT NULL,
    passed INTEGER NOT NULL,
    payload_json TEXT NOT NULL,
    created_at TEXT NOT NULL
);
CREATE TABLE IF NOT EXISTS formalization_plans (
    plan_id TEXT PRIMARY KEY,
    book_id TEXT NOT NULL,
    policy_hash TEXT NOT NULL,
    payload_json TEXT NOT NULL,
    active INTEGER NOT NULL DEFAULT 1,
    created_at TEXT NOT NULL
);
CREATE TABLE IF NOT EXISTS source_claims (
    claim_id TEXT PRIMARY KEY,
    book_id TEXT NOT NULL,
    chapter_id TEXT,
    payload_json TEXT NOT NULL,
    updated_at TEXT NOT NULL
);
CREATE TABLE IF NOT EXISTS obligations (
    obligation_id TEXT PRIMARY KEY,
    book_id TEXT NOT NULL,
    chapter_id TEXT,
    kind TEXT NOT NULL,
    status TEXT NOT NULL,
    marker TEXT,
    isolated INTEGER NOT NULL DEFAULT 0,
    payload_json TEXT NOT NULL,
    updated_at TEXT NOT NULL
);
CREATE TABLE IF NOT EXISTS agent_jobs (
    job_id TEXT PRIMARY KEY,
    book_id TEXT NOT NULL,
    chapter_id TEXT,
    role TEXT NOT NULL,
    pass_name TEXT NOT NULL,
    read_only INTEGER NOT NULL,
    status TEXT NOT NULL,
    input_snapshot_hash TEXT NOT NULL,
    payload_json TEXT NOT NULL,
    updated_at TEXT NOT NULL
);
CREATE TABLE IF NOT EXISTS path_leases (
    lease_id TEXT PRIMARY KEY,
    book_id TEXT NOT NULL,
    job_id TEXT NOT NULL,
    scope TEXT NOT NULL,
    path TEXT NOT NULL,
    acquired_at TEXT NOT NULL,
    expires_at TEXT NOT NULL,
    released_at TEXT,
    payload_json TEXT NOT NULL
);
CREATE INDEX IF NOT EXISTS idx_obligations_book_status
    ON obligations(book_id, chapter_id, status);
CREATE INDEX IF NOT EXISTS idx_jobs_book_status
    ON agent_jobs(book_id, status);
CREATE INDEX IF NOT EXISTS idx_leases_active
    ON path_leases(book_id, path, released_at, expires_at);
