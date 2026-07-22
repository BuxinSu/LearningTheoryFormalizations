CREATE TABLE IF NOT EXISTS schema_migrations (
    version INTEGER PRIMARY KEY,
    applied_at TEXT NOT NULL
);
CREATE TABLE IF NOT EXISTS books (
    book_id TEXT PRIMARY KEY,
    title TEXT NOT NULL,
    config_path TEXT NOT NULL,
    config_json TEXT NOT NULL,
    stage TEXT NOT NULL,
    active_run_id TEXT,
    created_at TEXT NOT NULL,
    updated_at TEXT NOT NULL
);
CREATE TABLE IF NOT EXISTS runs (
    run_id TEXT PRIMARY KEY,
    book_id TEXT NOT NULL REFERENCES books(book_id),
    run_dir TEXT NOT NULL,
    created_at TEXT NOT NULL
);
CREATE TABLE IF NOT EXISTS chapters (
    book_id TEXT NOT NULL REFERENCES books(book_id),
    chapter_id TEXT NOT NULL,
    stage TEXT NOT NULL,
    draft_session_id TEXT,
    revision_session_id TEXT,
    revision_cycle INTEGER NOT NULL DEFAULT 0,
    updated_at TEXT NOT NULL,
    PRIMARY KEY (book_id, chapter_id)
);
CREATE TABLE IF NOT EXISTS findings (
    book_id TEXT NOT NULL,
    chapter_id TEXT NOT NULL,
    finding_id TEXT NOT NULL,
    payload_json TEXT NOT NULL,
    active INTEGER NOT NULL DEFAULT 1,
    created_at TEXT NOT NULL,
    PRIMARY KEY (book_id, chapter_id, finding_id)
);
CREATE TABLE IF NOT EXISTS human_decisions (
    book_id TEXT NOT NULL,
    chapter_id TEXT NOT NULL,
    audit_unit_id TEXT NOT NULL,
    payload_json TEXT NOT NULL,
    updated_at TEXT NOT NULL,
    PRIMARY KEY (book_id, chapter_id, audit_unit_id)
);
CREATE TABLE IF NOT EXISTS events (
    id INTEGER PRIMARY KEY AUTOINCREMENT,
    book_id TEXT NOT NULL,
    chapter_id TEXT,
    kind TEXT NOT NULL,
    payload_json TEXT NOT NULL,
    created_at TEXT NOT NULL
);
