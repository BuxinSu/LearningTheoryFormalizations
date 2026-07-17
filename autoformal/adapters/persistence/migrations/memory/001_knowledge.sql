CREATE TABLE IF NOT EXISTS reference_snapshots (
    id TEXT PRIMARY KEY,
    name TEXT NOT NULL,
    version TEXT NOT NULL,
    license TEXT NOT NULL,
    blob_hash TEXT NOT NULL,
    source_path TEXT NOT NULL,
    summary TEXT NOT NULL,
    created_at TEXT NOT NULL,
    UNIQUE(name, version, blob_hash)
);
CREATE TABLE IF NOT EXISTS blobs (
    blob_hash TEXT PRIMARY KEY,
    size_bytes INTEGER NOT NULL,
    media_type TEXT NOT NULL,
    created_at TEXT NOT NULL
);
CREATE TABLE IF NOT EXISTS lean_modules (
    id TEXT PRIMARY KEY,
    module TEXT NOT NULL,
    imports_json TEXT NOT NULL,
    toolchain TEXT,
    build_hash TEXT,
    source_blob_hash TEXT,
    payload_json TEXT NOT NULL,
    created_at TEXT NOT NULL
);
CREATE TABLE IF NOT EXISTS declarations (
    id TEXT PRIMARY KEY,
    name TEXT NOT NULL,
    module TEXT NOT NULL,
    normalized_type TEXT NOT NULL,
    type_hash TEXT NOT NULL,
    trust_level TEXT NOT NULL,
    payload_json TEXT NOT NULL,
    created_at TEXT NOT NULL
);
CREATE UNIQUE INDEX IF NOT EXISTS idx_memory_decl_identity
    ON declarations(name, module, type_hash);
CREATE INDEX IF NOT EXISTS idx_memory_decl_type ON declarations(type_hash);
CREATE TABLE IF NOT EXISTS declaration_dependencies (
    declaration_id TEXT NOT NULL,
    dependency_name TEXT NOT NULL,
    PRIMARY KEY(declaration_id, dependency_name)
);
CREATE TABLE IF NOT EXISTS source_declaration_correspondence (
    source_claim_id TEXT NOT NULL,
    declaration_id TEXT NOT NULL,
    coverage_status TEXT NOT NULL,
    evidence_hash TEXT,
    PRIMARY KEY(source_claim_id, declaration_id)
);
CREATE TABLE IF NOT EXISTS proof_strategies (
    id TEXT PRIMARY KEY,
    declaration_id TEXT,
    title TEXT NOT NULL,
    strategy TEXT NOT NULL,
    successful INTEGER NOT NULL,
    payload_json TEXT NOT NULL,
    created_at TEXT NOT NULL
);
CREATE TABLE IF NOT EXISTS failed_approaches (
    id TEXT PRIMARY KEY,
    declaration_id TEXT,
    approach TEXT NOT NULL,
    failure TEXT NOT NULL,
    payload_json TEXT NOT NULL,
    created_at TEXT NOT NULL
);
CREATE TABLE IF NOT EXISTS literature_dossiers (
    id TEXT PRIMARY KEY,
    theorem_name TEXT NOT NULL,
    citation TEXT NOT NULL,
    source_blob_hash TEXT,
    strategy TEXT NOT NULL,
    status TEXT NOT NULL,
    payload_json TEXT NOT NULL,
    updated_at TEXT NOT NULL
);
CREATE TABLE IF NOT EXISTS lessons (
    id TEXT PRIMARY KEY,
    kind TEXT NOT NULL,
    title TEXT NOT NULL,
    body TEXT NOT NULL,
    trust_level TEXT NOT NULL,
    payload_json TEXT NOT NULL,
    created_at TEXT NOT NULL
);
