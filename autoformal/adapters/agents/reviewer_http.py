from __future__ import annotations

import json
from pathlib import Path

from ...domain import ReviewerResult, ServiceConfig
from .http_client import HTTPModelClient


class ReviewerHTTP:
    def __init__(self, config: ServiceConfig, schema_path: Path, retries: int = 3) -> None:
        self.client = HTTPModelClient(config, retries)
        self.schema = json.loads(schema_path.read_text(encoding="utf-8"))

    def review(self, prompt: str, attachments: list[Path] | None = None) -> ReviewerResult:
        payload = self.client.generate_json(
            prompt, self.schema, attachments=attachments, schema_name="autoformal_reviewer_result"
        )
        return ReviewerResult.model_validate(payload)

