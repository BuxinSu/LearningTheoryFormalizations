from __future__ import annotations

import base64
import json
import os
from pathlib import Path
from typing import Any

import httpx

from ...infrastructure.retry import retry_transport
from ...domain import ServiceConfig


class HTTPModelClient:
    def __init__(self, config: ServiceConfig, retries: int = 3) -> None:
        self.config = config
        self.retries = retries

    def _api_key(self) -> str:
        key = os.environ.get(self.config.api_key_env) or os.environ.get("OPENAI_API_KEY")
        if not key:
            raise RuntimeError(f"missing API key environment variable: {self.config.api_key_env}")
        return key

    def generate_json(
        self,
        prompt: str,
        schema: dict[str, Any],
        attachments: list[Path] | None = None,
        schema_name: str = "autoformal_result",
    ) -> dict[str, Any]:
        attachments = attachments or []
        key = self._api_key()
        headers = {"Authorization": f"Bearer {key}", "Content-Type": "application/json"}
        if self.config.protocol == "openai_responses":
            content: list[dict[str, Any]] = [{"type": "input_text", "text": prompt}]
            for path in attachments:
                mime = "application/pdf" if path.suffix.lower() == ".pdf" else "text/plain"
                encoded = base64.b64encode(path.read_bytes()).decode()
                content.append({
                    "type": "input_file", "filename": path.name,
                    "file_data": f"data:{mime};base64,{encoded}",
                })
            payload: dict[str, Any] = {
                "model": self.config.model,
                "input": [{"role": "user", "content": content}],
                "text": {"format": {"type": "json_schema", "name": schema_name, "strict": True, "schema": schema}},
            }
        else:
            payload = {
                "model": self.config.model, "prompt": prompt, "schema": schema,
                "attachments": [
                    {"filename": path.name, "data_base64": base64.b64encode(path.read_bytes()).decode()}
                    for path in attachments
                ],
            }

        def request() -> httpx.Response:
            response = httpx.post(
                self.config.endpoint, headers=headers, json=payload, timeout=self.config.timeout_seconds
            )
            if response.status_code >= 400:
                error = httpx.HTTPStatusError(
                    f"model endpoint returned HTTP {response.status_code}",
                    request=response.request, response=response,
                )
                if response.status_code not in {408, 409, 425, 429} and response.status_code < 500:
                    raise ValueError(str(error)) from error
                raise error
            return response

        response = retry_transport(request, self.retries, (httpx.TransportError, httpx.HTTPStatusError))
        data = response.json()
        if self.config.protocol == "generic_json":
            result = data.get("result", data)
            if not isinstance(result, dict):
                raise ValueError("generic model endpoint did not return a JSON object")
            return result
        text = self._openai_output_text(data)
        result = json.loads(text)
        if not isinstance(result, dict):
            raise ValueError("model output must be a JSON object")
        return result

    @staticmethod
    def _openai_output_text(data: dict[str, Any]) -> str:
        if isinstance(data.get("output_text"), str):
            return data["output_text"]
        for output in data.get("output", []):
            for content in output.get("content", []):
                if content.get("type") in {"output_text", "text"} and isinstance(content.get("text"), str):
                    return content["text"]
        raise ValueError("OpenAI Responses payload contained no output text")

