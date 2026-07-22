"""Reusable Lean declaration memory model."""

from datetime import datetime

from pydantic import BaseModel, Field

from .common import utc_now
from .enums import TrustLevel


class MemoryDeclaration(BaseModel):
    id: str
    name: str
    module: str
    lean_type: str
    normalized_type: str
    type_hash: str
    documentation: str = ""
    imports: list[str] = Field(default_factory=list)
    dependencies: list[str] = Field(default_factory=list)
    axiom_output: str = ""
    source_claim_ids: list[str] = Field(default_factory=list)
    trust_level: TrustLevel = TrustLevel.KERNEL_VERIFIED_CANDIDATE
    build_hash: str | None = None
    toolchain: str | None = None
    created_at: datetime = Field(default_factory=utc_now)
