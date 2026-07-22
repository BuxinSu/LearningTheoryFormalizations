"""Small domain-wide primitives."""

from datetime import datetime, timezone


def utc_now() -> datetime:
    return datetime.now(timezone.utc)
