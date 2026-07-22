from __future__ import annotations

import random
import time
from collections.abc import Callable
from typing import TypeVar

T = TypeVar("T")


def retry_transport(operation: Callable[[], T], retries: int, retryable: tuple[type[BaseException], ...]) -> T:
    for attempt in range(retries + 1):
        try:
            return operation()
        except retryable:
            if attempt >= retries:
                raise
            time.sleep(min(30.0, (2**attempt) + random.random()))
    raise AssertionError("unreachable")

