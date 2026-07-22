from __future__ import annotations

import os
from contextlib import contextmanager
from pathlib import Path
from typing import Iterator


class LockBusy(RuntimeError):
    pass


@contextmanager
def file_lock(path: Path) -> Iterator[None]:
    path.parent.mkdir(parents=True, exist_ok=True)
    try:
        descriptor = os.open(path, os.O_CREAT | os.O_EXCL | os.O_WRONLY)
    except FileExistsError as error:
        raise LockBusy(f"workflow lock is already held: {path}") from error
    try:
        os.write(descriptor, str(os.getpid()).encode())
        os.close(descriptor)
        yield
    finally:
        path.unlink(missing_ok=True)

