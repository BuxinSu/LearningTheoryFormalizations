from __future__ import annotations

import io
import stat
import tarfile
import zipfile
from pathlib import Path

import httpx

from ...infrastructure.retry import retry_transport


class UnsafeArchive(ValueError):
    pass


def _safe_destination(root: Path, member: str) -> Path:
    destination = (root / member).resolve()
    if root.resolve() not in destination.parents and destination != root.resolve():
        raise UnsafeArchive(f"unsafe archive member: {member}")
    return destination


def extract_archive(payload: bytes, destination: Path) -> list[Path]:
    destination.mkdir(parents=True, exist_ok=True)
    extracted: list[Path] = []
    max_member_size = 100 * 1024 * 1024
    max_total_size = 1024 * 1024 * 1024
    total_size = 0
    try:
        with tarfile.open(fileobj=io.BytesIO(payload), mode="r:*") as archive:
            for member in archive.getmembers():
                if member.issym() or member.islnk():
                    raise UnsafeArchive(f"archive links are not allowed: {member.name}")
                if member.size > max_member_size:
                    raise UnsafeArchive(f"archive member is too large: {member.name}")
                total_size += member.size
                if total_size > max_total_size:
                    raise UnsafeArchive("archive uncompressed size exceeds safety limit")
                target = _safe_destination(destination, member.name)
                if member.isdir():
                    target.mkdir(parents=True, exist_ok=True)
                elif member.isfile():
                    target.parent.mkdir(parents=True, exist_ok=True)
                    source = archive.extractfile(member)
                    if source is not None:
                        target.write_bytes(source.read())
                        extracted.append(target)
            return extracted
    except tarfile.ReadError:
        pass
    try:
        with zipfile.ZipFile(io.BytesIO(payload)) as archive:
            for info in archive.infolist():
                if stat.S_ISLNK(info.external_attr >> 16):
                    raise UnsafeArchive(f"archive links are not allowed: {info.filename}")
                if info.file_size > max_member_size:
                    raise UnsafeArchive(f"archive member is too large: {info.filename}")
                total_size += info.file_size
                if total_size > max_total_size:
                    raise UnsafeArchive("archive uncompressed size exceeds safety limit")
                target = _safe_destination(destination, info.filename)
                if info.is_dir():
                    target.mkdir(parents=True, exist_ok=True)
                else:
                    target.parent.mkdir(parents=True, exist_ok=True)
                    target.write_bytes(archive.read(info))
                    extracted.append(target)
            return extracted
    except zipfile.BadZipFile as error:
        raise ValueError("authoritative source response is not a supported tar or zip archive") from error


def download_authoritative_source(url: str, destination: Path, retries: int = 3) -> list[Path]:
    def request() -> httpx.Response:
        response = httpx.get(url, follow_redirects=True, timeout=120)
        response.raise_for_status()
        return response

    response = retry_transport(request, retries, (httpx.TransportError, httpx.HTTPStatusError))
    (destination / "source-response.bin").parent.mkdir(parents=True, exist_ok=True)
    (destination / "source-response.bin").write_bytes(response.content)
    return extract_archive(response.content, destination / "tex")

