"""Global reusable theorem-memory commands."""

from pathlib import Path
from typing import Annotated

import typer

from ..context import emit, memory


def ingest_reference(
    path: Annotated[Path, typer.Argument(exists=True, dir_okay=False)],
    name: Annotated[str, typer.Option("--name")],
    version: Annotated[str, typer.Option("--version")],
    license_name: Annotated[str, typer.Option("--license")],
) -> None:
    emit(memory().ingest_reference(path, name, version, license_name))


def ingest_lean(
    path: Annotated[Path, typer.Argument(exists=True, dir_okay=False)],
    module: Annotated[str, typer.Option("--module")],
    version: Annotated[str, typer.Option("--version")],
    license_name: Annotated[str, typer.Option("--license")],
) -> None:
    emit(
        [
            item.model_dump(mode="json")
            for item in memory().ingest_lean_module(
                path, module, version, license_name
            )
        ]
    )


def search(query: str) -> None:
    emit(memory().search(query))


def register(app: typer.Typer) -> None:
    app.command("ingest-reference")(ingest_reference)
    app.command("ingest-lean")(ingest_lean)
    app.command()(search)
