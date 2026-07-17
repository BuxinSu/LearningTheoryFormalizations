"""Thin Typer interface over AutoFormal application services."""

import typer

from .commands import books, memory, operations, review, workflow

app = typer.Typer(
    no_args_is_help=True,
    help="Profile-driven, dependency-aware PDF-to-Lean workflow",
)
memory_app = typer.Typer(
    no_args_is_help=True,
    help="Global reusable theorem/reference memory",
)
app.add_typer(memory_app, name="memory")

books.register(app)
workflow.register(app)
operations.register(app)
review.register(app)
memory.register(memory_app)

__all__ = ["app", "memory_app"]
