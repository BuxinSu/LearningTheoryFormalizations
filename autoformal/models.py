"""Compatibility exports for the split domain model package.

New code should import from ``autoformal.domain`` or its bounded modules.
Existing callers may continue importing the same names from this module during
migration.
"""

from .domain import *  # noqa: F403
from .domain import __all__
