"""Composition of the shared verification service with concrete Lean adapters."""

from ..application.verification import VerificationService
from .lean.axioms import print_axioms
from .lean.build import lake_build
from .lean.placeholders import (
    scan_placeholders,
    scan_theorem_shaped_propositions,
    unregistered_placeholders,
    unregistered_proposition_specifications,
)


def verification_service() -> VerificationService:
    return VerificationService(
        build=lake_build,
        scan_placeholders=scan_placeholders,
        unregistered_placeholders=unregistered_placeholders,
        scan_propositions=scan_theorem_shaped_propositions,
        unregistered_propositions=unregistered_proposition_specifications,
        print_axioms=print_axioms,
    )
