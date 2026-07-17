"""Compatibility facade for the immutable proofread service."""

from ..application.services.proofread import *  # noqa: F403
from ..application.services.proofread import (
    _legacy_inventory_to_contract, _near_contract_inventory_to_contract,
)
