#!/usr/bin/env python3
"""V3 textual placeholder and ledger-marker scanner."""

from lean_source_scanner import scanner_main
from scanner_profiles import V3_PATTERNS


if __name__ == "__main__":
    raise SystemExit(scanner_main(profile="V3", patterns=V3_PATTERNS))

