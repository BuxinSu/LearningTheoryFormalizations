#!/usr/bin/env python3
"""V5 escape-hatch and trust-surface scanner."""

from lean_source_scanner import scanner_main
from scanner_profiles import V5_PATTERNS


if __name__ == "__main__":
    raise SystemExit(scanner_main(profile="V5", patterns=V5_PATTERNS))

