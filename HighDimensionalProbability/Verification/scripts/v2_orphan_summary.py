#!/usr/bin/env python3
"""Summarize the current V2 zero-orphan and MatrixConcentration coverage result."""

from __future__ import annotations

from import_graph import ROOT, audit_import_graph


def main() -> int:
    graph = audit_import_graph(expected_count=222)
    partition = graph["partition"]
    assert isinstance(partition, dict)
    raw_orphans = partition["orphan"]
    assert isinstance(raw_orphans, list)
    raw_root = partition["root_reachable"]
    assert isinstance(raw_root, list)
    mc_entries = [
        row
        for row in raw_root
        if isinstance(row, dict) and row["library"] == "MatrixConcentration"
    ]

    print("V2 ORPHAN CLASSIFICATION EVIDENCE")
    print("=================================")
    print(f"graph_status: {graph['status']}")
    print(f"partition_status: {partition['status']}")
    print(f"orphan_count: {len(raw_orphans)}")
    print(f"matrix_concentration_modules: {len(mc_entries)}")
    print(
        "matrix_concentration_all_glob_built: "
        f"{all(bool(row['glob_built']) for row in mc_entries)}"
    )
    print(
        "matrix_concentration_all_root_reachable: "
        f"{all(bool(row['root_reachable']) for row in mc_entries)}"
    )
    print("orphan_module\tpath")
    for row in raw_orphans:
        assert isinstance(row, dict)
        print(f"{row['module']}\t{row['path']}")
    ok = (
        graph["status"] == "PASS"
        and not raw_orphans
        and len(mc_entries) == 10
        and all(bool(row["glob_built"]) for row in mc_entries)
        and all(bool(row["root_reachable"]) for row in mc_entries)
    )
    print(f"v2_zero_orphan_gate: {str(ok).lower()}")
    return 0 if ok else 2


if __name__ == "__main__":
    raise SystemExit(main())
