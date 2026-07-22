#!/usr/bin/env python3
"""Positive calibrations for the V2 Lean import-graph scanner."""

from __future__ import annotations

from import_graph import (
    ROOT,
    module_to_expected_path,
    parse_imports,
    strongly_connected_components,
    transitive_closure,
)


def require(condition: bool, message: str) -> None:
    if not condition:
        raise AssertionError(message)
    print(f"PASS\t{message}")


def main() -> int:
    plant = ".audit_work/verification/import_graph_positive.lean"
    imports = parse_imports(plant)
    require(
        [item.module for item in imports]
        == ["HighDimensionalProbability.DoesNotExistForV2Calibration"],
        "parser finds the planted live import and ignores comment/string decoys",
    )
    expected = module_to_expected_path(imports[0].module)
    require(
        expected
        == "HighDimensionalProbability/DoesNotExistForV2Calibration.lean",
        "local HDP import resolves to its expected physical path",
    )
    require(
        expected is not None and not (ROOT / expected).exists(),
        "planted local import is positively recognized as unresolved",
    )
    require(
        module_to_expected_path("MatrixConcentration.Appendix_MatrixRosenthal")
        == "MatrixConcentration/Appendix_MatrixRosenthal.lean",
        "MatrixConcentration modules resolve through the real project-root directory",
    )

    graph = {
        "root": {"a"},
        "a": {"b"},
        "b": {"a"},
        "isolated": set(),
    }
    require(
        transitive_closure(["root"], graph) == {"root", "a", "b"},
        "transitive reachability includes the planted reachable component only",
    )
    require(
        strongly_connected_components(graph) == [["a", "b"]],
        "cycle detector finds the planted two-node cycle",
    )
    print("calibrations: 6/6 PASS")
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
