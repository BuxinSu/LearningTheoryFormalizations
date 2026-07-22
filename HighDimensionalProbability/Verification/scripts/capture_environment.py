#!/usr/bin/env python3
"""Print the Step 0 environment, layout, pins, and file-universe counts."""

from __future__ import annotations

import datetime as dt
import json
import platform
import subprocess
from pathlib import Path

from file_universe import ROOT, enumerate_universe


def command_output(command: list[str]) -> tuple[int, str]:
    run = subprocess.run(
        command,
        cwd=ROOT,
        text=True,
        stdout=subprocess.PIPE,
        stderr=subprocess.STDOUT,
    )
    return run.returncode, run.stdout.rstrip()


def section(name: str, command: list[str]) -> list[str]:
    status, output = command_output(command)
    return [
        f"[{name}]",
        f"command: {' '.join(command)}",
        f"exit_code: {status}",
        output,
        "",
    ]


def main() -> int:
    expected_paths: dict[str, str] = {
        "project_root": ".",
        "hdp_source": "HighDimensionalProbability",
        "mc_real_source": "MatrixConcentration",
        "tmp": "tmp",
        "scripts": "scripts",
        "audit_work": ".audit_work",
        "verification": "HighDimensionalProbability/Verification",
        "hdp_root_module": "HighDimensionalProbability.lean",
        "root_readme": "README.md",
        "main_readme": "HighDimensionalProbability/README.md",
        "review_notes": "HighDimensionalProbability/Verification/REVIEW_NOTES.md",
        "final_correction_report": "HighDimensionalProbability/Verification/FINAL_CORRECTION_REPORT.md",
        "correction_ledger": "HighDimensionalProbability/Verification/CORRECTION_LEDGER.md",
        "faithful_report": "HighDimensionalProbability/Verification/archive/FAITHFUL_PROOFREAD_REPORT.md",
        "appendix_summary": "HighDimensionalProbability/APPENDIX_SUMMARY.md",
        "human_verification_log": "HighDimensionalProbability/HUMAN_VERIFICATION_LOG.md",
    }
    print("STEP 0 ENVIRONMENT AND LAYOUT")
    print("=============================")
    print(f"captured_local: {dt.datetime.now().astimezone().isoformat()}")
    print(f"captured_utc: {dt.datetime.now(dt.timezone.utc).isoformat()}")
    print(f"project_root: {ROOT}")
    print(f"platform: {platform.platform()}")
    print(f"machine: {platform.machine()}")
    print(f"processor: {platform.processor()}")
    print(f"python: {platform.python_version()}")
    print()

    layout_ok = True
    print("[layout]")
    for label, relative in expected_paths.items():
        path = ROOT / relative
        exists = path.exists()
        layout_ok = layout_ok and exists
        print(f"{label}: {relative} | exists={str(exists).lower()} | symlink={str(path.is_symlink()).lower()}")
    mc = ROOT / "MatrixConcentration"
    mc_modules = sorted(mc.glob("*.lean"))
    removed_paths = (
        ROOT / "Pre_MatrixConcentration",
        ROOT / "MatrixConcentration.lean",
    )
    mc_ok = mc.is_dir() and not mc.is_symlink() and len(mc_modules) == 10
    removed_ok = not any(path.exists() or path.is_symlink() for path in removed_paths)
    layout_ok = layout_ok and mc_ok and removed_ok
    print(f"mc_real_directory: {str(mc.is_dir() and not mc.is_symlink()).lower()}")
    print(f"mc_module_count: {len(mc_modules)}")
    print(f"pre_matrix_concentration_absent: {str(not removed_paths[0].exists()).lower()}")
    print(f"mc_root_module_absent: {str(not removed_paths[1].exists()).lower()}")
    print(f"layout_ok: {str(layout_ok).lower()}")
    print()

    lakefile = (ROOT / "lakefile.toml").read_text(encoding="utf-8")
    explicit_glob_lines = [
        line for line in lakefile.splitlines() if "glob" in line.lower() or "roots" in line.lower()
    ]
    print("[lakefile]")
    print("lean_lib_high_dimensional_probability: " + str('name = "HighDimensionalProbability"' in lakefile).lower())
    print("lean_lib_matrix_concentration: " + str('name = "MatrixConcentration"' in lakefile).lower())
    print(f"explicit_glob_or_roots_lines: {json.dumps(explicit_glob_lines)}")
    hdp_has_no_glob = lakefile.count('name = "HighDimensionalProbability"') == 2 and (
        'globs = ["HighDimensionalProbability.+' not in lakefile
    )
    mc_glob_ok = 'globs = ["MatrixConcentration.+"]' in lakefile
    layout_ok = layout_ok and hdp_has_no_glob and mc_glob_ok
    print(f"hdp_has_no_glob: {str(hdp_has_no_glob).lower()}")
    print(f"matrix_concentration_glob_exact: {str(mc_glob_ok).lower()}")
    print("verification_swept_by_explicit_glob: false")
    print()

    manifest = json.loads((ROOT / "lake-manifest.json").read_text(encoding="utf-8"))
    mathlib = next(package for package in manifest["packages"] if package["name"] == "mathlib")
    print("[pins]")
    print(f"lean_toolchain: {(ROOT / 'lean-toolchain').read_text(encoding='utf-8').strip()}")
    print(f"mathlib_rev: {mathlib['rev']}")
    print(f"mathlib_inputRev: {mathlib['inputRev']}")
    print()

    for line in section("lake_version", [str(Path.home() / ".elan/bin/lake"), "--version"]):
        print(line)
    for line in section("lean_version", [str(Path.home() / ".elan/bin/lean"), "--version"]):
        print(line)
    for line in section("elan_show", [str(Path.home() / ".elan/bin/elan"), "show"]):
        print(line)
    for name, command in (
        ("sw_vers", ["/usr/bin/sw_vers"]),
        ("uname", ["/usr/bin/uname", "-a"]),
    ):
        for line in section(name, command):
            print(line)
    hardware_command = ["/usr/sbin/system_profiler", "SPHardwareDataType"]
    hardware_status, hardware_output = command_output(hardware_command)
    permitted_hardware_fields = (
        "Model Name:",
        "Model Identifier:",
        "Chip:",
        "Total Number of Cores:",
        "Memory:",
    )
    filtered_hardware = [
        line.strip()
        for line in hardware_output.splitlines()
        if line.strip().startswith(permitted_hardware_fields)
    ]
    print("[hardware]")
    print(f"command: {' '.join(hardware_command)}")
    print("filter: model name, model identifier, chip, core count, memory; serial and UUID omitted")
    print(f"exit_code: {hardware_status}")
    print("\n".join(filtered_hardware))
    print()

    universe = enumerate_universe()
    print("[file_universe_counts]")
    counts = universe["counts"]
    assert isinstance(counts, dict)
    for key, value in counts.items():
        print(f"{key}: {value}")
    return 0 if layout_ok else 1


if __name__ == "__main__":
    raise SystemExit(main())
