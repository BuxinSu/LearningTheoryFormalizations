#!/usr/bin/env bash
set -euo pipefail

SCRIPT_DIR="$(cd "$(dirname "${BASH_SOURCE[0]}")" && pwd)"
VERIFY_DIR="$(cd "${SCRIPT_DIR}/.." && pwd)"
ROOT="$(cd "${VERIFY_DIR}/../.." && pwd)"
LOG="${VERIFY_DIR}/logs/environment.txt"
PARENT="$(cd "${ROOT}/.." && pwd)"
HDP="${PARENT}/HighDimensionalProbability"

cd "${ROOT}"

if [[ ! -d .git || ! -f lakefile.toml || ! -f MatrixConcentration.lean ]]; then
  echo "ERROR: not the canonical MatrixConcentration project root" >&2
  exit 1
fi

source_count="$(
  find MatrixConcentration -maxdepth 1 -type f -name '*.lean' -print | wc -l | tr -d ' '
)"
if [[ "${source_count}" != "14" ]]; then
  echo "ERROR: expected 14 flat source modules, found ${source_count}" >&2
  exit 1
fi

{
  echo "Mechanical soundness verification environment"
  echo "Captured local: $(date '+%Y-%m-%d %H:%M:%S %Z')"
  echo "Captured UTC: $(date -u '+%Y-%m-%dT%H:%M:%SZ')"
  echo "Canonical project root: ${ROOT}"
  echo "Physical project root: $(pwd -P)"
  echo
  echo "[Toolchain]"
  "${HOME}/.elan/bin/lake" --version
  "${HOME}/.elan/bin/elan" show
  echo "lean-toolchain: $(tr -d '\n' < lean-toolchain)"
  "${HOME}/.elan/bin/lake" env lean --version
  echo
  echo "[Pinned dependency record]"
  rg -n '"name": "mathlib"|"inputRev":|"rev":' lake-manifest.json
  echo
  echo "[Host]"
  uname -a
  if command -v sw_vers >/dev/null 2>&1; then
    sw_vers
  fi
  if command -v system_profiler >/dev/null 2>&1; then
    system_profiler SPHardwareDataType |
      sed -E '/Serial Number|Hardware UUID|Provisioning UDID/d'
  fi
  echo
  echo "[Canonical layout]"
  echo "Flat source .lean count: ${source_count}"
  find MatrixConcentration -maxdepth 1 -type f -name '*.lean' -print | sort
  echo "Root module: MatrixConcentration.lean"
  echo "Claims documents:"
  ls -l MatrixConcentration/README.md MatrixConcentration/APPENDIX_SUMMARY.md
  echo "Project-root README:"
  ls -l README.md
  echo "TranslationReport content-file count:"
  find "${PARENT}/TranslationReport" -maxdepth 1 -type f ! -name 'Icon*' -print |
    wc -l | tr -d ' '
  echo
  echo "[File-walk universe]"
  find . \
    -path './.lake' -prune -o \
    -path './MatrixConcentration/Verification' -prune -o \
    -path './.audit_work' -prune -o \
    -type f -name '*.lean' -print | sort
  echo "Universe file count:"
  find . \
    -path './.lake' -prune -o \
    -path './MatrixConcentration/Verification' -prune -o \
    -path './.audit_work' -prune -o \
    -type f -name '*.lean' -print | wc -l | tr -d ' '
  echo "In-universe symlinks:"
  find . \
    -path './.lake' -prune -o \
    -path './MatrixConcentration/Verification' -prune -o \
    -path './.audit_work' -prune -o \
    -type l -print | sort
  echo
  echo "[Lake library declaration]"
  sed -n '1,220p' lakefile.toml
  echo
  echo "[Stale parent scaffold: excluded]"
  ls -l "${PARENT}/lakefile.toml" "${PARENT}/lean-toolchain" \
    "${PARENT}/lake-manifest.json" "${PARENT}/MatrixConcentration.lean"
  sed -n '1,30p' "${PARENT}/MatrixConcentration.lean"
  echo
  echo "[Stale sibling copies: excluded]"
  if [[ -d "${HDP}" ]]; then
    find "${HDP}" -maxdepth 2 \
      \( -path '*/MatrixConcentration' -o \
         -path '*/Pre_MatrixConcentration' -o \
         -name 'MatrixConcentration.lean' \) -print | sort
  else
    echo "HDP sibling not present"
  fi
} > "${LOG}" 2>&1

echo "WROTE ${LOG}"
