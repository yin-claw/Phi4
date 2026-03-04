#!/usr/bin/env bash
set -euo pipefail

ROOT_DIR="$(cd "$(dirname "${BASH_SOURCE[0]}")/.." && pwd)"
cd "$ROOT_DIR"

MAX_SCRATCH_LEAN_FILES=60
MAX_CHECK_FILES=0

scratch_count="$(find Phi4/Scratch -type f -name '*.lean' | wc -l | tr -d ' ')"
check_count="$(find Phi4/Scratch -type f -name 'Check*.lean' | wc -l | tr -d ' ')"

echo "[scratch_guard] Scratch .lean files: $scratch_count (max $MAX_SCRATCH_LEAN_FILES)"
echo "[scratch_guard] Scratch Check*.lean files: $check_count (max $MAX_CHECK_FILES)"

fail=0
if (( scratch_count > MAX_SCRATCH_LEAN_FILES )); then
  echo "[FAIL] Scratch .lean file count exceeds cap." >&2
  fail=1
fi

if (( check_count > MAX_CHECK_FILES )); then
  echo "[FAIL] Scratch Check*.lean file count exceeds cap." >&2
  fail=1
fi

if (( fail != 0 )); then
  exit 1
fi

echo "[scratch_guard] OK"
