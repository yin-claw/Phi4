#!/usr/bin/env bash
set -euo pipefail

ROOT_DIR="$(cd "$(dirname "${BASH_SOURCE[0]}")/.." && pwd)"
cd "$ROOT_DIR"

emit_path=""
if [[ "${1:-}" == "--emit" ]]; then
  if [[ -z "${2:-}" ]]; then
    echo "[frontier_report] --emit requires a path" >&2
    exit 1
  fi
  emit_path="$2"
fi

TMP_DIR="$(mktemp -d "${TMPDIR:-/tmp}/phi4_frontier.XXXXXX")"
trap 'rm -rf "$TMP_DIR"' EXIT

GAPS_FILE="$TMP_DIR/gaps.txt"
MODELS_FILE="$TMP_DIR/models.txt"
NONEMPTY_FILE="$TMP_DIR/nonempty.txt"
SORRY_FILE="$TMP_DIR/sorry.txt"

rg -n '^theorem[[:space:]]+gap_' Phi4 --glob '*.lean' | rg -v '/Scratch/' > "$GAPS_FILE" || true
rg -n '^class[[:space:]].*Model' Phi4 --glob '*.lean' | rg -v '/Scratch/' > "$MODELS_FILE" || true
rg -n '^theorem[[:space:]]+.*_nonempty_of_' Phi4 --glob '*.lean' | rg -v '/Scratch/' > "$NONEMPTY_FILE" || true
grep -RIn '^[[:space:]]*sorry\b' Phi4 --include='*.lean' | rg -v '/Scratch/' > "$SORRY_FILE" || true

gap_count="$(wc -l < "$GAPS_FILE" | tr -d ' ')"
model_count="$(wc -l < "$MODELS_FILE" | tr -d ' ')"
nonempty_count="$(wc -l < "$NONEMPTY_FILE" | tr -d ' ')"
core_sorry_count="$(wc -l < "$SORRY_FILE" | tr -d ' ')"

echo "[frontier_report] core theorem-level sorry count: $core_sorry_count"
echo "[frontier_report] core gap theorem count: $gap_count"
echo "[frontier_report] core class .*Model count: $model_count"
echo "[frontier_report] core theorem .*_nonempty_of_ count: $nonempty_count"
echo "[frontier_report] canonical gap theorems:"
if [[ "$gap_count" -eq 0 ]]; then
  echo "  (none)"
else
  sed 's/^/  /' "$GAPS_FILE"
fi

if [[ -n "$emit_path" ]]; then
  mkdir -p "$(dirname "$emit_path")"
  {
    echo -e "kind\tname\tfile\tline"
    sed -E "s|^([^:]+):([0-9]+):theorem[[:space:]]+([^ (]+).*$|gap_theorem\t\\3\t\\1\t\\2|" "$GAPS_FILE"
    sed -E "s|^([^:]+):([0-9]+):class[[:space:]]+([^ (]+).*$|model_class\t\\3\t\\1\t\\2|" "$MODELS_FILE"
    sed -E "s|^([^:]+):([0-9]+):theorem[[:space:]]+([^ (]+).*$|nonempty_constructor\t\\3\t\\1\t\\2|" "$NONEMPTY_FILE"
  } > "$emit_path"
  echo "[frontier_report] wrote machine-readable report: $emit_path"
fi
