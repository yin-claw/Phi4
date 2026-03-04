#!/usr/bin/env bash
set -euo pipefail

ROOT_DIR="$(cd "$(dirname "${BASH_SOURCE[0]}")/.." && pwd)"
cd "$ROOT_DIR"

emit_path=""
if [[ "${1:-}" == "--emit" ]]; then
  if [[ -z "${2:-}" ]]; then
    echo "[upstream_sorry_report] --emit requires a path" >&2
    exit 1
  fi
  emit_path="$2"
fi

os_pkg=".lake/packages/OSReconstruction"
if [[ ! -d "$os_pkg" ]]; then
  echo "[upstream_sorry_report] OSReconstruction package not found at $os_pkg" >&2
  exit 1
fi

if command -v jq >/dev/null 2>&1; then
  os_rev="$(jq -r '.packages[] | select(.name=="OSReconstruction") | .rev' lake-manifest.json)"
else
  os_rev="$(awk '
    /"name": "OSReconstruction"/ { capture = 1 }
    capture && /"rev":/ {
      gsub(/.*"rev": "/, "", $0)
      gsub(/".*/, "", $0)
      print $0
      exit
    }
  ' lake-manifest.json)"
fi

if [[ -z "$os_rev" ]]; then
  os_rev="unknown"
fi

TMP_DIR="$(mktemp -d "${TMPDIR:-/tmp}/phi4_upstream_sorry.XXXXXX")"
trap 'rm -rf "$TMP_DIR"' EXIT

SORRY_FILE="$TMP_DIR/os_sorry.txt"
grep -RIn '^[[:space:]]*sorry([[:space:]]|$)' "$os_pkg/OSReconstruction" --include='*.lean' > "$SORRY_FILE" || true
sorry_count="$(wc -l < "$SORRY_FILE" | tr -d ' ')"

AXIOMS_IN="$TMP_DIR/os_axioms_check.lean"
AXIOMS_OUT="$TMP_DIR/os_axioms_out.txt"
cat > "$AXIOMS_IN" <<'EOF'
import OSReconstruction.Wightman.Reconstruction.WickRotation.OSToWightman
#print axioms os_to_wightman_full
EOF

upstream_sorryax_status="unknown"
if lake env lean "$AXIOMS_IN" > "$AXIOMS_OUT" 2>&1; then
  if rg -n 'sorryAx' "$AXIOMS_OUT" >/dev/null 2>&1; then
    upstream_sorryax_status="present"
  else
    upstream_sorryax_status="absent"
  fi
else
  upstream_sorryax_status="check_failed"
fi

echo "[upstream_sorry_report] OSReconstruction rev: $os_rev"
echo "[upstream_sorry_report] textual theorem-level sorry count: $sorry_count"
echo "[upstream_sorry_report] os_to_wightman_full sorryAx status: $upstream_sorryax_status"
if [[ "$sorry_count" -gt 0 ]]; then
  echo "[upstream_sorry_report] top sorry locations:"
  sed -n '1,30p' "$SORRY_FILE" | sed 's/^/  /'
fi

if [[ -n "$emit_path" ]]; then
  mkdir -p "$(dirname "$emit_path")"
  {
    echo "osreconstruction_rev=$os_rev"
    echo "textual_theorem_level_sorry_count=$sorry_count"
    echo "os_to_wightman_full_sorryax_status=$upstream_sorryax_status"
    if [[ "$sorry_count" -gt 0 ]]; then
      echo "sample_locations:"
      sed -n '1,30p' "$SORRY_FILE"
    fi
    if [[ -f "$AXIOMS_OUT" ]]; then
      echo "axiom_report_sample:"
      sed -n '1,20p' "$AXIOMS_OUT"
    fi
  } > "$emit_path"
  echo "[upstream_sorry_report] wrote report: $emit_path"
fi
