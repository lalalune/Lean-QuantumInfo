#!/usr/bin/env bash
set -euo pipefail

ROOT_DIR="$(cd "$(dirname "${BASH_SOURCE[0]}")/.." && pwd)"
cd "$ROOT_DIR"

OUT_FILE="${1:-docs/FOUNDATION_BACKLOG.md}"
SKIP_FILE="tools/foundation_skip_paths.txt"
TMP_DIR="$(mktemp -d)"
trap 'rm -rf "$TMP_DIR"' EXIT

SORRY_RAW="$TMP_DIR/sorry.txt"
AXIOM_RAW="$TMP_DIR/axiom.txt"
TRUE_STUB_RAW="$TMP_DIR/true_stub.txt"
PROP_TRUE_RAW="$TMP_DIR/prop_true.txt"

SKIP_GLOBS=()
if [[ -f "$SKIP_FILE" ]]; then
  while IFS= read -r line; do
    line="$(echo "$line" | sed 's/[[:space:]]*$//')"
    [[ -z "$line" ]] && continue
    [[ "$line" =~ ^# ]] && continue
    SKIP_GLOBS+=(--glob "!${line}")
  done < "$SKIP_FILE"
fi

RG_GLOB_ARGS=(--glob '*.lean' --glob '!Meta/**')
if [[ ${#SKIP_GLOBS[@]} -gt 0 ]]; then
  RG_GLOB_ARGS+=("${SKIP_GLOBS[@]}")
fi

rg -n "${RG_GLOB_ARGS[@]}" '(:=\s*by\s*sorry\b)|(\bby\s*sorry\b)|(^\s*sorry\b)' . > "$SORRY_RAW" || true
rg -n "${RG_GLOB_ARGS[@]}" '^\s*(private\s+)?axiom\b' . > "$AXIOM_RAW" || true
rg -n "${RG_GLOB_ARGS[@]}" 'True\s*:=\s*by\s*trivial\b' . > "$TRUE_STUB_RAW" || true
rg -n "${RG_GLOB_ARGS[@]}" ':\s*Prop\s*:=\s*True\b' . > "$PROP_TRUE_RAW" || true

count_lines() {
  local file="$1"
  if [[ -s "$file" ]]; then
    wc -l < "$file" | tr -d ' '
  else
    echo 0
  fi
}

summarize_by_file() {
  local file="$1"
  if [[ ! -s "$file" ]]; then
    echo "_None_"
    return
  fi
  awk -F: '{print $1}' "$file" | sort | uniq -c | sort -nr | head -40
}

SORRY_COUNT="$(count_lines "$SORRY_RAW")"
AXIOM_COUNT="$(count_lines "$AXIOM_RAW")"
TRUE_STUB_COUNT="$(count_lines "$TRUE_STUB_RAW")"
PROP_TRUE_COUNT="$(count_lines "$PROP_TRUE_RAW")"

mkdir -p "$(dirname "$OUT_FILE")"

{
  echo "# Foundation Backlog"
  echo
  echo "Generated on: $(date -u '+%Y-%m-%d %H:%M:%SZ')"
  echo
  echo "## Summary"
  echo
  echo "- sorry tactics: **$SORRY_COUNT**"
  echo "- axiom declarations: **$AXIOM_COUNT**"
  echo "- True := by trivial stubs: **$TRUE_STUB_COUNT**"
  echo "- Prop := True stubs: **$PROP_TRUE_COUNT**"
  echo
  echo "## Skip Globs"
  echo
  if [[ -f "$SKIP_FILE" ]]; then
    if grep -qv '^\s*#' "$SKIP_FILE"; then
      grep -v '^\s*#' "$SKIP_FILE" | sed '/^\s*$/d'
    else
      echo "_None_"
    fi
  else
    echo "_None_"
  fi
  echo
  echo "## Top Files: sorry"
  echo
  summarize_by_file "$SORRY_RAW"
  echo
  echo "## Top Files: axiom"
  echo
  summarize_by_file "$AXIOM_RAW"
  echo
  echo "## Top Files: True := by trivial"
  echo
  summarize_by_file "$TRUE_STUB_RAW"
  echo
  echo "## Top Files: Prop := True"
  echo
  summarize_by_file "$PROP_TRUE_RAW"
  echo
  echo "## Raw Extracts"
  echo
  echo "### sorry"
  echo
  if [[ -s "$SORRY_RAW" ]]; then
    sed -n '1,200p' "$SORRY_RAW"
  else
    echo "_None_"
  fi
  echo
  echo "### axiom"
  echo
  if [[ -s "$AXIOM_RAW" ]]; then
    sed -n '1,200p' "$AXIOM_RAW"
  else
    echo "_None_"
  fi
  echo
  echo "### True := by trivial"
  echo
  if [[ -s "$TRUE_STUB_RAW" ]]; then
    sed -n '1,200p' "$TRUE_STUB_RAW"
  else
    echo "_None_"
  fi
  echo
  echo "### Prop := True"
  echo
  if [[ -s "$PROP_TRUE_RAW" ]]; then
    sed -n '1,200p' "$PROP_TRUE_RAW"
  else
    echo "_None_"
  fi
} > "$OUT_FILE"

echo "Wrote $OUT_FILE"
