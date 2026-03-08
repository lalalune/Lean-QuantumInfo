#!/usr/bin/env bash
set -euo pipefail

ROOT_DIR="$(cd "$(dirname "${BASH_SOURCE[0]}")/.." && pwd)"
cd "$ROOT_DIR"

EXCEPTIONS_FILE="tools/import_layer_exceptions.txt"
FAIL=0

layer_of() {
  case "$1" in
    Mathematics|Units) echo 1 ;;
    ClassicalInfo|ClassicalMechanics|Thermodynamics) echo 2 ;;
    Mechanics) echo 3 ;;
    SpaceAndTime) echo 4 ;;
    Electromagnetism|Optics) echo 5 ;;
    Relativity) echo 6 ;;
    QuantumMechanics) echo 7 ;;
    QuantumInfo) echo 8 ;;
    QEC|QFT) echo 9 ;;
    Particles) echo 10 ;;
    StatMech|Cosmology|CondensedMatter|StringTheory) echo 11 ;;
    Physics) echo 99 ;;
    Meta|Test) echo 100 ;;
    *) echo "" ;;
  esac
}

is_exception() {
  local file="$1"
  local import_root="$2"
  [[ -f "$EXCEPTIONS_FILE" ]] || return 1
  grep -Fxq "${file}|${import_root}" "$EXCEPTIONS_FILE"
}

owner_of_file() {
  local f="$1"
  if [[ "$f" == */* ]]; then
    echo "${f%%/*}"
  else
    basename "$f" .lean
  fi
}

while IFS= read -r line; do
  file="$(echo "$line" | cut -d: -f1)"
  rest="$(echo "$line" | cut -d: -f3-)"
  owner="$(owner_of_file "$file")"

  # Skip non-library and tooling trees.
  case "$owner" in
    .lake|scratch) continue ;;
  esac

  # Parse first imported root.
  imported="$(echo "$rest" | sed -E 's/^import[[:space:]]+([A-Za-z0-9_]+).*/\1/')"
  owner_layer="$(layer_of "$owner")"
  [[ -n "$owner_layer" ]] || continue

  # External imports (Mathlib, Lean, Std, etc.) are ignored.
  imported_layer="$(layer_of "$imported")"
  [[ -n "$imported_layer" ]] || continue

  # Tooling and integration umbrellas are exempt.
  [[ "$owner" == "Meta" || "$owner" == "Physics" || "$owner" == "Test" ]] && continue
  [[ "$imported" == "Meta" ]] && continue

  if is_exception "$file" "$imported"; then
    continue
  fi

  if (( imported_layer > owner_layer )); then
    echo "Layer violation: $file imports $imported (layer $owner_layer -> $imported_layer)"
    FAIL=1
  fi
done < <(rg -n '^import[[:space:]]+[A-Za-z0-9_.]+' . \
  --glob '*.lean' \
  --glob '!.lake/**' \
  --glob '!scratch/**')

if (( FAIL == 0 )); then
  echo "Import layer check: PASS"
  exit 0
fi

echo "Import layer check: FAIL"
exit 1
