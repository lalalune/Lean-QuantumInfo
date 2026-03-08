#!/usr/bin/env bash
set -euo pipefail

ROOT_DIR="$(cd "$(dirname "${BASH_SOURCE[0]}")/.." && pwd)"
cd "$ROOT_DIR"

SKIP_BUILD=0
if [[ "${1:-}" == "--skip-build" ]]; then
  SKIP_BUILD=1
fi

FAIL=0
SKIP_FILE="tools/foundation_skip_paths.txt"

print_header() {
  printf '\n== %s ==\n' "$1"
}

read_skip_globs() {
  local -a globs=()
  if [[ -f "$SKIP_FILE" ]]; then
    while IFS= read -r line; do
      line="$(echo "$line" | sed 's/[[:space:]]*$//')"
      [[ -z "$line" ]] && continue
      [[ "$line" =~ ^# ]] && continue
      globs+=(--glob "!${line}")
    done < "$SKIP_FILE"
  fi
  echo "${globs[*]-}"
}

run_check() {
  local name="$1"
  local pattern="$2"
  shift 2
  local -a extra_args=("$@")
  local skip_raw
  skip_raw="$(read_skip_globs)"
  local -a cmd=(rg -n --glob '*.lean' "${extra_args[@]}")
  if [[ -n "$skip_raw" ]]; then
    local -a skip_globs=()
    # shellcheck disable=SC2206
    skip_globs=($skip_raw)
    cmd+=("${skip_globs[@]}")
  fi
  cmd+=("$pattern" .)
  local out
  out="$("${cmd[@]}" || true)"
  if [[ -n "$out" ]]; then
    echo "FAIL: ${name}"
    echo "$out"
    FAIL=1
  else
    echo "PASS: ${name}"
  fi
}

if [[ "$SKIP_BUILD" -eq 0 ]]; then
  print_header "Build"
  if lake build; then
    echo "PASS: lake build"
  else
    echo "FAIL: lake build"
    FAIL=1
  fi
else
  print_header "Build"
  echo "SKIP: lake build (--skip-build)"
fi

print_header "Static Placeholder Gates"

# Exclude Meta tooling files because they intentionally reference sorry/axiom internals.
EXCLUDE_META=(--glob '!Meta/**')

print_header "Skip Globs"
if [[ -f "$SKIP_FILE" ]]; then
  grep -v '^\s*#' "$SKIP_FILE" | sed '/^\s*$/d' || true
else
  echo "(none)"
fi

run_check "No sorry tactics" '(:=\s*by\s*sorry\b)|(\bby\s*sorry\b)|(^\s*sorry\b)' "${EXCLUDE_META[@]}"
run_check "No axiom-like declarations" '^\s*(private\s+)?(axiom|constant|postulate|opaque)\s+[A-Za-z_][A-Za-z0-9_]*\s*[:(]' "${EXCLUDE_META[@]}"
run_check "No theorem/lemma True:=trivial stubs" 'True\s*:=\s*by\s*trivial\b' "${EXCLUDE_META[@]}"
run_check "No Prop:=True structural stubs" ':\s*Prop\s*:=\s*True\b' "${EXCLUDE_META[@]}"

print_header "Result"
if [[ "$FAIL" -eq 0 ]]; then
  echo "FOUNDATION AUDIT: PASS"
  exit 0
fi

echo "FOUNDATION AUDIT: FAIL"
exit 1
