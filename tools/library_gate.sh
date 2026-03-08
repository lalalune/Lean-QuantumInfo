#!/usr/bin/env bash
set -euo pipefail

ROOT_DIR="$(cd "$(dirname "${BASH_SOURCE[0]}")/.." && pwd)"
cd "$ROOT_DIR"

bash tools/foundation_audit.sh --skip-build
bash tools/check_import_layers.sh
bash tools/generate_theorem_index.sh docs/THEOREM_INDEX.md

echo "Library gate checks completed."
