#!/usr/bin/env bash
set -euo pipefail

ROOT_DIR="$(cd "$(dirname "$0")/.." && pwd)"
cd "$ROOT_DIR"

source "$HOME/.elan/env"

echo "[1/4] lake build"
lake build

echo "[2/4] check axioms"
if rg -n '^axiom ' Question8.lean Question8/Core.lean Question8/ExternalGromov.lean; then
  echo "FAIL: unexpected axiom declarations found"
  exit 1
fi

echo "[3/4] check sorry/admit"
if rg -n '^\s*(sorry|admit)\b' Question8.lean Question8/Core.lean Question8/ExternalGromov.lean; then
  echo "FAIL: sorry/admit found"
  exit 1
fi

echo "[4/4] run geometric sanity script"
python3 scripts/verify_octa_lagrangian.py

echo "PASS: build/sorry/axiom/geometry checks all passed"
