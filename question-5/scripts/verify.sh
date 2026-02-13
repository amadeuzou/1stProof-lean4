#!/usr/bin/env bash
set -euo pipefail

ROOT_DIR="$(cd -- "$(dirname -- "${BASH_SOURCE[0]}")/.." && pwd)"
cd "$ROOT_DIR"

echo "[1/5] Building project"
lake build

echo "[2/5] Checking unfinished proofs (sorry)"
if rg -n '\bsorry\b' --glob '*.lean'; then
  echo "Found 'sorry' in Lean sources."
  exit 1
fi

echo "[3/5] Checking custom axiom declarations"
if rg -n '^\s*axiom\b' --glob '*.lean'; then
  echo "Found custom 'axiom' declaration in Lean sources."
  exit 1
fi

echo "[4/5] Checking paper-layer theorem interface surface"
if rg -n 'MainFixedPointClosureAxioms|MainReconstructionAxiom|MainSyntaxReconstructionAxiom' \
  Equivariant/Paper/MainTheorem.lean; then
  echo "Paper theorem surface leaks low-level closure/reconstruction assumptions."
  exit 1
fi

echo "[5/5] Printing axioms of key theorems"
TMP_FILE="$(mktemp "${TMPDIR:-/tmp}/q5-axioms-XXXXXX.lean")"
cat > "$TMP_FILE" <<'EOF'
import Question5
import Equivariant

#print axioms Question5.oSliceConnectivity_iff_geometricFixedPoints
#print axioms Equivariant.Paper.sliceConnectivity_iff_geometricFixedPoints
#print axioms Equivariant.Paper.toy_sliceConnectivity_iff_geometricFixedPoints
EOF

lake env lean "$TMP_FILE"
rm -f "$TMP_FILE"

echo "Verification passed."
