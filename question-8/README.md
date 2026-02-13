# Constructive Counterexample for Question 8 (Lean 4)

This repository formalizes a **negative answer** to the following question:

> If a polyhedral Lagrangian surface \(K \subset \mathbb{R}^4\) has exactly 4 faces meeting at every vertex, must \(K\) admit a Lagrangian smoothing?

The formal result proves that the answer is **No** (under a standard external Gromov-type obstruction hypothesis).

## What this project solves

The project provides a machine-checked constructive counterexample pipeline:

- Explicit octahedron-like coordinates in standard symplectic \(\mathbb{R}^4\)
- Explicit face/edge/vertex combinatorics
- Verified local geometric properties (four faces per vertex, two faces per edge, nondegenerate faces)
- Verified vanishing symplectic area on all listed faces (`OctFacesAreLagrangian`)
- Formal contradiction architecture parameterized by
  `NoCompactLagrangianSphereInR4`

The Lean development is organized so the core file is axiom-free and external theory is passed as an explicit parameter.

## Repository layout

- `Question8.lean`: entry module importing the full development
- `Question8/Core.lean`: constructive core formalization
- `Question8/ExternalGromov.lean`: citation-facing theorems with explicit external parameter
- `scripts/verify_formal_status.sh`: one-shot verification (build + axiom/sorry scan + geometry checks)
- `scripts/verify_octa_lagrangian.py`: numeric/symbolic sanity check for face symplectic areas and vertex incidences
- `question-8.tex`: original problem statement
- `question-8-paper-proof.md`: paper-style proof narrative
- `question-8-submission.tex`: journal-style LaTeX manuscript
- `question-8-submission.pdf`: compiled manuscript
- `question-8-references.bib`: bibliography (Gromov reference)

## Requirements

- Lean 4 (configured by `lean-toolchain`, currently `v4.15.0`)
- Lake
- Python 3
- (Optional for paper build) `pdflatex`, `bibtex`

## How to run

1. Build Lean files:

```bash
source $HOME/.elan/env
lake build
```

2. Run full verification:

```bash
./scripts/verify_formal_status.sh
```

3. Run geometry check only:

```bash
python3 scripts/verify_octa_lagrangian.py
```

4. Build the paper PDF:

```bash
pdflatex -interaction=nonstopmode -halt-on-error question-8-submission.tex
bibtex question-8-submission
pdflatex -interaction=nonstopmode -halt-on-error question-8-submission.tex
pdflatex -interaction=nonstopmode -halt-on-error question-8-submission.tex
```

## AI-assisted solving process

This result was developed with an AI-assisted workflow:

1. Start from an abstract shell formalization.
2. Replace existence-style assumptions with explicit coordinates and combinatorics.
3. Add small lemmas for each local geometric property and verify each step with `lake build`.
4. Separate the architecture into a constructive core and an external-obstruction interface.
5. Add reproducibility scripts and manuscript artifacts.

In short, AI was used as a theorem-engineering assistant for decomposition, implementation, proof repair, and iterative verification.

## Code link

Lean 4 code repository:

- <https://github.com/amadeuzou/1stProof-lean4>
