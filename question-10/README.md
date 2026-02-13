# Formalizing Question 10 in Lean 4

## What this repository solves
This project formalizes the mode-\(k\) RKHS-constrained CP subproblem with missing tensor entries, based on `question-10.tex`.  
The target equation is the \(nr \times nr\) linear system
\[
\big[(Z \otimes K)^TSS^T(Z \otimes K)+\lambda(I_r\otimes K)\big]\operatorname{vec}(W)
=(I_r\otimes K)\operatorname{vec}(B),
\]
and the repository proves (in Lean 4) an operator-based PCG framework, SPD-based admissibility conditions, and explicit complexity bounds that avoid \(O(N)\) ambient-tensor computation.

## How to run
Prerequisites:
- Lean toolchain: `leanprover/lean4:v4.15.0` (from `lean-toolchain`)
- Lake + mathlib (resolved by `lake update`)

Build and verify:
```bash
source "$HOME/.elan/env"
lean --version
lake update
lake build
rg -n "sorry|admit" Question10 *.lean
rg -n "axiom" Question10 *.lean
```

Expected result:
- `lake build` succeeds
- `rg` finds no `sorry`/`admit`
- `rg` finds no custom `axiom` declarations

## Current formal status
- Fully mechanized in Lean:
  - operator/SPD/cost chain
  - Section-4 spectral bridge chain
  - Section-5 logarithmic-to-geometric step:
    `geometric_term_le_eps_of_kEps`
  - direct budgeted error theorem:
    `error_bound_at_kEps`
- Still provided as an input assumption:
  - the standard PCG contraction premise (`hContract`)

## Code structure and files
- `Question10/Defs.lean`: core data model, observation indexing, and system operator definitions.
- `Question10/SparseMatVec.lean`: observation-driven matvec and matvec cost theorems.
- `Question10/PCG.lean`: Frobenius-inner-product framework, SPD lemmas, and PCG admissibility theorems.
- `Question10/Complexity.lean`: per-iteration/total cost formulas and Big-O-style abstractions.
- `Question10/Main.lean`: bundled top-level theorem statements.
- `question-10-lean4.md`: Chinese explanation mapping math to Lean.
- `question-10-lean4-en.md`: English explanation mapping math to Lean.
- `question-10-paper.tex` / `question-10-paper.pdf`: paper-style writeup and compiled PDF.
- `question-10.tex`: original problem statement.

## AI-assisted solution process
The solution was developed with an AI coding/proof assistant in an iterative loop:
1. Parse the mathematical problem and define Lean data structures and operators.
2. Decompose the goal into small lemmas (matvec, SPD, preconditioner, complexity).
3. Implement each lemma in Lean, run `lake build`, and fix type/proof errors.
4. Eliminate all placeholders (`sorry`) and re-check full compilation.
5. Produce bilingual proof notes and a paper-form LaTeX/PDF narrative.

## Rebuild the paper PDF
```bash
pdflatex -interaction=nonstopmode -halt-on-error question-10-paper.tex
pdflatex -interaction=nonstopmode -halt-on-error question-10-paper.tex
```
