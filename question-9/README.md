# Question 9 (1stProof) — Lean 4 Formalization

This directory contains a Lean 4 / mathlib formalization of **`question-9.tex`** (1stProof): algebraic relations among multi-view tensors built from determinants of Zariski-generic camera matrices, and how these relations characterize when a scaling tensor is **separable** (rank-1 outer product).

## What Is Proved

The original question asks for a polynomial map on the **input tensor space** \(Y=\lambda\cdot Q(A)\) whose vanishing detects whether \(\lambda\) factorizes as \(u\otimes v\otimes w\otimes x\), with degree bounds independent of \(n\) and independent of the cameras \(A\).

This repo formalizes (and cleanly separates) three verified results:

1. **Intrinsic ground truth on \(\lambda\)** (uniform degree): a finite **quadratic** map on \(\lambda\) whose vanishing is equivalent to separability under the natural “nonzero on valid indices” condition.
   - Key theorem: `Question9.hConditionResidualFin_zero_iff_separable`.

2. **Camera-dependent characterization on inputs \(Y\)**: for fixed cameras \(A\) satisfying `IsGenericStrong`, a uniform-degree **polynomial** test on \(Y\) equivalent to separability of \(\lambda\) when \(Y=\lambda\cdot Q(A)\).
   - Key theorem: `Question9.cameraNormalizedHPolyFin_scaled_iff_separable_of_genericStrong`.

3. **Boundary/negative results at \(n=5\)** (conditional on existence of a generic-strong camera): a natural camera-independent degree-2 “swap-balance / Plücker residual” family is **not** sufficient, and also **not** necessary, to characterize separability.
   - Key theorems: `Question9.not_bridgeRecoverability5_of_genericStrong_exists`,
     `Question9.not_swapZeroForwardCompleteness5_of_genericStrong_exists`.

All theorems are checked by Lean with **no `sorry`**, and the main statements depend only on standard axioms (`propext`, `Classical.choice`, `Quot.sound`).

## Build / Check

Prerequisites:
- `elan` (Lean toolchain manager)
- A C toolchain suitable for building mathlib dependencies (standard on most Linux systems)

Commands:
```bash
cd question-9
source "$HOME/.elan/env"   # ensures `lean`/`lake` are on PATH
lake update                # fetch mathlib pinned in lake-manifest.json
lake build                 # build and check all proofs
```

Optional sanity checks:
```bash
rg -n "sorry|admit|axiom" Question9
```

## Project Layout

- `Question9/Defs.lean`: indices, `Lambda`, `valid`, `nonzeroOnValid`, `separable`, and anchors.
- `Question9/Geometry.lean`: concrete construction of \(Q\) via \(4\times4\) determinants and the input vector type.
- `Question9/Generic.lean`: algebraic “genericity” predicates (`IsGeneric`, `IsGenericStrong`) and polynomial evaluation helpers.
- `Question9/Plucker.lean`: Plücker-style quadratic residuals (`pluckerRel`, `pluckerMap`) and forward-vanishing lemmas.
- `Question9/PolynomialMap.lean`: a quartic “coordinate map” on \(\lambda\) (used in one characterization pipeline).
- `Question9/Characterization.lean`: core equivalence theorems connecting vanishing conditions to `separable`.
- `Question9/Bridge.lean`: bilinear identity families (`H1/H2/H3`) and their relation to separability.
- `Question9/HFamily.lean`: packages the `H1/H2/H3` identities as an explicit finite quadratic map on \(\lambda\).
- `Question9/NormalizedPolynomialFamily.lean`: removes divisions by cross-multiplication to obtain a camera-fixed polynomial test on inputs \(Y\).
- `Question9/Counterexample.lean`: explicit \(n=5\) counterexamples (Lean-checked).
- `Question9/Main.lean`: ties the layers together and provides “exists map” packaging statements.

Supporting docs:
- `question-9-lean4-en.md` / `question-9-lean4.md`: human-readable explanation (English/Chinese).
- `question-9-paper.tex` / `question-9-paper.pdf`: a paper-style write-up aligned to the Lean theorems.

## How It Was Built (AI-Assisted)

The formalization was developed with help from an AI coding agent (OpenAI Codex) in a tight compile-check loop:
1. Break the problem into small lemmas mirroring the math (definitions, residual families, equivalences).
2. Implement the lemmas in Lean 4 using mathlib, iterating with `lake build` until all proofs type-check.
3. Add explicit counterexamples and discharge finite arithmetic/index facts with `native_decide` and `norm_num`.

Even though AI assisted the implementation, correctness comes from Lean’s kernel: the final codebase contains no placeholders and is fully verified by the compiler.
