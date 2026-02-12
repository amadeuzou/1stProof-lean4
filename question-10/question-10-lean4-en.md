# Lean4 Formalization Notes for Question 10 (English)

## Goal and Modeling
This formalization encodes the mode-\(k\) subproblem from `question-10.tex` into Lean:
- `Question10/Defs.lean`: `ProblemData` with dimensions `n,r,M,q`, kernel matrix `K`, factor-side matrix `Z`, observation index map `obs`, and regularization `lambda`.
- `systemOp`: system operator \(A(W)=\text{dataTerm}(W)+\lambda K W\).
- `rhs`: right-hand side \(K B\).

The key point is that `dataTerm` sums over `Fin q` only, so matrix-vector products are driven by observed entries (not by ambient size \(N=nM\)).

## PCG and Preconditioner
`Question10/PCG.lean` introduces:
- Frobenius inner product `frobInner`
- `Symmetric`, `PosDef`, and `SPD` predicates
- preconditioner matrix `preconditionerMatrix mu = K + mu * I`
- `preconditionerApply` (columnwise left multiplication, matching the block form \(I_r \otimes (K+\mu I)\))

Strengthened proof chain:
- `spd_systemOp_of_assumptions`: from symmetry + semidefiniteness of `dataTerm` and symmetry + definiteness of `kMul`, derive `SPD systemOp`.
- `spd_preconditioner_of_kernel_assumptions`: from kernel-side assumptions (and `lambda > 0`), derive SPD of the default preconditioner (`mu = lambda`).
- `pcg_ready_fully_structured`: deduces PCG admissibility directly from those structured assumptions, without an extra standalone SPD assumption for the preconditioner.

## Complexity System
`Question10/SparseMatVec.lean` and `Question10/Complexity.lean` provide:
- explicit per-matvec cost (`costSystemMatVec`)
- per-PCG-iteration cost (`costPCGIter`)
- total cost after `iters` iterations (`totalCost`)
- a discrete Big-O predicate (`IsBigONat`) and associated lemmas
- a strict comparison theorem (`costSystemMatVec_lt_ambient_scaled`) showing improvement when `q < n*M`

`main_solver_statement` in `Question10/Main.lean` bundles solver admissibility and cost identities.

## Validation
```bash
source "$HOME/.elan/env"
lake update
lake build
rg -n "sorry" Question10 *.lean
```
