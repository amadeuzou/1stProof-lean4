# Question 10 Expanded Paper Notes (v2, English)

## Adopted New Title
`Certified Efficient Algorithms for Tensor Completion: A Formally Verified PCG Approach with Explicit Complexity Bounds`

Main manuscript file: `question-10-paper.tex`.

## What v2 adds beyond v1
Compared with the original draft (mostly verified numerical-algebra analysis), v2 adds four standard research-paper layers:

1. Condition-number analysis with explicit dependence on `λ` and observation density `ρ=q/N`.
2. Convergence-to-accuracy theory: explicit iteration bound `k_ε` for target error `ε`.
3. Theoretical positioning against ALS/SGD, plus transfer discussion for Tucker/TT.
4. A dedicated formalization-methodology section and a reproducible (non-formal) numerical protocol.

## 1. Lean-formalized core (unchanged, machine-checked)
These statements remain fully formalized in Lean 4:

- Operator model and observation indexing in `Question10/Defs.lean`
  - `systemOp`, `dataTerm`, `sampleScore`
  - `obs : Fin q → Fin n × Fin M`
- Matvec complexity in `Question10/SparseMatVec.lean`
  - `costSystemMatVec_eq`
  - strict sparsity advantage: `costSystemMatVec_lt_ambient_scaled` when `q < n*M`
- SPD/PCG admissibility in `Question10/PCG.lean`
  - `spd_systemOp_of_assumptions`
  - `spd_preconditioner_of_kernel_assumptions`
  - `pcg_ready_fully_structured`
- Per-iteration and total cost in `Question10/Complexity.lean`
  - `costPCGIter_eq`
  - `totalCost_eq`
- v2 extension scaffold in `Question10/SpectralConvergence.lean`
  - `SpectralAssumptions` (structured packaging of Section-4 hypotheses)
  - `observationDensity`
  - `kappaUpperFromCount` / `kappaUpperFromDensity`
  - `kappaUpperFromDensity_eq_count` (algebraic equivalence of density/count forms)
  - `kappaFromExtremes_le_kappaUpperFromCount` / `...Density`
  - `SpectralAssumptions.eigen_sandwich`
  - `SpectralAssumptions.kappa_bound_count` / `..._density`
  - `gramMatrix_posSemidef` (`F^T F` is PSD)
  - `regularizedNormalMatrix_posDef` (positivity chain for `F^T F + λR`)
  - `regularizedNormalMatrix_quad_lower` / `..._quad_upper` (quadratic-form lower/upper bounds)
  - `gramMatrix_quad_upper_of_feature_bounds_q` (row-norm bounds imply `q L_K^2 L_Z^2` envelope)
  - `regularizedNormalMatrix_quad_upper_of_feature_bounds_q`
  - `rowNormSq_kron_eq` / `rowNormSq_kron_le_product_bounds` (Kronecker row-norm factorization and bound)
  - `rowNormSq_bound_of_factorized_rows`
  - `gramMatrix_quad_upper_of_factorized_feature_bounds_q`
  - `regularizedNormalMatrix_quad_upper_of_factorized_feature_bounds_q`
  - `kFeatFromObs` / `zFeatFromObs` / `factorizedFeatureMatrix`
  - `rowNormSq_bound_of_observed_factor_matrices`
  - `gramMatrix_quad_upper_of_observed_factor_matrices_q`
  - `regularizedNormalMatrix_quad_upper_of_observed_factor_matrices_q`
  - `eigenvalue_lower_of_quad_lower` / `eigenvalue_upper_of_quad_upper`
  - `regularizedNormalMatrix_eigenvalue_lower` / `..._eigenvalue_upper`
  - `regularizedNormalMatrix_eigen_ratio_le_kappaUpperFromCount` / `...Density`
  - `regularizedNormalMatrix_eigen_ratio_le_kappaUpperFromCount_of_factorized_feature_bounds_q`
  - `regularizedNormalMatrix_eigen_ratio_le_kappaUpperFromCount_of_observed_factor_matrices_q`
  - `kEps` / `pcgContractionFactor` / `kEps_ge_log_ratio`
  - `geometric_term_le_eps_of_kEps`
  - `error_bound_at_kEps_of_assumptions`
  - `error_bound_at_kEps`
  - `totalCostToAccuracy_formula`

## 2. New v2 theory: condition number
Section 4 of the paper introduces a spectral decomposition at matrix level:

- `Â = FᵀF + λ(I_r ⊗ K)`
- feature row vectors `φ_p = z_{m_p} ⊗ k_{i_p}`

Under assumptions

- `K` is SPD with eigenvalues in `[μ_min, μ_max]`
- row-norm bounds `||k_i||₂ ≤ L_K`, `||z_m||₂ ≤ L_Z`

we derive

`λ_min(Â) ≥ λ μ_min`

`λ_max(Â) ≤ q L_K^2 L_Z^2 + λ μ_max`

thus

`κ(Â) ≤ (q L_K^2 L_Z^2 + λ μ_max) / (λ μ_min)`

and with `ρ=q/(nM)`,

`κ(Â) ≤ (ρ nM L_K^2 L_Z^2 + λ μ_max) / (λ μ_min)`.

This directly addresses the review request on linking conditioning to regularization and sampling density.

## 3. New v2 theory: convergence rate and `k_ε`
Section 5 adds the standard PCG error bound:

`||e_k||_A ≤ 2 ((sqrt(κ_P)-1)/(sqrt(κ_P)+1))^k ||e_0||_A`

which yields

`k_ε = ceil( log(2/ε) / log((sqrt(κ_P)+1)/(sqrt(κ_P)-1)) )`.

Combining with the Lean-verified one-step cost

`C_iter = q(2r+nr) + 2n^2r + 6nr`

gives

`C_total(ε) ≤ k_ε · C_iter`.

This closes the gap where iteration count `k` was previously left as a free variable.

## 4. Connection to tensor completion theory
Section 6 now provides explicit positioning:

- vs. ALS: this work avoids explicit large normal-matrix assembly and emphasizes observed-entry operator actions.
- vs. SGD: this work trades stochastic flexibility for deterministic linear-system structure with condition-number-based iteration analysis.

The same operator template is discussed for Tucker/TT local updates when they can be written as

`A_local = F_localᵀF_local + λG`.

## 5. Formalization methodology discussion
Section 7 now explains practical Lean design choices:

- dimension safety via `Matrix (Fin n) (Fin r) ℝ`
- safe observation mapping via `Fin`-indexed tuples
- compositional predicates (`Symmetric`, `PosDef`, `PosSemidef`, `SPD`)
- certified arithmetic identities via `Nat`-level cost definitions

## 6. Numerical experiments protocol (non-formal)
Section 8 adds a reproducible experimental plan (without fabricating results):

- sweep `ρ=q/(nM)` and `λ`
- report per-iteration time, total runtime, iteration count, residual
- compare with dense normal-equation solve for small/medium sizes
- test falsifiable hypotheses implied by the complexity and conditioning analysis

## 7. Current boundary of formal certification
- Fully formalized: operator model, SPD admissibility, cost identities, and the v2 spectral bridge chain (density/count equivalence, matrix-level positivity, quadratic envelopes, and eigenvalue-ratio upper bounds).
- Newly completed tail step in Section 5: the analytic logarithmic inequality turning `k_ε` into the explicit geometric guarantee `2*((sqrt κ-1)/(sqrt κ+1))^k ≤ ε`, formalized as `geometric_term_le_eps_of_kEps`, with direct downstream theorem `error_bound_at_kEps`.
- Still mathematical/external: the standard PCG contraction premise itself (`hContract`), which is currently used as an input assumption and then linked end-to-end to the certified `k_ε` and complexity chain.
