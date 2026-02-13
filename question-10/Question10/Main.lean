import Question10.SpectralConvergence

namespace Question10
namespace ProblemData

variable (P : ProblemData)

theorem sparse_matvec_avoids_ambient_enumeration :
    P.observationCount ≤ P.ambientTensorSize ∧
      P.costSystemMatVec ≤
        P.ambientTensorSize * (2 * P.r + P.n * P.r) + P.n * P.n * P.r := by
  exact ⟨P.avoid_ambient_enumeration, P.costSystemMatVec_le_ambient_scaled⟩

theorem main_solver_statement
    (hDataSymm : P.Symmetric P.dataTerm)
    (hDataNonneg : P.PosSemidef P.dataTerm)
    (hKSymm : P.Symmetric P.kMul)
    (hKPos : P.PosDef P.kMul) :
    P.PCGAdmissible P.systemOp (P.preconditionerApply P.defaultMu) ∧
      P.costSystemMatVec = P.q * (2 * P.r + P.n * P.r) + P.n * P.n * P.r ∧
      (∀ iters : Nat, P.totalCost iters = iters * P.costPCGIter) := by
  refine ⟨P.pcg_ready_fully_structured hDataSymm hDataNonneg hKSymm hKPos,
    P.costSystemMatVec_eq, ?_⟩
  intro iters
  exact P.totalCost_eq iters

theorem sparse_matvec_strictly_better_than_ambient
    (hqStrict : P.q < P.ambientTensorSize) :
    P.costSystemMatVec <
      P.ambientTensorSize * (2 * P.r + P.n * P.r) + P.n * P.n * P.r := by
  exact P.costSystemMatVec_lt_ambient_scaled hqStrict

theorem v2_kappa_density_count_equiv
    (muMin muMax LK LZ : ℝ)
    (hM : 0 < P.M) :
    P.kappaUpperFromDensity muMin muMax LK LZ =
      P.kappaUpperFromCount muMin muMax LK LZ := by
  exact P.kappaUpperFromDensity_eq_count muMin muMax LK LZ hM

theorem v2_kappa_upper_bound_from_extremes_count
    {muMin muMax LK LZ lambdaMinA lambdaMaxA : ℝ}
    (hmuMin : 0 < muMin)
    (hmuMax : 0 ≤ muMax)
    (hLower : P.lambda * muMin ≤ lambdaMinA)
    (hUpper : lambdaMaxA ≤ (P.q : ℝ) * LK ^ 2 * LZ ^ 2 + P.lambda * muMax) :
    kappaFromExtremes lambdaMinA lambdaMaxA ≤
      P.kappaUpperFromCount muMin muMax LK LZ := by
  exact P.kappaFromExtremes_le_kappaUpperFromCount hmuMin hmuMax hLower hUpper

theorem v2_kappa_upper_bound_from_extremes_density
    {muMin muMax LK LZ lambdaMinA lambdaMaxA : ℝ}
    (hM : 0 < P.M)
    (hmuMin : 0 < muMin)
    (hmuMax : 0 ≤ muMax)
    (hLower : P.lambda * muMin ≤ lambdaMinA)
    (hUpper : lambdaMaxA ≤ (P.q : ℝ) * LK ^ 2 * LZ ^ 2 + P.lambda * muMax) :
    kappaFromExtremes lambdaMinA lambdaMaxA ≤
      P.kappaUpperFromDensity muMin muMax LK LZ := by
  exact P.kappaFromExtremes_le_kappaUpperFromDensity hM hmuMin hmuMax hLower hUpper

theorem v2_eigen_sandwich_from_structured_assumptions
    (S : P.SpectralAssumptions) :
    P.lambda * S.muMin ≤ S.lambdaMinA ∧
      S.lambdaMaxA ≤ (P.q : ℝ) * S.LK ^ 2 * S.LZ ^ 2 + P.lambda * S.muMax := by
  exact S.eigen_sandwich

theorem v2_kappa_upper_bound_from_structured_assumptions_count
    (S : P.SpectralAssumptions) :
    kappaFromExtremes S.lambdaMinA S.lambdaMaxA ≤
      P.kappaUpperFromCount S.muMin S.muMax S.LK S.LZ := by
  exact S.kappa_bound_count

theorem v2_kappa_upper_bound_from_structured_assumptions_density
    (S : P.SpectralAssumptions) :
    kappaFromExtremes S.lambdaMinA S.lambdaMaxA ≤
      P.kappaUpperFromDensity S.muMin S.muMax S.LK S.LZ := by
  exact S.kappa_bound_density

theorem v2_matrix_level_regularized_posDef
    {obsIdx varIdx : Type*}
    [Fintype obsIdx] [Fintype varIdx]
    (F : Matrix obsIdx varIdx ℝ)
    {R : Matrix varIdx varIdx ℝ} {lam : ℝ}
    (hR : R.PosDef) (hlam : 0 < lam) :
    (regularizedNormalMatrix F R lam).PosDef := by
  exact regularizedNormalMatrix_posDef F hR hlam

theorem v2_matrix_level_regularized_eigenvalues_pos
    {obsIdx varIdx : Type*}
    [Fintype obsIdx] [Fintype varIdx] [DecidableEq varIdx]
    (F : Matrix obsIdx varIdx ℝ)
    {R : Matrix varIdx varIdx ℝ} {lam : ℝ}
    (hR : R.PosDef) (hlam : 0 < lam) (i : varIdx) :
    0 < (Matrix.PosDef.isHermitian (regularizedNormalMatrix_posDef F hR hlam)).eigenvalues i := by
  exact regularizedNormalMatrix_eigenvalues_pos F hR hlam i

theorem v2_matrix_level_quad_lower_bound
    {obsIdx varIdx : Type*}
    [Fintype obsIdx] [Fintype varIdx]
    (F : Matrix obsIdx varIdx ℝ) (R : Matrix varIdx varIdx ℝ) (muMin : ℝ)
    (hRLower :
      ∀ x : varIdx → ℝ, muMin * dotProduct (star x) x ≤ dotProduct (star x) (R.mulVec x)) :
    ∀ x : varIdx → ℝ,
      (P.lambda * muMin) * dotProduct (star x) x ≤
        dotProduct (star x) ((regularizedNormalMatrix F R P.lambda).mulVec x) := by
  exact regularizedNormalMatrix_quad_lower (P := P) F R muMin hRLower

theorem v2_matrix_level_quad_upper_bound
    {obsIdx varIdx : Type*}
    [Fintype obsIdx] [Fintype varIdx]
    (F : Matrix obsIdx varIdx ℝ) (R : Matrix varIdx varIdx ℝ)
    (muMax LK LZ : ℝ)
    (hGramUpper :
      ∀ x : varIdx → ℝ,
        dotProduct (star x) ((gramMatrix F).mulVec x) ≤
          ((P.q : ℝ) * LK ^ 2 * LZ ^ 2) * dotProduct (star x) x)
    (hRUpper :
      ∀ x : varIdx → ℝ, dotProduct (star x) (R.mulVec x) ≤ muMax * dotProduct (star x) x) :
    ∀ x : varIdx → ℝ,
      dotProduct (star x) ((regularizedNormalMatrix F R P.lambda).mulVec x) ≤
        (((P.q : ℝ) * LK ^ 2 * LZ ^ 2) + P.lambda * muMax) * dotProduct (star x) x := by
  exact regularizedNormalMatrix_quad_upper (P := P) F R muMax LK LZ hGramUpper hRUpper

theorem v2_matrix_level_gram_upper_from_feature_bounds_q
    {varIdx : Type*} [Fintype varIdx]
    (F : Matrix (Fin P.q) varIdx ℝ) (LK LZ : ℝ)
    (hRowBound : ∀ p : Fin P.q, dotProduct (star (F p)) (F p) ≤ LK ^ 2 * LZ ^ 2) :
    ∀ x : varIdx → ℝ,
      dotProduct (star x) ((gramMatrix F).mulVec x) ≤
        ((P.q : ℝ) * LK ^ 2 * LZ ^ 2) * dotProduct (star x) x := by
  exact gramMatrix_quad_upper_of_feature_bounds_q (P := P) F LK LZ hRowBound

theorem v2_matrix_level_rowNormSq_kron_le_product_bounds
    {kIdx zIdx : Type*} [Fintype kIdx] [Fintype zIdx]
    (kRow : kIdx → ℝ) (zRow : zIdx → ℝ) (LK LZ : ℝ)
    (hK : dotProduct (star kRow) kRow ≤ LK ^ 2)
    (hZ : dotProduct (star zRow) zRow ≤ LZ ^ 2) :
    dotProduct (star (fun u : kIdx × zIdx => kRow u.1 * zRow u.2))
      (fun u : kIdx × zIdx => kRow u.1 * zRow u.2) ≤
      LK ^ 2 * LZ ^ 2 := by
  exact rowNormSq_kron_le_product_bounds kRow zRow LK LZ hK hZ

theorem v2_matrix_level_rowNormSq_bound_of_factorized_rows
    {obsIdx kIdx zIdx : Type*}
    [Fintype obsIdx] [Fintype kIdx] [Fintype zIdx]
    (F : Matrix obsIdx (kIdx × zIdx) ℝ)
    (kFeat : obsIdx → kIdx → ℝ)
    (zFeat : obsIdx → zIdx → ℝ)
    (LK LZ : ℝ)
    (hFactor : ∀ p : obsIdx, ∀ i : kIdx, ∀ j : zIdx, F p (i, j) = kFeat p i * zFeat p j)
    (hKBound : ∀ p : obsIdx, dotProduct (star (kFeat p)) (kFeat p) ≤ LK ^ 2)
    (hZBound : ∀ p : obsIdx, dotProduct (star (zFeat p)) (zFeat p) ≤ LZ ^ 2) :
    ∀ p : obsIdx, dotProduct (star (F p)) (F p) ≤ LK ^ 2 * LZ ^ 2 := by
  exact rowNormSq_bound_of_factorized_rows (F := F) kFeat zFeat LK LZ hFactor hKBound hZBound

theorem v2_matrix_level_gram_upper_from_factorized_feature_bounds_q
    {kIdx zIdx : Type*} [Fintype kIdx] [Fintype zIdx]
    (F : Matrix (Fin P.q) (kIdx × zIdx) ℝ)
    (kFeat : Fin P.q → kIdx → ℝ)
    (zFeat : Fin P.q → zIdx → ℝ)
    (LK LZ : ℝ)
    (hFactor :
      ∀ p : Fin P.q, ∀ i : kIdx, ∀ j : zIdx, F p (i, j) = kFeat p i * zFeat p j)
    (hKBound : ∀ p : Fin P.q, dotProduct (star (kFeat p)) (kFeat p) ≤ LK ^ 2)
    (hZBound : ∀ p : Fin P.q, dotProduct (star (zFeat p)) (zFeat p) ≤ LZ ^ 2) :
    ∀ x : (kIdx × zIdx) → ℝ,
      dotProduct (star x) ((gramMatrix F).mulVec x) ≤
        ((P.q : ℝ) * LK ^ 2 * LZ ^ 2) * dotProduct (star x) x := by
  exact gramMatrix_quad_upper_of_factorized_feature_bounds_q
    (P := P) F kFeat zFeat LK LZ hFactor hKBound hZBound

theorem v2_matrix_level_gram_upper_from_observed_factor_matrices_q
    {iIdx mIdx kIdx zIdx : Type*}
    [Fintype kIdx] [Fintype zIdx]
    (obs : Fin P.q → iIdx × mIdx)
    (K : Matrix iIdx kIdx ℝ)
    (Z : Matrix mIdx zIdx ℝ)
    (LK LZ : ℝ)
    (hKRowBound : ∀ i : iIdx, dotProduct (star (K i)) (K i) ≤ LK ^ 2)
    (hZRowBound : ∀ m : mIdx, dotProduct (star (Z m)) (Z m) ≤ LZ ^ 2) :
    ∀ x : (kIdx × zIdx) → ℝ,
      dotProduct (star x) ((gramMatrix (factorizedFeatureMatrix obs K Z)).mulVec x) ≤
        ((P.q : ℝ) * LK ^ 2 * LZ ^ 2) * dotProduct (star x) x := by
  exact gramMatrix_quad_upper_of_observed_factor_matrices_q
    (P := P) obs K Z LK LZ hKRowBound hZRowBound

theorem v2_matrix_level_quad_upper_from_feature_bounds_q
    {varIdx : Type*} [Fintype varIdx]
    (F : Matrix (Fin P.q) varIdx ℝ) (R : Matrix varIdx varIdx ℝ)
    (muMax LK LZ : ℝ)
    (hRowBound : ∀ p : Fin P.q, dotProduct (star (F p)) (F p) ≤ LK ^ 2 * LZ ^ 2)
    (hRUpper :
      ∀ x : varIdx → ℝ, dotProduct (star x) (R.mulVec x) ≤ muMax * dotProduct (star x) x) :
    ∀ x : varIdx → ℝ,
      dotProduct (star x) ((regularizedNormalMatrix F R P.lambda).mulVec x) ≤
        (((P.q : ℝ) * LK ^ 2 * LZ ^ 2) + P.lambda * muMax) * dotProduct (star x) x := by
  exact regularizedNormalMatrix_quad_upper_of_feature_bounds_q
    (P := P) F R muMax LK LZ hRowBound hRUpper

theorem v2_matrix_level_eigenvalue_lower_from_quad
    {obsIdx varIdx : Type*}
    [Fintype obsIdx] [Fintype varIdx] [DecidableEq varIdx]
    (F : Matrix obsIdx varIdx ℝ) {R : Matrix varIdx varIdx ℝ}
    (hRPos : R.PosDef) (muMin : ℝ)
    (hRLower :
      ∀ x : varIdx → ℝ, muMin * dotProduct (star x) x ≤ dotProduct (star x) (R.mulVec x))
    (i : varIdx) :
    P.lambda * muMin ≤
      (Matrix.PosDef.isHermitian (regularizedNormalMatrix_posDef F hRPos P.hlambda)).eigenvalues i := by
  exact regularizedNormalMatrix_eigenvalue_lower (P := P) F hRPos muMin hRLower i

theorem v2_matrix_level_eigenvalue_upper_from_quad
    {obsIdx varIdx : Type*}
    [Fintype obsIdx] [Fintype varIdx] [DecidableEq varIdx]
    (F : Matrix obsIdx varIdx ℝ) {R : Matrix varIdx varIdx ℝ}
    (hRPos : R.PosDef)
    (muMax LK LZ : ℝ)
    (hGramUpper :
      ∀ x : varIdx → ℝ,
        dotProduct (star x) ((gramMatrix F).mulVec x) ≤
          ((P.q : ℝ) * LK ^ 2 * LZ ^ 2) * dotProduct (star x) x)
    (hRUpper :
      ∀ x : varIdx → ℝ, dotProduct (star x) (R.mulVec x) ≤ muMax * dotProduct (star x) x)
    (i : varIdx) :
    (Matrix.PosDef.isHermitian (regularizedNormalMatrix_posDef F hRPos P.hlambda)).eigenvalues i ≤
      ((P.q : ℝ) * LK ^ 2 * LZ ^ 2) + P.lambda * muMax := by
  exact regularizedNormalMatrix_eigenvalue_upper (P := P) F hRPos muMax LK LZ hGramUpper hRUpper i

theorem v2_matrix_level_eigen_ratio_kappa_upper_count
    {obsIdx varIdx : Type*}
    [Fintype obsIdx] [Fintype varIdx] [DecidableEq varIdx]
    (F : Matrix obsIdx varIdx ℝ) {R : Matrix varIdx varIdx ℝ}
    (hRPos : R.PosDef)
    (muMin muMax LK LZ : ℝ)
    (hmuMin : 0 < muMin)
    (hmuMax : 0 ≤ muMax)
    (hGramUpper :
      ∀ x : varIdx → ℝ,
        dotProduct (star x) ((gramMatrix F).mulVec x) ≤
          ((P.q : ℝ) * LK ^ 2 * LZ ^ 2) * dotProduct (star x) x)
    (hRLower :
      ∀ x : varIdx → ℝ, muMin * dotProduct (star x) x ≤ dotProduct (star x) (R.mulVec x))
    (hRUpper :
      ∀ x : varIdx → ℝ, dotProduct (star x) (R.mulVec x) ≤ muMax * dotProduct (star x) x)
    (iMax iMin : varIdx) :
    kappaFromExtremes
      ((Matrix.PosDef.isHermitian (regularizedNormalMatrix_posDef F hRPos P.hlambda)).eigenvalues iMin)
      ((Matrix.PosDef.isHermitian (regularizedNormalMatrix_posDef F hRPos P.hlambda)).eigenvalues iMax) ≤
      P.kappaUpperFromCount muMin muMax LK LZ := by
  exact regularizedNormalMatrix_eigen_ratio_le_kappaUpperFromCount
    (P := P) F hRPos muMin muMax LK LZ hmuMin hmuMax hGramUpper hRLower hRUpper iMax iMin

theorem v2_matrix_level_eigen_ratio_kappa_upper_density
    {obsIdx varIdx : Type*}
    [Fintype obsIdx] [Fintype varIdx] [DecidableEq varIdx]
    (F : Matrix obsIdx varIdx ℝ) {R : Matrix varIdx varIdx ℝ}
    (hRPos : R.PosDef)
    (muMin muMax LK LZ : ℝ)
    (hM : 0 < P.M)
    (hmuMin : 0 < muMin)
    (hmuMax : 0 ≤ muMax)
    (hGramUpper :
      ∀ x : varIdx → ℝ,
        dotProduct (star x) ((gramMatrix F).mulVec x) ≤
          ((P.q : ℝ) * LK ^ 2 * LZ ^ 2) * dotProduct (star x) x)
    (hRLower :
      ∀ x : varIdx → ℝ, muMin * dotProduct (star x) x ≤ dotProduct (star x) (R.mulVec x))
    (hRUpper :
      ∀ x : varIdx → ℝ, dotProduct (star x) (R.mulVec x) ≤ muMax * dotProduct (star x) x)
    (iMax iMin : varIdx) :
    kappaFromExtremes
      ((Matrix.PosDef.isHermitian (regularizedNormalMatrix_posDef F hRPos P.hlambda)).eigenvalues iMin)
      ((Matrix.PosDef.isHermitian (regularizedNormalMatrix_posDef F hRPos P.hlambda)).eigenvalues iMax) ≤
      P.kappaUpperFromDensity muMin muMax LK LZ := by
  exact regularizedNormalMatrix_eigen_ratio_le_kappaUpperFromDensity
    (P := P) F hRPos muMin muMax LK LZ hM hmuMin hmuMax hGramUpper hRLower hRUpper iMax iMin

theorem v2_matrix_level_quad_upper_from_factorized_feature_bounds_q
    {kIdx zIdx : Type*} [Fintype kIdx] [Fintype zIdx]
    (F : Matrix (Fin P.q) (kIdx × zIdx) ℝ)
    (R : Matrix (kIdx × zIdx) (kIdx × zIdx) ℝ)
    (muMax LK LZ : ℝ)
    (kFeat : Fin P.q → kIdx → ℝ)
    (zFeat : Fin P.q → zIdx → ℝ)
    (hFactor :
      ∀ p : Fin P.q, ∀ i : kIdx, ∀ j : zIdx, F p (i, j) = kFeat p i * zFeat p j)
    (hKBound : ∀ p : Fin P.q, dotProduct (star (kFeat p)) (kFeat p) ≤ LK ^ 2)
    (hZBound : ∀ p : Fin P.q, dotProduct (star (zFeat p)) (zFeat p) ≤ LZ ^ 2)
    (hRUpper :
      ∀ x : (kIdx × zIdx) → ℝ, dotProduct (star x) (R.mulVec x) ≤ muMax * dotProduct (star x) x) :
    ∀ x : (kIdx × zIdx) → ℝ,
      dotProduct (star x) ((regularizedNormalMatrix F R P.lambda).mulVec x) ≤
        (((P.q : ℝ) * LK ^ 2 * LZ ^ 2) + P.lambda * muMax) * dotProduct (star x) x := by
  exact regularizedNormalMatrix_quad_upper_of_factorized_feature_bounds_q
    (P := P) F R muMax LK LZ kFeat zFeat hFactor hKBound hZBound hRUpper

theorem v2_matrix_level_eigen_ratio_kappa_upper_count_from_factorized_feature_bounds_q
    {kIdx zIdx : Type*} [Fintype kIdx] [Fintype zIdx] [DecidableEq (kIdx × zIdx)]
    (F : Matrix (Fin P.q) (kIdx × zIdx) ℝ)
    {R : Matrix (kIdx × zIdx) (kIdx × zIdx) ℝ}
    (hRPos : R.PosDef)
    (muMin muMax LK LZ : ℝ)
    (hmuMin : 0 < muMin)
    (hmuMax : 0 ≤ muMax)
    (kFeat : Fin P.q → kIdx → ℝ)
    (zFeat : Fin P.q → zIdx → ℝ)
    (hFactor :
      ∀ p : Fin P.q, ∀ i : kIdx, ∀ j : zIdx, F p (i, j) = kFeat p i * zFeat p j)
    (hKBound : ∀ p : Fin P.q, dotProduct (star (kFeat p)) (kFeat p) ≤ LK ^ 2)
    (hZBound : ∀ p : Fin P.q, dotProduct (star (zFeat p)) (zFeat p) ≤ LZ ^ 2)
    (hRLower :
      ∀ x : (kIdx × zIdx) → ℝ, muMin * dotProduct (star x) x ≤ dotProduct (star x) (R.mulVec x))
    (hRUpper :
      ∀ x : (kIdx × zIdx) → ℝ, dotProduct (star x) (R.mulVec x) ≤ muMax * dotProduct (star x) x)
    (iMax iMin : (kIdx × zIdx)) :
    kappaFromExtremes
      ((Matrix.PosDef.isHermitian (regularizedNormalMatrix_posDef F hRPos P.hlambda)).eigenvalues iMin)
      ((Matrix.PosDef.isHermitian (regularizedNormalMatrix_posDef F hRPos P.hlambda)).eigenvalues iMax) ≤
      P.kappaUpperFromCount muMin muMax LK LZ := by
  exact regularizedNormalMatrix_eigen_ratio_le_kappaUpperFromCount_of_factorized_feature_bounds_q
    (P := P) F hRPos muMin muMax LK LZ hmuMin hmuMax
    kFeat zFeat hFactor hKBound hZBound hRLower hRUpper iMax iMin

theorem v2_matrix_level_quad_upper_from_observed_factor_matrices_q
    {iIdx mIdx kIdx zIdx : Type*}
    [Fintype kIdx] [Fintype zIdx]
    (obs : Fin P.q → iIdx × mIdx)
    (K : Matrix iIdx kIdx ℝ)
    (Z : Matrix mIdx zIdx ℝ)
    (R : Matrix (kIdx × zIdx) (kIdx × zIdx) ℝ)
    (muMax LK LZ : ℝ)
    (hKRowBound : ∀ i : iIdx, dotProduct (star (K i)) (K i) ≤ LK ^ 2)
    (hZRowBound : ∀ m : mIdx, dotProduct (star (Z m)) (Z m) ≤ LZ ^ 2)
    (hRUpper :
      ∀ x : (kIdx × zIdx) → ℝ, dotProduct (star x) (R.mulVec x) ≤ muMax * dotProduct (star x) x) :
    ∀ x : (kIdx × zIdx) → ℝ,
      dotProduct (star x)
          ((regularizedNormalMatrix (factorizedFeatureMatrix obs K Z) R P.lambda).mulVec x) ≤
        (((P.q : ℝ) * LK ^ 2 * LZ ^ 2) + P.lambda * muMax) * dotProduct (star x) x := by
  exact regularizedNormalMatrix_quad_upper_of_observed_factor_matrices_q
    (P := P) obs K Z R muMax LK LZ hKRowBound hZRowBound hRUpper

theorem v2_matrix_level_eigen_ratio_kappa_upper_count_from_observed_factor_matrices_q
    {iIdx mIdx kIdx zIdx : Type*}
    [Fintype kIdx] [Fintype zIdx] [DecidableEq (kIdx × zIdx)]
    (obs : Fin P.q → iIdx × mIdx)
    (K : Matrix iIdx kIdx ℝ)
    (Z : Matrix mIdx zIdx ℝ)
    {R : Matrix (kIdx × zIdx) (kIdx × zIdx) ℝ}
    (hRPos : R.PosDef)
    (muMin muMax LK LZ : ℝ)
    (hmuMin : 0 < muMin)
    (hmuMax : 0 ≤ muMax)
    (hKRowBound : ∀ i : iIdx, dotProduct (star (K i)) (K i) ≤ LK ^ 2)
    (hZRowBound : ∀ m : mIdx, dotProduct (star (Z m)) (Z m) ≤ LZ ^ 2)
    (hRLower :
      ∀ x : (kIdx × zIdx) → ℝ, muMin * dotProduct (star x) x ≤ dotProduct (star x) (R.mulVec x))
    (hRUpper :
      ∀ x : (kIdx × zIdx) → ℝ, dotProduct (star x) (R.mulVec x) ≤ muMax * dotProduct (star x) x)
    (iMax iMin : (kIdx × zIdx)) :
    kappaFromExtremes
      ((Matrix.PosDef.isHermitian
          (regularizedNormalMatrix_posDef (factorizedFeatureMatrix obs K Z) hRPos P.hlambda)).eigenvalues iMin)
      ((Matrix.PosDef.isHermitian
          (regularizedNormalMatrix_posDef (factorizedFeatureMatrix obs K Z) hRPos P.hlambda)).eigenvalues iMax) ≤
      P.kappaUpperFromCount muMin muMax LK LZ := by
  exact regularizedNormalMatrix_eigen_ratio_le_kappaUpperFromCount_of_observed_factor_matrices_q
    (P := P) obs K Z hRPos muMin muMax LK LZ hmuMin hmuMax
    hKRowBound hZRowBound hRLower hRUpper iMax iMin

theorem v2_total_cost_to_accuracy_formula
    (kappaP eps : ℝ) :
    P.totalCostToAccuracy kappaP eps =
      kEps kappaP eps *
        (P.q * (2 * P.r + P.n * P.r) + P.n * P.n * P.r + P.n * P.n * P.r +
          6 * (P.n * P.r)) := by
  exact P.totalCostToAccuracy_formula kappaP eps

theorem v2_kEps_ge_log_ratio
    (kappaP eps : ℝ) :
    Real.log (2 / eps) / Real.log ((Real.sqrt kappaP + 1) / (Real.sqrt kappaP - 1)) ≤
      (kEps kappaP eps : ℝ) := by
  exact kEps_ge_log_ratio kappaP eps

theorem v2_geometric_term_le_eps_of_kEps
    {kappaP eps : ℝ}
    (hkappa : 1 < kappaP)
    (heps0 : 0 < eps) :
    2 * (pcgContractionFactor kappaP) ^ (kEps kappaP eps) ≤ eps := by
  exact geometric_term_le_eps_of_kEps hkappa heps0

theorem v2_error_bound_at_kEps_of_assumptions
    {err0 : ℝ} {err : Nat → ℝ}
    (kappaP eps : ℝ)
    (hContract :
      ∀ k : Nat, err k ≤ 2 * (pcgContractionFactor kappaP) ^ k * err0)
    (hGeometricAtBudget :
      2 * (pcgContractionFactor kappaP) ^ (kEps kappaP eps) ≤ eps)
    (herr0 : 0 ≤ err0) :
    err (kEps kappaP eps) ≤ eps * err0 := by
  exact error_bound_at_kEps_of_assumptions kappaP eps hContract hGeometricAtBudget herr0

theorem v2_error_bound_at_kEps
    {err0 : ℝ} {err : Nat → ℝ}
    (kappaP eps : ℝ)
    (hkappa : 1 < kappaP)
    (heps0 : 0 < eps)
    (hContract :
      ∀ k : Nat, err k ≤ 2 * (pcgContractionFactor kappaP) ^ k * err0)
    (herr0 : 0 ≤ err0) :
    err (kEps kappaP eps) ≤ eps * err0 := by
  exact error_bound_at_kEps kappaP eps hkappa heps0 hContract herr0

end ProblemData
end Question10
