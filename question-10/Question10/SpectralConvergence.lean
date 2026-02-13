import Question10.Complexity

namespace Question10
namespace ProblemData

noncomputable section

variable (P : ProblemData)

/-- Observation density `ρ = q / (nM)` used in the v2 analysis section. -/
def observationDensity : ℝ :=
  (P.q : ℝ) / ((P.n : ℝ) * (P.M : ℝ))

/-- Condition-number upper-bound expression in count form (`q`). -/
def kappaUpperFromCount (muMin muMax LK LZ : ℝ) : ℝ :=
  ((P.q : ℝ) * LK ^ 2 * LZ ^ 2 + P.lambda * muMax) / (P.lambda * muMin)

/-- The same upper-bound expression written with observation density (`ρ`). -/
def kappaUpperFromDensity (muMin muMax LK LZ : ℝ) : ℝ :=
  (P.observationDensity * (P.n : ℝ) * (P.M : ℝ) * LK ^ 2 * LZ ^ 2 + P.lambda * muMax) /
    (P.lambda * muMin)

/-- Abstract condition number from extremal values. -/
def kappaFromExtremes (lambdaMinA lambdaMaxA : ℝ) : ℝ :=
  lambdaMaxA / lambdaMinA

/-- Recovering the observation count from density requires `M > 0` (with `n > 0` from data). -/
theorem observationDensity_mul_ambient
    (hM : 0 < P.M) :
    P.observationDensity * (P.n : ℝ) * (P.M : ℝ) = (P.q : ℝ) := by
  have hn : (0 : ℝ) < (P.n : ℝ) := by
    exact_mod_cast P.hn
  have hm : (0 : ℝ) < (P.M : ℝ) := by
    exact_mod_cast hM
  have hnm : ((P.n : ℝ) * (P.M : ℝ)) ≠ 0 := by
    nlinarith
  unfold observationDensity
  field_simp [hnm]
  ring

/-- Algebraic equivalence between the `q`-form and `ρ`-form of the bound. -/
theorem kappaUpperFromDensity_eq_count
    (muMin muMax LK LZ : ℝ)
    (hM : 0 < P.M) :
    P.kappaUpperFromDensity muMin muMax LK LZ =
      P.kappaUpperFromCount muMin muMax LK LZ := by
  unfold kappaUpperFromDensity kappaUpperFromCount
  rw [P.observationDensity_mul_ambient hM]

/--
Given a lower bound on `λ_min(A)` and an upper bound on `λ_max(A)`,
derive the corresponding condition-number upper bound in count form.
-/
theorem kappaFromExtremes_le_kappaUpperFromCount
    {muMin muMax LK LZ lambdaMinA lambdaMaxA : ℝ}
    (hmuMin : 0 < muMin)
    (hmuMax : 0 ≤ muMax)
    (hLower : P.lambda * muMin ≤ lambdaMinA)
    (hUpper : lambdaMaxA ≤ (P.q : ℝ) * LK ^ 2 * LZ ^ 2 + P.lambda * muMax) :
    kappaFromExtremes lambdaMinA lambdaMaxA ≤
      P.kappaUpperFromCount muMin muMax LK LZ := by
  let base : ℝ := P.lambda * muMin
  let expr : ℝ := (P.q : ℝ) * LK ^ 2 * LZ ^ 2 + P.lambda * muMax
  have hbasePos : 0 < base := by
    dsimp [base]
    nlinarith [P.hlambda, hmuMin]
  have hbaseNonneg : 0 ≤ base := hbasePos.le
  have hexprNonneg : 0 ≤ expr := by
    have hq : 0 ≤ (P.q : ℝ) := by
      exact_mod_cast Nat.zero_le P.q
    have hsqLK : 0 ≤ LK ^ 2 := by nlinarith
    have hsqLZ : 0 ≤ LZ ^ 2 := by nlinarith
    have hmulPart : 0 ≤ (P.q : ℝ) * LK ^ 2 * LZ ^ 2 := by
      exact mul_nonneg (mul_nonneg hq hsqLK) hsqLZ
    have hregPart : 0 ≤ P.lambda * muMax := by
      nlinarith [P.hlambda, hmuMax]
    dsimp [expr]
    nlinarith
  have hminPos : 0 < lambdaMinA := by
    have h : base ≤ lambdaMinA := by simpa [base] using hLower
    exact lt_of_lt_of_le hbasePos h
  have hmulUpper : lambdaMaxA * base ≤ expr * base := by
    have h : lambdaMaxA ≤ expr := by simpa [expr] using hUpper
    exact mul_le_mul_of_nonneg_right h hbaseNonneg
  have hmulLower : expr * base ≤ expr * lambdaMinA := by
    have h : base ≤ lambdaMinA := by simpa [base] using hLower
    exact mul_le_mul_of_nonneg_left h hexprNonneg
  have hCross : lambdaMaxA * base ≤ expr * lambdaMinA := le_trans hmulUpper hmulLower
  have hDiv : lambdaMaxA / lambdaMinA ≤ expr / base := by
    exact (div_le_div_iff₀ hminPos hbasePos).2
      (by simpa [mul_comm, mul_left_comm, mul_assoc] using hCross)
  simpa [ProblemData.kappaFromExtremes, ProblemData.kappaUpperFromCount, base, expr] using hDiv

/-- Density-form variant of the spectral condition-number bound. -/
theorem kappaFromExtremes_le_kappaUpperFromDensity
    {muMin muMax LK LZ lambdaMinA lambdaMaxA : ℝ}
    (hM : 0 < P.M)
    (hmuMin : 0 < muMin)
    (hmuMax : 0 ≤ muMax)
    (hLower : P.lambda * muMin ≤ lambdaMinA)
    (hUpper : lambdaMaxA ≤ (P.q : ℝ) * LK ^ 2 * LZ ^ 2 + P.lambda * muMax) :
    kappaFromExtremes lambdaMinA lambdaMaxA ≤
      P.kappaUpperFromDensity muMin muMax LK LZ := by
  rw [P.kappaUpperFromDensity_eq_count muMin muMax LK LZ hM]
  exact P.kappaFromExtremes_le_kappaUpperFromCount hmuMin hmuMax hLower hUpper

/--
Structured assumptions mirroring the paper's Section 4 bound setup:
`μ_min, μ_max, L_K, L_Z` and abstract extremal bounds for `A`.
-/
structure SpectralAssumptions where
  muMin : ℝ
  muMax : ℝ
  LK : ℝ
  LZ : ℝ
  lambdaMinA : ℝ
  lambdaMaxA : ℝ
  hM : 0 < P.M
  hmuMin : 0 < muMin
  hmuMax : 0 ≤ muMax
  hLower : P.lambda * muMin ≤ lambdaMinA
  hUpper : lambdaMaxA ≤ (P.q : ℝ) * LK ^ 2 * LZ ^ 2 + P.lambda * muMax

namespace SpectralAssumptions

theorem eigen_sandwich (S : P.SpectralAssumptions) :
    P.lambda * S.muMin ≤ S.lambdaMinA ∧
      S.lambdaMaxA ≤ (P.q : ℝ) * S.LK ^ 2 * S.LZ ^ 2 + P.lambda * S.muMax := by
  exact ⟨S.hLower, S.hUpper⟩

theorem kappa_bound_count (S : P.SpectralAssumptions) :
    kappaFromExtremes S.lambdaMinA S.lambdaMaxA ≤
      P.kappaUpperFromCount S.muMin S.muMax S.LK S.LZ := by
  exact P.kappaFromExtremes_le_kappaUpperFromCount
    S.hmuMin S.hmuMax S.hLower S.hUpper

theorem kappa_bound_density (S : P.SpectralAssumptions) :
    kappaFromExtremes S.lambdaMinA S.lambdaMaxA ≤
      P.kappaUpperFromDensity S.muMin S.muMax S.LK S.LZ := by
  exact P.kappaFromExtremes_le_kappaUpperFromDensity
    S.hM S.hmuMin S.hmuMax S.hLower S.hUpper

theorem density_count_equiv (S : P.SpectralAssumptions) :
    P.kappaUpperFromDensity S.muMin S.muMax S.LK S.LZ =
      P.kappaUpperFromCount S.muMin S.muMax S.LK S.LZ := by
  exact P.kappaUpperFromDensity_eq_count S.muMin S.muMax S.LK S.LZ S.hM

end SpectralAssumptions

/- Matrix-level normal-matrix objects used in Section 4:
   gram term F^T F and regularized matrix F^T F + lam * R. -/
section MatrixLevel

variable {obsIdx varIdx : Type*}
  [Fintype obsIdx] [Fintype varIdx]

def gramMatrix (F : Matrix obsIdx varIdx ℝ) : Matrix varIdx varIdx ℝ :=
  Matrix.transpose F * F

def regularizedNormalMatrix
    (F : Matrix obsIdx varIdx ℝ) (R : Matrix varIdx varIdx ℝ) (lam : ℝ) :
    Matrix varIdx varIdx ℝ :=
  gramMatrix F + lam • R

theorem dotProduct_star_smul_mulVec
    (a : ℝ) (A : Matrix varIdx varIdx ℝ) (x : varIdx → ℝ) :
    dotProduct (star x) ((a • A).mulVec x) = a * dotProduct (star x) (A.mulVec x) := by
  simp [Matrix.mulVec, dotProduct, Finset.mul_sum, Finset.sum_mul, mul_assoc,
    mul_left_comm, mul_comm]

theorem dotProduct_star_regularizedNormalMatrix_mulVec
    (F : Matrix obsIdx varIdx ℝ) (R : Matrix varIdx varIdx ℝ) (lam : ℝ) (x : varIdx → ℝ) :
    dotProduct (star x) ((regularizedNormalMatrix F R lam).mulVec x) =
      dotProduct (star x) ((gramMatrix F).mulVec x) +
        lam * dotProduct (star x) (R.mulVec x) := by
  unfold regularizedNormalMatrix
  rw [Matrix.add_mulVec, dotProduct_add, dotProduct_star_smul_mulVec]

theorem dotProduct_star_gramMatrix_mulVec
    (F : Matrix obsIdx varIdx ℝ) (x : varIdx → ℝ) :
    dotProduct (star x) ((gramMatrix F).mulVec x) =
      dotProduct (star (F.mulVec x)) (F.mulVec x) := by
  unfold gramMatrix
  rw [← Matrix.mulVec_mulVec, Matrix.dotProduct_mulVec]
  simp [Matrix.vecMul_transpose]

theorem gramMatrix_posSemidef (F : Matrix obsIdx varIdx ℝ) :
    (gramMatrix F).PosSemidef := by
  simpa [gramMatrix, Matrix.conjTranspose] using
    (Matrix.posSemidef_conjTranspose_mul_self F)

theorem posDef_smul_of_pos
    {R : Matrix varIdx varIdx ℝ} {lam : ℝ}
    (hR : R.PosDef) (hlam : 0 < lam) :
    (lam • R).PosDef := by
  refine ⟨?_, ?_⟩
  · rw [Matrix.IsHermitian]
    simpa [Matrix.conjTranspose_smul] using congrArg (fun M => lam • M) hR.isHermitian
  · intro x hx
    have hbase : 0 < dotProduct (star x) (R.mulVec x) := hR.2 x hx
    have hEq : dotProduct (star x) ((lam • R).mulVec x) =
        lam * dotProduct (star x) (R.mulVec x) := by
      exact dotProduct_star_smul_mulVec lam R x
    rw [hEq]
    nlinarith

theorem regularizedNormalMatrix_posDef
    (F : Matrix obsIdx varIdx ℝ) {R : Matrix varIdx varIdx ℝ} {lam : ℝ}
    (hR : R.PosDef) (hlam : 0 < lam) :
    (regularizedNormalMatrix F R lam).PosDef := by
  unfold regularizedNormalMatrix
  have hGram : (gramMatrix F).PosSemidef := gramMatrix_posSemidef F
  have hReg : (lam • R).PosDef := posDef_smul_of_pos hR hlam
  exact Matrix.PosDef.posSemidef_add hGram hReg

theorem regularizedNormalMatrix_eigenvalues_pos
    (F : Matrix obsIdx varIdx ℝ) {R : Matrix varIdx varIdx ℝ} {lam : ℝ}
    [DecidableEq varIdx]
    (hR : R.PosDef) (hlam : 0 < lam) (i : varIdx) :
    0 < (Matrix.PosDef.isHermitian (regularizedNormalMatrix_posDef F hR hlam)).eigenvalues i := by
  have hA : (regularizedNormalMatrix F R lam).PosDef :=
    regularizedNormalMatrix_posDef F hR hlam
  simpa using hA.eigenvalues_pos i

theorem eigenvalue_lower_of_quad_lower
    [DecidableEq varIdx]
    {A : Matrix varIdx varIdx ℝ}
    (hA : A.IsHermitian)
    (c : ℝ)
    (hLower :
      ∀ x : varIdx → ℝ,
        c * dotProduct (star x) x ≤ dotProduct (star x) (A.mulVec x))
    (i : varIdx) :
    c ≤ hA.eigenvalues i := by
  have hnorm' : ‖(hA.eigenvectorBasis i : EuclideanSpace ℝ varIdx)‖ = 1 :=
    hA.eigenvectorBasis.orthonormal.1 i
  have hsq : ‖(hA.eigenvectorBasis i : EuclideanSpace ℝ varIdx)‖ ^ 2 = 1 := by
    nlinarith [hnorm']
  have hnorm : dotProduct (star ⇑(hA.eigenvectorBasis i)) (⇑(hA.eigenvectorBasis i)) = 1 := by
    calc
      dotProduct (star ⇑(hA.eigenvectorBasis i)) (⇑(hA.eigenvectorBasis i))
          = ‖(hA.eigenvectorBasis i : EuclideanSpace ℝ varIdx)‖ ^ 2 := by
            rw [← EuclideanSpace.inner_eq_star_dotProduct]
            simp [inner_self_eq_norm_sq_to_K]
      _ = 1 := hsq
  have hEig :
      hA.eigenvalues i =
        dotProduct (star ⇑(hA.eigenvectorBasis i)) (A.mulVec ⇑(hA.eigenvectorBasis i)) := by
    simpa using hA.eigenvalues_eq i
  have hAtEig : c * dotProduct (star ⇑(hA.eigenvectorBasis i)) (⇑(hA.eigenvectorBasis i)) ≤
      dotProduct (star ⇑(hA.eigenvectorBasis i)) (A.mulVec ⇑(hA.eigenvectorBasis i)) :=
    hLower ⇑(hA.eigenvectorBasis i)
  rw [hnorm] at hAtEig
  have hAtEig' : c ≤ dotProduct (star ⇑(hA.eigenvectorBasis i)) (A.mulVec ⇑(hA.eigenvectorBasis i)) := by
    simpa using hAtEig
  rw [hEig]
  exact hAtEig'

theorem eigenvalue_upper_of_quad_upper
    [DecidableEq varIdx]
    {A : Matrix varIdx varIdx ℝ}
    (hA : A.IsHermitian)
    (c : ℝ)
    (hUpper :
      ∀ x : varIdx → ℝ,
        dotProduct (star x) (A.mulVec x) ≤ c * dotProduct (star x) x)
    (i : varIdx) :
    hA.eigenvalues i ≤ c := by
  have hnorm' : ‖(hA.eigenvectorBasis i : EuclideanSpace ℝ varIdx)‖ = 1 :=
    hA.eigenvectorBasis.orthonormal.1 i
  have hsq : ‖(hA.eigenvectorBasis i : EuclideanSpace ℝ varIdx)‖ ^ 2 = 1 := by
    nlinarith [hnorm']
  have hnorm : dotProduct (star ⇑(hA.eigenvectorBasis i)) (⇑(hA.eigenvectorBasis i)) = 1 := by
    calc
      dotProduct (star ⇑(hA.eigenvectorBasis i)) (⇑(hA.eigenvectorBasis i))
          = ‖(hA.eigenvectorBasis i : EuclideanSpace ℝ varIdx)‖ ^ 2 := by
            rw [← EuclideanSpace.inner_eq_star_dotProduct]
            simp [inner_self_eq_norm_sq_to_K]
      _ = 1 := hsq
  have hEig :
      hA.eigenvalues i =
        dotProduct (star ⇑(hA.eigenvectorBasis i)) (A.mulVec ⇑(hA.eigenvectorBasis i)) := by
    simpa using hA.eigenvalues_eq i
  have hAtEig :
      dotProduct (star ⇑(hA.eigenvectorBasis i)) (A.mulVec ⇑(hA.eigenvectorBasis i)) ≤
        c * dotProduct (star ⇑(hA.eigenvectorBasis i)) (⇑(hA.eigenvectorBasis i)) :=
    hUpper ⇑(hA.eigenvectorBasis i)
  rw [hnorm] at hAtEig
  have hAtEig' : dotProduct (star ⇑(hA.eigenvectorBasis i)) (A.mulVec ⇑(hA.eigenvectorBasis i)) ≤ c := by
    simpa using hAtEig
  rw [hEig]
  exact hAtEig'

theorem regularizedNormalMatrix_quad_lower
    (F : Matrix obsIdx varIdx ℝ) (R : Matrix varIdx varIdx ℝ) (muMin : ℝ)
    (hRLower :
      ∀ x : varIdx → ℝ, muMin * dotProduct (star x) x ≤ dotProduct (star x) (R.mulVec x)) :
    ∀ x : varIdx → ℝ,
      (P.lambda * muMin) * dotProduct (star x) x ≤
        dotProduct (star x) ((regularizedNormalMatrix F R P.lambda).mulVec x) := by
  intro x
  have hGramPS : (gramMatrix F).PosSemidef := gramMatrix_posSemidef F
  have hGramNonneg : 0 ≤ dotProduct (star x) ((gramMatrix F).mulVec x) := hGramPS.2 x
  have hRScaled :
      P.lambda * (muMin * dotProduct (star x) x) ≤
        P.lambda * dotProduct (star x) (R.mulVec x) := by
    exact mul_le_mul_of_nonneg_left (hRLower x) (le_of_lt P.hlambda)
  have hDecomp := dotProduct_star_regularizedNormalMatrix_mulVec F R P.lambda x
  rw [hDecomp]
  nlinarith

theorem regularizedNormalMatrix_quad_upper
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
  intro x
  have hRScaled :
      P.lambda * dotProduct (star x) (R.mulVec x) ≤
        P.lambda * (muMax * dotProduct (star x) x) := by
    exact mul_le_mul_of_nonneg_left (hRUpper x) (le_of_lt P.hlambda)
  have hDecomp := dotProduct_star_regularizedNormalMatrix_mulVec F R P.lambda x
  rw [hDecomp]
  nlinarith [hGramUpper x, hRScaled]

theorem gramMatrix_quad_upper_of_rowNormSq_bound
    (F : Matrix obsIdx varIdx ℝ) (rowBound : ℝ)
    (hRowBound : ∀ p : obsIdx, dotProduct (star (F p)) (F p) ≤ rowBound) :
    ∀ x : varIdx → ℝ,
      dotProduct (star x) ((gramMatrix F).mulVec x) ≤
        ((Fintype.card obsIdx : ℝ) * rowBound) * dotProduct (star x) x := by
  intro x
  have hGramEq :
      dotProduct (star x) ((gramMatrix F).mulVec x) =
        ∑ p : obsIdx, (F.mulVec x p) ^ 2 := by
    rw [dotProduct_star_gramMatrix_mulVec (F := F) x]
    simp [gramMatrix, dotProduct, pow_two]
  have hTerm :
      ∀ p : obsIdx,
        (F.mulVec x p) ^ 2 ≤ rowBound * dotProduct (star x) x := by
    intro p
    have hCS :
        (F.mulVec x p) ^ 2 ≤
          dotProduct (star (F p)) (F p) * dotProduct (star x) x := by
      unfold Matrix.mulVec dotProduct
      simpa [pow_two, mul_assoc, mul_left_comm, mul_comm] using
        (Finset.sum_mul_sq_le_sq_mul_sq (s := Finset.univ)
          (f := fun j : varIdx => F p j) (g := fun j : varIdx => x j))
    have hxxNonneg : 0 ≤ dotProduct (star x) x := by
      simpa using (dotProduct_star_self_nonneg x)
    have hMul :
        dotProduct (star (F p)) (F p) * dotProduct (star x) x ≤
          rowBound * dotProduct (star x) x := by
      exact mul_le_mul_of_nonneg_right (hRowBound p) hxxNonneg
    exact le_trans hCS hMul
  have hSum :
      (∑ p : obsIdx, (F.mulVec x p) ^ 2) ≤
        (∑ p : obsIdx, rowBound * dotProduct (star x) x) := by
    refine Finset.sum_le_sum ?_
    intro p hp
    exact hTerm p
  rw [hGramEq]
  calc
    ∑ p : obsIdx, (F.mulVec x p) ^ 2
        ≤ ∑ p : obsIdx, (rowBound * dotProduct (star x) x) := hSum
    _ = (Fintype.card obsIdx : ℝ) * (rowBound * dotProduct (star x) x) := by
      simp
    _ = ((Fintype.card obsIdx : ℝ) * rowBound) * dotProduct (star x) x := by ring

theorem gramMatrix_quad_upper_of_feature_bounds
    (F : Matrix obsIdx varIdx ℝ) (LK LZ : ℝ)
    (hRowBound : ∀ p : obsIdx, dotProduct (star (F p)) (F p) ≤ LK ^ 2 * LZ ^ 2) :
    ∀ x : varIdx → ℝ,
      dotProduct (star x) ((gramMatrix F).mulVec x) ≤
        ((Fintype.card obsIdx : ℝ) * LK ^ 2 * LZ ^ 2) * dotProduct (star x) x := by
  have h :=
    gramMatrix_quad_upper_of_rowNormSq_bound (F := F) (rowBound := LK ^ 2 * LZ ^ 2) hRowBound
  simpa [mul_assoc, mul_left_comm, mul_comm] using h

theorem gramMatrix_quad_upper_of_feature_bounds_q
    (F : Matrix (Fin P.q) varIdx ℝ) (LK LZ : ℝ)
    (hRowBound : ∀ p : Fin P.q, dotProduct (star (F p)) (F p) ≤ LK ^ 2 * LZ ^ 2) :
    ∀ x : varIdx → ℝ,
      dotProduct (star x) ((gramMatrix F).mulVec x) ≤
        ((P.q : ℝ) * LK ^ 2 * LZ ^ 2) * dotProduct (star x) x := by
  simpa using gramMatrix_quad_upper_of_feature_bounds (F := F) LK LZ hRowBound

/--
Squared norm factorization for rank-1/Kronecker row features:
`‖k ⊗ z‖² = ‖k‖² · ‖z‖²`.
-/
theorem rowNormSq_kron_eq
    {kIdx zIdx : Type*} [Fintype kIdx] [Fintype zIdx]
    (kRow : kIdx → ℝ) (zRow : zIdx → ℝ) :
    dotProduct (star (fun u : kIdx × zIdx => kRow u.1 * zRow u.2))
      (fun u : kIdx × zIdx => kRow u.1 * zRow u.2) =
      dotProduct (star kRow) kRow * dotProduct (star zRow) zRow := by
  simp [dotProduct, Fintype.sum_prod_type, pow_two, mul_assoc, mul_left_comm, mul_comm,
    Finset.sum_mul, Finset.mul_sum]
  rw [Finset.sum_comm]

/--
If each factor row has bounded squared norm, then the Kronecker row does too.
-/
theorem rowNormSq_kron_le_product_bounds
    {kIdx zIdx : Type*} [Fintype kIdx] [Fintype zIdx]
    (kRow : kIdx → ℝ) (zRow : zIdx → ℝ) (LK LZ : ℝ)
    (hK : dotProduct (star kRow) kRow ≤ LK ^ 2)
    (hZ : dotProduct (star zRow) zRow ≤ LZ ^ 2) :
    dotProduct (star (fun u : kIdx × zIdx => kRow u.1 * zRow u.2))
      (fun u : kIdx × zIdx => kRow u.1 * zRow u.2) ≤
      LK ^ 2 * LZ ^ 2 := by
  have hLKNonneg : 0 ≤ LK ^ 2 := by nlinarith
  have hMul :
      dotProduct (star kRow) kRow * dotProduct (star zRow) zRow ≤ LK ^ 2 * LZ ^ 2 := by
    exact mul_le_mul hK hZ (dotProduct_star_self_nonneg zRow) hLKNonneg
  calc
    dotProduct (star (fun u : kIdx × zIdx => kRow u.1 * zRow u.2))
        (fun u : kIdx × zIdx => kRow u.1 * zRow u.2)
      = dotProduct (star kRow) kRow * dotProduct (star zRow) zRow :=
        rowNormSq_kron_eq kRow zRow
    _ ≤ LK ^ 2 * LZ ^ 2 := hMul

/--
Derive the row-norm envelope needed by the `q`-scaled Gram bound from factorized rows.
-/
theorem rowNormSq_bound_of_factorized_rows
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
  intro p
  have hRowEq : (F p) = (fun u : kIdx × zIdx => kFeat p u.1 * zFeat p u.2) := by
    funext u
    exact hFactor p u.1 u.2
  rw [hRowEq]
  exact rowNormSq_kron_le_product_bounds (kFeat p) (zFeat p) LK LZ (hKBound p) (hZBound p)

/-- Feature row induced by observed left index `i_p` through matrix `K`. -/
def kFeatFromObs
    {obsIdx iIdx kIdx mIdx : Type*}
    (obs : obsIdx → iIdx × mIdx)
    (K : Matrix iIdx kIdx ℝ) :
    obsIdx → kIdx → ℝ :=
  fun p i => K (obs p).1 i

/-- Feature row induced by observed right index `m_p` through matrix `Z`. -/
def zFeatFromObs
    {obsIdx iIdx mIdx zIdx : Type*}
    (obs : obsIdx → iIdx × mIdx)
    (Z : Matrix mIdx zIdx ℝ) :
    obsIdx → zIdx → ℝ :=
  fun p j => Z (obs p).2 j

/-- Rank-1/Kronecker feature matrix built from observations and factor rows. -/
def factorizedFeatureMatrix
    {obsIdx iIdx mIdx kIdx zIdx : Type*}
    (obs : obsIdx → iIdx × mIdx)
    (K : Matrix iIdx kIdx ℝ)
    (Z : Matrix mIdx zIdx ℝ) :
    Matrix obsIdx (kIdx × zIdx) ℝ :=
  fun p u => K (obs p).1 u.1 * Z (obs p).2 u.2

theorem factorizedFeatureMatrix_factor
    {obsIdx iIdx mIdx kIdx zIdx : Type*}
    (obs : obsIdx → iIdx × mIdx)
    (K : Matrix iIdx kIdx ℝ)
    (Z : Matrix mIdx zIdx ℝ) :
    ∀ p : obsIdx, ∀ i : kIdx, ∀ j : zIdx,
      factorizedFeatureMatrix obs K Z p (i, j) =
        kFeatFromObs obs K p i * zFeatFromObs obs Z p j := by
  intro p i j
  rfl

theorem rowNormSq_bound_of_observed_factor_matrices
    {obsIdx iIdx mIdx kIdx zIdx : Type*}
    [Fintype obsIdx] [Fintype kIdx] [Fintype zIdx]
    (obs : obsIdx → iIdx × mIdx)
    (K : Matrix iIdx kIdx ℝ)
    (Z : Matrix mIdx zIdx ℝ)
    (LK LZ : ℝ)
    (hKRowBound : ∀ i : iIdx, dotProduct (star (K i)) (K i) ≤ LK ^ 2)
    (hZRowBound : ∀ m : mIdx, dotProduct (star (Z m)) (Z m) ≤ LZ ^ 2) :
    ∀ p : obsIdx,
      dotProduct (star ((factorizedFeatureMatrix obs K Z) p)) ((factorizedFeatureMatrix obs K Z) p) ≤
        LK ^ 2 * LZ ^ 2 := by
  have hKBound :
      ∀ p : obsIdx,
        dotProduct (star (kFeatFromObs obs K p)) (kFeatFromObs obs K p) ≤ LK ^ 2 := by
    intro p
    simpa [kFeatFromObs] using hKRowBound (obs p).1
  have hZBound :
      ∀ p : obsIdx,
        dotProduct (star (zFeatFromObs obs Z p)) (zFeatFromObs obs Z p) ≤ LZ ^ 2 := by
    intro p
    simpa [zFeatFromObs] using hZRowBound (obs p).2
  have hFactor :
      ∀ p : obsIdx, ∀ i : kIdx, ∀ j : zIdx,
        factorizedFeatureMatrix obs K Z p (i, j) =
          kFeatFromObs obs K p i * zFeatFromObs obs Z p j :=
    factorizedFeatureMatrix_factor obs K Z
  exact rowNormSq_bound_of_factorized_rows
    (F := factorizedFeatureMatrix obs K Z)
    (kFeat := kFeatFromObs obs K)
    (zFeat := zFeatFromObs obs Z)
    LK LZ hFactor hKBound hZBound

theorem gramMatrix_quad_upper_of_factorized_feature_bounds_q
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
  have hRowBound :
      ∀ p : Fin P.q, dotProduct (star (F p)) (F p) ≤ LK ^ 2 * LZ ^ 2 :=
    rowNormSq_bound_of_factorized_rows (F := F) kFeat zFeat LK LZ hFactor hKBound hZBound
  exact gramMatrix_quad_upper_of_feature_bounds_q (P := P) F LK LZ hRowBound

theorem gramMatrix_quad_upper_of_observed_factor_matrices_q
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
  have hRowBound :
      ∀ p : Fin P.q,
        dotProduct (star ((factorizedFeatureMatrix obs K Z) p))
          ((factorizedFeatureMatrix obs K Z) p) ≤ LK ^ 2 * LZ ^ 2 :=
    rowNormSq_bound_of_observed_factor_matrices (obs := obs) K Z LK LZ hKRowBound hZRowBound
  exact gramMatrix_quad_upper_of_feature_bounds_q
    (P := P) (factorizedFeatureMatrix obs K Z) LK LZ hRowBound

theorem regularizedNormalMatrix_quad_upper_of_feature_bounds_q
    (F : Matrix (Fin P.q) varIdx ℝ) (R : Matrix varIdx varIdx ℝ)
    (muMax LK LZ : ℝ)
    (hRowBound : ∀ p : Fin P.q, dotProduct (star (F p)) (F p) ≤ LK ^ 2 * LZ ^ 2)
    (hRUpper :
      ∀ x : varIdx → ℝ, dotProduct (star x) (R.mulVec x) ≤ muMax * dotProduct (star x) x) :
    ∀ x : varIdx → ℝ,
      dotProduct (star x) ((regularizedNormalMatrix F R P.lambda).mulVec x) ≤
        (((P.q : ℝ) * LK ^ 2 * LZ ^ 2) + P.lambda * muMax) * dotProduct (star x) x := by
  have hGramUpper :
      ∀ x : varIdx → ℝ,
        dotProduct (star x) ((gramMatrix F).mulVec x) ≤
          ((P.q : ℝ) * LK ^ 2 * LZ ^ 2) * dotProduct (star x) x :=
    gramMatrix_quad_upper_of_feature_bounds_q (P := P) F LK LZ hRowBound
  exact regularizedNormalMatrix_quad_upper (P := P) F R muMax LK LZ hGramUpper hRUpper

theorem regularizedNormalMatrix_eigenvalue_lower
    [DecidableEq varIdx]
    (F : Matrix obsIdx varIdx ℝ) {R : Matrix varIdx varIdx ℝ}
    (hRPos : R.PosDef) (muMin : ℝ)
    (hRLower :
      ∀ x : varIdx → ℝ, muMin * dotProduct (star x) x ≤ dotProduct (star x) (R.mulVec x))
    (i : varIdx) :
    P.lambda * muMin ≤
      (Matrix.PosDef.isHermitian (regularizedNormalMatrix_posDef F hRPos P.hlambda)).eigenvalues i := by
  have hQuad :
      ∀ x : varIdx → ℝ,
        (P.lambda * muMin) * dotProduct (star x) x ≤
          dotProduct (star x) ((regularizedNormalMatrix F R P.lambda).mulVec x) :=
    regularizedNormalMatrix_quad_lower (P := P) F R muMin hRLower
  exact eigenvalue_lower_of_quad_lower
    (A := regularizedNormalMatrix F R P.lambda)
    (hA := Matrix.PosDef.isHermitian (regularizedNormalMatrix_posDef F hRPos P.hlambda))
    (c := P.lambda * muMin) hQuad i

theorem regularizedNormalMatrix_eigenvalue_upper
    [DecidableEq varIdx]
    (F : Matrix obsIdx varIdx ℝ) {R : Matrix varIdx varIdx ℝ}
    (hRPos : R.PosDef) (muMax LK LZ : ℝ)
    (hGramUpper :
      ∀ x : varIdx → ℝ,
        dotProduct (star x) ((gramMatrix F).mulVec x) ≤
          ((P.q : ℝ) * LK ^ 2 * LZ ^ 2) * dotProduct (star x) x)
    (hRUpper :
      ∀ x : varIdx → ℝ, dotProduct (star x) (R.mulVec x) ≤ muMax * dotProduct (star x) x)
    (i : varIdx) :
    (Matrix.PosDef.isHermitian (regularizedNormalMatrix_posDef F hRPos P.hlambda)).eigenvalues i ≤
      ((P.q : ℝ) * LK ^ 2 * LZ ^ 2) + P.lambda * muMax := by
  have hQuad :
      ∀ x : varIdx → ℝ,
        dotProduct (star x) ((regularizedNormalMatrix F R P.lambda).mulVec x) ≤
          (((P.q : ℝ) * LK ^ 2 * LZ ^ 2) + P.lambda * muMax) * dotProduct (star x) x :=
    regularizedNormalMatrix_quad_upper (P := P) F R muMax LK LZ hGramUpper hRUpper
  exact eigenvalue_upper_of_quad_upper
    (A := regularizedNormalMatrix F R P.lambda)
    (hA := Matrix.PosDef.isHermitian (regularizedNormalMatrix_posDef F hRPos P.hlambda))
    (c := ((P.q : ℝ) * LK ^ 2 * LZ ^ 2) + P.lambda * muMax) hQuad i

theorem regularizedNormalMatrix_eigen_ratio_le_kappaUpperFromCount
    [DecidableEq varIdx]
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
  have hLower :
      P.lambda * muMin ≤
        (Matrix.PosDef.isHermitian (regularizedNormalMatrix_posDef F hRPos P.hlambda)).eigenvalues iMin :=
    regularizedNormalMatrix_eigenvalue_lower (P := P) F hRPos muMin hRLower iMin
  have hUpper :
      (Matrix.PosDef.isHermitian (regularizedNormalMatrix_posDef F hRPos P.hlambda)).eigenvalues iMax ≤
        ((P.q : ℝ) * LK ^ 2 * LZ ^ 2) + P.lambda * muMax :=
    regularizedNormalMatrix_eigenvalue_upper (P := P) F hRPos muMax LK LZ hGramUpper hRUpper iMax
  exact P.kappaFromExtremes_le_kappaUpperFromCount hmuMin hmuMax hLower hUpper

theorem regularizedNormalMatrix_eigen_ratio_le_kappaUpperFromDensity
    [DecidableEq varIdx]
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
  rw [P.kappaUpperFromDensity_eq_count muMin muMax LK LZ hM]
  exact regularizedNormalMatrix_eigen_ratio_le_kappaUpperFromCount
    (P := P) F hRPos muMin muMax LK LZ hmuMin hmuMax hGramUpper hRLower hRUpper iMax iMin

theorem regularizedNormalMatrix_quad_upper_of_factorized_feature_bounds_q
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
      ∀ x : (kIdx × zIdx) → ℝ,
        dotProduct (star x) (R.mulVec x) ≤ muMax * dotProduct (star x) x) :
    ∀ x : (kIdx × zIdx) → ℝ,
      dotProduct (star x) ((regularizedNormalMatrix F R P.lambda).mulVec x) ≤
        (((P.q : ℝ) * LK ^ 2 * LZ ^ 2) + P.lambda * muMax) * dotProduct (star x) x := by
  have hRowBound :
      ∀ p : Fin P.q, dotProduct (star (F p)) (F p) ≤ LK ^ 2 * LZ ^ 2 :=
    rowNormSq_bound_of_factorized_rows (F := F) kFeat zFeat LK LZ hFactor hKBound hZBound
  exact regularizedNormalMatrix_quad_upper_of_feature_bounds_q
    (P := P) F R muMax LK LZ hRowBound hRUpper

theorem regularizedNormalMatrix_eigen_ratio_le_kappaUpperFromCount_of_factorized_feature_bounds_q
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
  have hGramUpper :
      ∀ x : (kIdx × zIdx) → ℝ,
        dotProduct (star x) ((gramMatrix F).mulVec x) ≤
          ((P.q : ℝ) * LK ^ 2 * LZ ^ 2) * dotProduct (star x) x :=
    gramMatrix_quad_upper_of_factorized_feature_bounds_q (P := P) F kFeat zFeat LK LZ
      hFactor hKBound hZBound
  exact regularizedNormalMatrix_eigen_ratio_le_kappaUpperFromCount
    (P := P) F hRPos muMin muMax LK LZ hmuMin hmuMax hGramUpper hRLower hRUpper iMax iMin

theorem regularizedNormalMatrix_quad_upper_of_observed_factor_matrices_q
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
      ∀ x : (kIdx × zIdx) → ℝ,
        dotProduct (star x) (R.mulVec x) ≤ muMax * dotProduct (star x) x) :
    ∀ x : (kIdx × zIdx) → ℝ,
      dotProduct (star x)
          ((regularizedNormalMatrix (factorizedFeatureMatrix obs K Z) R P.lambda).mulVec x) ≤
        (((P.q : ℝ) * LK ^ 2 * LZ ^ 2) + P.lambda * muMax) * dotProduct (star x) x := by
  have hRowBound :
      ∀ p : Fin P.q,
        dotProduct (star ((factorizedFeatureMatrix obs K Z) p))
          ((factorizedFeatureMatrix obs K Z) p) ≤ LK ^ 2 * LZ ^ 2 :=
    rowNormSq_bound_of_observed_factor_matrices (obs := obs) K Z LK LZ hKRowBound hZRowBound
  exact regularizedNormalMatrix_quad_upper_of_feature_bounds_q
    (P := P) (factorizedFeatureMatrix obs K Z) R muMax LK LZ hRowBound hRUpper

theorem regularizedNormalMatrix_eigen_ratio_le_kappaUpperFromCount_of_observed_factor_matrices_q
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
  have hGramUpper :
      ∀ x : (kIdx × zIdx) → ℝ,
        dotProduct (star x) ((gramMatrix (factorizedFeatureMatrix obs K Z)).mulVec x) ≤
          ((P.q : ℝ) * LK ^ 2 * LZ ^ 2) * dotProduct (star x) x :=
    gramMatrix_quad_upper_of_observed_factor_matrices_q (P := P) obs K Z LK LZ hKRowBound hZRowBound
  exact regularizedNormalMatrix_eigen_ratio_le_kappaUpperFromCount
    (P := P) (factorizedFeatureMatrix obs K Z) hRPos muMin muMax LK LZ
    hmuMin hmuMax hGramUpper hRLower hRUpper iMax iMin

end MatrixLevel

/-- v2 iteration budget symbol `k_ε`. -/
def kEps (kappaP eps : ℝ) : Nat :=
  Nat.ceil
    (Real.log (2 / eps) /
      Real.log ((Real.sqrt kappaP + 1) / (Real.sqrt kappaP - 1)))

/-- PCG contraction factor expression `(sqrt κ - 1) / (sqrt κ + 1)`. -/
def pcgContractionFactor (kappaP : ℝ) : ℝ :=
  (Real.sqrt kappaP - 1) / (Real.sqrt kappaP + 1)

/-- Total arithmetic cost at target accuracy, using `k_ε` iterations. -/
def totalCostToAccuracy (kappaP eps : ℝ) : Nat :=
  P.totalCost (kEps kappaP eps)

theorem kEps_ge_log_ratio
    (kappaP eps : ℝ) :
    Real.log (2 / eps) / Real.log ((Real.sqrt kappaP + 1) / (Real.sqrt kappaP - 1)) ≤
      (kEps kappaP eps : ℝ) := by
  exact Nat.le_ceil _

theorem geometric_term_le_eps_of_kEps
    {kappaP eps : ℝ}
    (hkappa : 1 < kappaP)
    (heps0 : 0 < eps) :
    2 * (pcgContractionFactor kappaP) ^ (kEps kappaP eps) ≤ eps := by
  let r : ℝ := (Real.sqrt kappaP + 1) / (Real.sqrt kappaP - 1)
  let q : ℝ := pcgContractionFactor kappaP
  have hsqrtGtOne : 1 < Real.sqrt kappaP := by
    have hsqrt : Real.sqrt 1 < Real.sqrt kappaP := by
      exact Real.sqrt_lt_sqrt zero_le_one hkappa
    simpa using hsqrt
  have hsqrtSubPos : 0 < Real.sqrt kappaP - 1 := sub_pos.mpr hsqrtGtOne
  have hsqrtAddPos : 0 < Real.sqrt kappaP + 1 := by
    nlinarith [Real.sqrt_nonneg kappaP]
  have hqPos : 0 < q := by
    dsimp [q, ProblemData.pcgContractionFactor]
    exact div_pos hsqrtSubPos hsqrtAddPos
  have hqLeOne : q ≤ 1 := by
    dsimp [q, ProblemData.pcgContractionFactor]
    exact (div_le_iff₀ hsqrtAddPos).2 (by nlinarith)
  have hrGtOne : 1 < r := by
    dsimp [r]
    exact (one_lt_div hsqrtSubPos).2 (by nlinarith)
  have hlogrPos : 0 < Real.log r := Real.log_pos hrGtOne
  have hkR :
      Real.log (2 / eps) / Real.log r ≤ (kEps kappaP eps : ℝ) := by
    simpa [ProblemData.kEps, r] using (Nat.le_ceil (Real.log (2 / eps) / Real.log r))
  have hlogq : Real.log q = -Real.log r := by
    have hqInv : q = r⁻¹ := by
      dsimp [q, r, ProblemData.pcgContractionFactor]
      field_simp [hsqrtSubPos.ne', hsqrtAddPos.ne']
    rw [hqInv, Real.log_inv]
  have hkMul :
      (kEps kappaP eps : ℝ) * Real.log q ≤
        (Real.log (2 / eps) / Real.log r) * Real.log q := by
    have hlogqNonpos : Real.log q ≤ 0 := Real.log_nonpos hqPos.le hqLeOne
    exact mul_le_mul_of_nonpos_right hkR hlogqNonpos
  have hratioLog :
      (Real.log (2 / eps) / Real.log r) * Real.log q = Real.log (eps / 2) := by
    have hstep :
        (Real.log (2 / eps) / Real.log r) * Real.log q = -Real.log (2 / eps) := by
      calc
        (Real.log (2 / eps) / Real.log r) * Real.log q
            = (Real.log (2 / eps) / Real.log r) * (-Real.log r) := by rw [hlogq]
        _ = -((Real.log (2 / eps) / Real.log r) * Real.log r) := by ring
        _ = -Real.log (2 / eps) := by
          field_simp [hlogrPos.ne']
    have hdivInv : (2 / eps)⁻¹ = eps / 2 := by
      field_simp [heps0.ne']
    calc
      (Real.log (2 / eps) / Real.log r) * Real.log q = -Real.log (2 / eps) := hstep
      _ = Real.log ((2 / eps)⁻¹) := by symm; exact Real.log_inv (2 / eps)
      _ = Real.log (eps / 2) := by simp [hdivInv]
  have hkLog :
      (kEps kappaP eps : ℝ) * Real.log q ≤ Real.log (eps / 2) := by
    calc
      (kEps kappaP eps : ℝ) * Real.log q ≤
          (Real.log (2 / eps) / Real.log r) * Real.log q := hkMul
      _ = Real.log (eps / 2) := hratioLog
  have hepsHalfPos : 0 < eps / 2 := by
    exact div_pos heps0 (by norm_num)
  have hpowLe : q ^ (kEps kappaP eps) ≤ eps / 2 := by
    exact (Real.pow_le_iff_le_log hqPos hepsHalfPos).2 (by simpa using hkLog)
  have hmul :
      2 * q ^ (kEps kappaP eps) ≤ 2 * (eps / 2) := by
    exact mul_le_mul_of_nonneg_left hpowLe (by norm_num)
  have hfinal : 2 * q ^ (kEps kappaP eps) ≤ eps := by
    calc
      2 * q ^ (kEps kappaP eps) ≤ 2 * (eps / 2) := hmul
      _ = eps := by ring
  simpa [q] using hfinal

theorem totalCostToAccuracy_eq
    (kappaP eps : ℝ) :
    P.totalCostToAccuracy kappaP eps = kEps kappaP eps * P.costPCGIter := by
  rfl

theorem totalCostToAccuracy_formula
    (kappaP eps : ℝ) :
    P.totalCostToAccuracy kappaP eps =
      kEps kappaP eps *
        (P.q * (2 * P.r + P.n * P.r) + P.n * P.n * P.r + P.n * P.n * P.r +
          6 * (P.n * P.r)) := by
  simp [ProblemData.totalCostToAccuracy, ProblemData.totalCost, P.costPCGIter_eq]

theorem totalCostToAccuracy_le_totalCost
    {kappaP eps : ℝ}
    {k : Nat}
    (hk : kEps kappaP eps ≤ k) :
    P.totalCostToAccuracy kappaP eps ≤ P.totalCost k := by
  simpa [ProblemData.totalCostToAccuracy] using P.totalCost_mono hk

theorem error_bound_at_kEps_of_assumptions
    {err0 : ℝ} {err : Nat → ℝ}
    (kappaP eps : ℝ)
    (hContract :
      ∀ k : Nat, err k ≤ 2 * (pcgContractionFactor kappaP) ^ k * err0)
    (hGeometricAtBudget :
      2 * (pcgContractionFactor kappaP) ^ (kEps kappaP eps) ≤ eps)
    (herr0 : 0 ≤ err0) :
    err (kEps kappaP eps) ≤ eps * err0 := by
  have hAtBudget : err (kEps kappaP eps) ≤
      2 * (pcgContractionFactor kappaP) ^ (kEps kappaP eps) * err0 :=
    hContract (kEps kappaP eps)
  have hScale :
      2 * (pcgContractionFactor kappaP) ^ (kEps kappaP eps) * err0 ≤ eps * err0 := by
    exact mul_le_mul_of_nonneg_right hGeometricAtBudget herr0
  exact le_trans hAtBudget hScale

theorem error_bound_at_kEps
    {err0 : ℝ} {err : Nat → ℝ}
    (kappaP eps : ℝ)
    (hkappa : 1 < kappaP)
    (heps0 : 0 < eps)
    (hContract :
      ∀ k : Nat, err k ≤ 2 * (pcgContractionFactor kappaP) ^ k * err0)
    (herr0 : 0 ≤ err0) :
    err (kEps kappaP eps) ≤ eps * err0 := by
  exact error_bound_at_kEps_of_assumptions kappaP eps hContract
    (geometric_term_le_eps_of_kEps hkappa heps0) herr0

end
end ProblemData
end Question10
