import Question9.NormalizedInputFamily

namespace Question9

noncomputable section

def anchorY {n : Nat} (Y : InputVector n) (a b c d : Idx n) : ℝ :=
  Y (anchorQIndex a b c d)

noncomputable def anchorQ {n : Nat} (A : CameraMatrices n) (a b c d : Idx n) : ℝ :=
  QInput A (anchorQIndex a b c d)

noncomputable def qProdWithAnchors
    {n : Nat}
    (S : Anchors n)
    (A : CameraMatrices n) :
    HConditionIndex n → ℝ
  | .h1 q =>
      anchorQ A (ValidQuad.a q) (ValidQuad.b q) (ValidQuad.c q) (ValidQuad.d q)
        * anchorQ A S.a0 S.b0 S.c0 S.d0
        * anchorQ A (ValidQuad.a q) (ValidQuad.b q) S.c0 S.d0
        * anchorQ A S.a0 S.b0 (ValidQuad.c q) (ValidQuad.d q)
  | .h2 a b =>
      anchorQ A a b S.c0 S.d0
        * anchorQ A S.a0 S.b0 S.c0 S.d0
        * anchorQ A a S.b0 S.c0 S.d0
        * anchorQ A S.a0 b S.c0 S.d0
  | .h3 c d =>
      anchorQ A S.a0 S.b0 c d
        * anchorQ A S.a0 S.b0 S.c0 S.d0
        * anchorQ A S.a0 S.b0 c S.d0
        * anchorQ A S.a0 S.b0 S.c0 d

noncomputable def hConditionResidualPolyWithAnchors
    {n : Nat}
    (S : Anchors n)
    (A : CameraMatrices n)
    (Y : InputVector n) :
    HConditionIndex n → ℝ
  | .h1 q =>
      (anchorY Y (ValidQuad.a q) (ValidQuad.b q) (ValidQuad.c q) (ValidQuad.d q)
          * anchorY Y S.a0 S.b0 S.c0 S.d0)
        * (anchorQ A (ValidQuad.a q) (ValidQuad.b q) S.c0 S.d0
            * anchorQ A S.a0 S.b0 (ValidQuad.c q) (ValidQuad.d q))
        -
        (anchorY Y (ValidQuad.a q) (ValidQuad.b q) S.c0 S.d0
          * anchorY Y S.a0 S.b0 (ValidQuad.c q) (ValidQuad.d q))
        * (anchorQ A (ValidQuad.a q) (ValidQuad.b q) (ValidQuad.c q) (ValidQuad.d q)
            * anchorQ A S.a0 S.b0 S.c0 S.d0)
  | .h2 a b =>
      (anchorY Y a b S.c0 S.d0 * anchorY Y S.a0 S.b0 S.c0 S.d0)
        * (anchorQ A a S.b0 S.c0 S.d0 * anchorQ A S.a0 b S.c0 S.d0)
        -
        (anchorY Y a S.b0 S.c0 S.d0 * anchorY Y S.a0 b S.c0 S.d0)
        * (anchorQ A a b S.c0 S.d0 * anchorQ A S.a0 S.b0 S.c0 S.d0)
  | .h3 c d =>
      (anchorY Y S.a0 S.b0 c d * anchorY Y S.a0 S.b0 S.c0 S.d0)
        * (anchorQ A S.a0 S.b0 c S.d0 * anchorQ A S.a0 S.b0 S.c0 d)
        -
        (anchorY Y S.a0 S.b0 c S.d0 * anchorY Y S.a0 S.b0 S.c0 d)
        * (anchorQ A S.a0 S.b0 c d * anchorQ A S.a0 S.b0 S.c0 S.d0)

theorem hConditionResidualPolyWithAnchors_scaled
    {n : Nat}
    (S : Anchors n)
    (A : CameraMatrices n)
    (lam : Lambda n) :
    ∀ idx : HConditionIndex n,
      hConditionResidualPolyWithAnchors S A (scaleInput lam (QInput A)) idx =
        qProdWithAnchors S A idx * hConditionResidualWithAnchors S lam idx := by
  intro idx
  cases idx with
  | h1 q =>
      simp [hConditionResidualPolyWithAnchors, qProdWithAnchors, hConditionResidualWithAnchors,
        anchorY, anchorQ, scaleInput, anchorQIndex]
      ring_nf
  | h2 a b =>
      simp [hConditionResidualPolyWithAnchors, qProdWithAnchors, hConditionResidualWithAnchors,
        anchorY, anchorQ, scaleInput, anchorQIndex]
      ring_nf
  | h3 c d =>
      simp [hConditionResidualPolyWithAnchors, qProdWithAnchors, hConditionResidualWithAnchors,
        anchorY, anchorQ, scaleInput, anchorQIndex]
      ring_nf

theorem qProdWithAnchors_ne_zero_of_genericStrong
    {n : Nat}
    (S : Anchors n)
    (A : CameraMatrices n)
    (hGeneric : IsGenericStrong A) :
    ∀ idx : HConditionIndex n, qProdWithAnchors S A idx ≠ 0 := by
  intro idx
  cases idx with
  | h1 q =>
      have hq1 :
          anchorQ A (ValidQuad.a q) (ValidQuad.b q) (ValidQuad.c q) (ValidQuad.d q) ≠ 0 := by
        exact qInput_nonzero_of_isGenericStrong A hGeneric
          (anchorQIndex (ValidQuad.a q) (ValidQuad.b q) (ValidQuad.c q) (ValidQuad.d q))
          (ValidQuad.hvalid q)
      have hq0 :
          anchorQ A S.a0 S.b0 S.c0 S.d0 ≠ 0 := by
        exact qInput_nonzero_of_isGenericStrong A hGeneric
          (anchorQIndex S.a0 S.b0 S.c0 S.d0)
          S.valid_anchor
      have hvalid2 : valid (ValidQuad.a q) (ValidQuad.b q) S.c0 S.d0 := by
        intro hall
        exact S.hcd hall.2.2
      have hq2 :
          anchorQ A (ValidQuad.a q) (ValidQuad.b q) S.c0 S.d0 ≠ 0 := by
        exact qInput_nonzero_of_isGenericStrong A hGeneric
          (anchorQIndex (ValidQuad.a q) (ValidQuad.b q) S.c0 S.d0)
          hvalid2
      have hvalid3 : valid S.a0 S.b0 (ValidQuad.c q) (ValidQuad.d q) := by
        intro hall
        exact S.hab hall.1
      have hq3 :
          anchorQ A S.a0 S.b0 (ValidQuad.c q) (ValidQuad.d q) ≠ 0 := by
        exact qInput_nonzero_of_isGenericStrong A hGeneric
          (anchorQIndex S.a0 S.b0 (ValidQuad.c q) (ValidQuad.d q))
          hvalid3
      have h10 : anchorQ A (ValidQuad.a q) (ValidQuad.b q) (ValidQuad.c q) (ValidQuad.d q)
          * anchorQ A S.a0 S.b0 S.c0 S.d0 ≠ 0 := mul_ne_zero hq1 hq0
      have h102 : anchorQ A (ValidQuad.a q) (ValidQuad.b q) (ValidQuad.c q) (ValidQuad.d q)
          * anchorQ A S.a0 S.b0 S.c0 S.d0
          * anchorQ A (ValidQuad.a q) (ValidQuad.b q) S.c0 S.d0 ≠ 0 := mul_ne_zero h10 hq2
      have h1023 :
          anchorQ A (ValidQuad.a q) (ValidQuad.b q) (ValidQuad.c q) (ValidQuad.d q)
            * anchorQ A S.a0 S.b0 S.c0 S.d0
            * anchorQ A (ValidQuad.a q) (ValidQuad.b q) S.c0 S.d0
            * anchorQ A S.a0 S.b0 (ValidQuad.c q) (ValidQuad.d q) ≠ 0 := mul_ne_zero h102 hq3
      simpa [qProdWithAnchors] using h1023
  | h2 a b =>
      have hq1 : anchorQ A a b S.c0 S.d0 ≠ 0 := by
        have hvalid : valid a b S.c0 S.d0 := by
          intro hall
          exact S.hcd hall.2.2
        exact qInput_nonzero_of_isGenericStrong A hGeneric (anchorQIndex a b S.c0 S.d0) hvalid
      have hq0 : anchorQ A S.a0 S.b0 S.c0 S.d0 ≠ 0 := by
        exact qInput_nonzero_of_isGenericStrong A hGeneric (anchorQIndex S.a0 S.b0 S.c0 S.d0)
          S.valid_anchor
      have hq2 : anchorQ A a S.b0 S.c0 S.d0 ≠ 0 := by
        exact qInput_nonzero_of_isGenericStrong A hGeneric (anchorQIndex a S.b0 S.c0 S.d0)
          (S.valid_a_slice a)
      have hq3 : anchorQ A S.a0 b S.c0 S.d0 ≠ 0 := by
        exact qInput_nonzero_of_isGenericStrong A hGeneric (anchorQIndex S.a0 b S.c0 S.d0)
          (S.valid_b_slice b)
      have h10 : anchorQ A a b S.c0 S.d0 * anchorQ A S.a0 S.b0 S.c0 S.d0 ≠ 0 :=
        mul_ne_zero hq1 hq0
      have h102 :
          anchorQ A a b S.c0 S.d0 * anchorQ A S.a0 S.b0 S.c0 S.d0
            * anchorQ A a S.b0 S.c0 S.d0 ≠ 0 := mul_ne_zero h10 hq2
      have h1023 :
          anchorQ A a b S.c0 S.d0 * anchorQ A S.a0 S.b0 S.c0 S.d0
            * anchorQ A a S.b0 S.c0 S.d0 * anchorQ A S.a0 b S.c0 S.d0 ≠ 0 :=
        mul_ne_zero h102 hq3
      simpa [qProdWithAnchors] using h1023
  | h3 c d =>
      have hq1 : anchorQ A S.a0 S.b0 c d ≠ 0 := by
        have hvalid : valid S.a0 S.b0 c d := by
          intro hall
          exact S.hab hall.1
        exact qInput_nonzero_of_isGenericStrong A hGeneric (anchorQIndex S.a0 S.b0 c d) hvalid
      have hq0 : anchorQ A S.a0 S.b0 S.c0 S.d0 ≠ 0 := by
        exact qInput_nonzero_of_isGenericStrong A hGeneric (anchorQIndex S.a0 S.b0 S.c0 S.d0)
          S.valid_anchor
      have hq2 : anchorQ A S.a0 S.b0 c S.d0 ≠ 0 := by
        exact qInput_nonzero_of_isGenericStrong A hGeneric (anchorQIndex S.a0 S.b0 c S.d0)
          (S.valid_c_slice c)
      have hq3 : anchorQ A S.a0 S.b0 S.c0 d ≠ 0 := by
        exact qInput_nonzero_of_isGenericStrong A hGeneric (anchorQIndex S.a0 S.b0 S.c0 d)
          (S.valid_d_slice d)
      have h10 : anchorQ A S.a0 S.b0 c d * anchorQ A S.a0 S.b0 S.c0 S.d0 ≠ 0 :=
        mul_ne_zero hq1 hq0
      have h102 :
          anchorQ A S.a0 S.b0 c d * anchorQ A S.a0 S.b0 S.c0 S.d0
            * anchorQ A S.a0 S.b0 c S.d0 ≠ 0 := mul_ne_zero h10 hq2
      have h1023 :
          anchorQ A S.a0 S.b0 c d * anchorQ A S.a0 S.b0 S.c0 S.d0
            * anchorQ A S.a0 S.b0 c S.d0 * anchorQ A S.a0 S.b0 S.c0 d ≠ 0 :=
        mul_ne_zero h102 hq3
      simpa [qProdWithAnchors] using h1023

noncomputable def cameraNormalizedHPolyFin
    (n : Nat)
    (hn : 5 ≤ n)
    (A : CameraMatrices n) :
    InputVector n → (Fin (Fintype.card (HConditionIndex n)) → ℝ) :=
  fun Y t =>
    hConditionResidualPolyWithAnchors (canonicalAnchors n hn) A Y
      ((Fintype.equivFin (HConditionIndex n)).symm t)

def cameraNormalizedHPolyCoordinateDegree : Nat := 4

theorem cameraNormalizedHPolyCoordinateDegree_eq : cameraNormalizedHPolyCoordinateDegree = 4 := rfl

theorem cameraNormalizedHPolyFin_scaled_iff_separable_of_genericStrong
    {n : Nat}
    (hn : 5 ≤ n)
    (A : CameraMatrices n)
    (lam : Lambda n)
    (hGeneric : IsGenericStrong A)
    (hLamNZ : nonzeroOnValid lam) :
    (∀ t, cameraNormalizedHPolyFin n hn A (scaleInput lam (QInput A)) t = 0) ↔
      separable lam := by
  let S : Anchors n := canonicalAnchors n hn
  constructor
  · intro hZero
    have hZeroIdx :
        ∀ idx : HConditionIndex n,
          hConditionResidualPolyWithAnchors S A (scaleInput lam (QInput A)) idx = 0 := by
      intro idx
      have hz := hZero ((Fintype.equivFin (HConditionIndex n)) idx)
      simpa [cameraNormalizedHPolyFin, S] using hz
    have hLamZero :
        ∀ idx : HConditionIndex n, hConditionResidualWithAnchors S lam idx = 0 := by
      intro idx
      have hEq := hConditionResidualPolyWithAnchors_scaled S A lam idx
      have hprod : qProdWithAnchors S A idx ≠ 0 :=
        qProdWithAnchors_ne_zero_of_genericStrong S A hGeneric idx
      have hz : qProdWithAnchors S A idx * hConditionResidualWithAnchors S lam idx = 0 := by
        -- rewrite the zero hypothesis using the scaling identity
        simpa [hEq] using hZeroIdx idx
      exact (mul_eq_zero.mp hz).resolve_left hprod
    exact (hConditionResidual_zero_iff_separable S lam hLamNZ).1 hLamZero
  · intro hSep t
    have hLamZero :
        ∀ idx : HConditionIndex n, hConditionResidualWithAnchors S lam idx = 0 := by
      exact (hConditionResidual_zero_iff_separable S lam hLamNZ).2 hSep
    let idx : HConditionIndex n := (Fintype.equivFin (HConditionIndex n)).symm t
    have hEq := hConditionResidualPolyWithAnchors_scaled S A lam idx
    have hz : qProdWithAnchors S A idx * hConditionResidualWithAnchors S lam idx = 0 := by
      simp [hLamZero idx]
    -- convert back to the poly residual coordinate
    simpa [cameraNormalizedHPolyFin, S, idx, hEq] using hz

theorem exists_cameraNormalizedHPolyFin_solution
    {n : Nat}
    (hn : 5 ≤ n) :
    ∃ m : Nat, ∃ F : CameraMatrices n → InputVector n → (Fin m → ℝ),
      (cameraNormalizedHPolyCoordinateDegree = 4) ∧
      (∀ A : CameraMatrices n, ∀ lam : Lambda n, nonzeroOnValid lam →
        IsGenericStrong A →
          ((∀ t, F A (scaleInput lam (QInput A)) t = 0) ↔ separable lam)) := by
  refine ⟨Fintype.card (HConditionIndex n), cameraNormalizedHPolyFin n hn,
    cameraNormalizedHPolyCoordinateDegree_eq, ?_⟩
  intro A lam hLamNZ hGeneric
  exact cameraNormalizedHPolyFin_scaled_iff_separable_of_genericStrong hn A lam hGeneric hLamNZ

end

end Question9
