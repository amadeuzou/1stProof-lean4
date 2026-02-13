import Question9.HFamily

namespace Question9

theorem separable_congr_valid
    {n : Nat}
    {lam₁ lam₂ : Lambda n}
    (hEq : ∀ a b c d, valid a b c d → lam₁ a b c d = lam₂ a b c d) :
    separable lam₁ ↔ separable lam₂ := by
  constructor
  · intro hSep
    rcases hSep with ⟨u, v, w, x, hu, hv, hw, hx, hform⟩
    refine ⟨u, v, w, x, hu, hv, hw, hx, ?_⟩
    intro a b c d hvalid
    calc
      lam₂ a b c d = lam₁ a b c d := (hEq a b c d hvalid).symm
      _ = u a * v b * w c * x d := hform a b c d hvalid
  · intro hSep
    rcases hSep with ⟨u, v, w, x, hu, hv, hw, hx, hform⟩
    refine ⟨u, v, w, x, hu, hv, hw, hx, ?_⟩
    intro a b c d hvalid
    calc
      lam₁ a b c d = lam₂ a b c d := hEq a b c d hvalid
      _ = u a * v b * w c * x d := hform a b c d hvalid

noncomputable def cameraNormalizedHMapFin
    (n : Nat)
    (hn : 5 ≤ n)
    (A : CameraMatrices n) :
    InputVector n → (Fin (Fintype.card (HConditionIndex n)) → ℝ) :=
  fun Y => hConditionResidualFin n hn (extractLambdaFromInput (QInput A) Y)

theorem cameraNormalizedHMapFin_zero_iff_separable_extract_of_genericStrong
    {n : Nat}
    (hn : 5 ≤ n)
    (A : CameraMatrices n)
    (Y : InputVector n)
    (lam : Lambda n)
    (hScale : isScaledInput Y lam (QInput A))
    (hGeneric : IsGenericStrong A)
    (hLamNZ : nonzeroOnValid lam) :
    (∀ t, cameraNormalizedHMapFin n hn A Y t = 0) ↔
      separable (extractLambdaFromInput (QInput A) Y) := by
  simpa [cameraNormalizedHMapFin] using
    concrete_hConditionResidualFin_characterization_of_genericStrong
      hn A Y lam hScale hGeneric hLamNZ

theorem cameraNormalizedHMapFin_scaled_iff_separable_of_genericStrong
    {n : Nat}
    (hn : 5 ≤ n)
    (A : CameraMatrices n)
    (lam : Lambda n)
    (hGeneric : IsGenericStrong A)
    (hLamNZ : nonzeroOnValid lam) :
    (∀ t, cameraNormalizedHMapFin n hn A (scaleInput lam (QInput A)) t = 0) ↔
      separable lam := by
  have hScale : isScaledInput (scaleInput lam (QInput A)) lam (QInput A) := by
    intro idx hvalid
    rfl
  have hiffExtract :
      (∀ t, cameraNormalizedHMapFin n hn A (scaleInput lam (QInput A)) t = 0) ↔
        separable (extractLambdaFromInput (QInput A) (scaleInput lam (QInput A))) := by
    exact cameraNormalizedHMapFin_zero_iff_separable_extract_of_genericStrong
      hn A (scaleInput lam (QInput A)) lam hScale hGeneric hLamNZ
  have hQNZ : ∀ a b c d, valid a b c d → QInput A (anchorQIndex a b c d) ≠ 0 := by
    exact anchor_nonzero_of_isGeneric A (isGenericStrong_implies_isGeneric A hGeneric)
  have hEq :
      ∀ a b c d, valid a b c d →
        extractLambdaFromInput (QInput A) (scaleInput lam (QInput A)) a b c d = lam a b c d := by
    exact extractLambdaFromInput_eq (QInput A) (scaleInput lam (QInput A)) lam hScale hQNZ
  exact hiffExtract.trans (separable_congr_valid hEq)

theorem exists_cameraNormalizedHMapFin_solution
    {n : Nat}
    (hn : 5 ≤ n) :
    ∃ m : Nat, ∃ F : CameraMatrices n → InputVector n → (Fin m → ℝ),
      (hConditionCoordinateDegree = 2) ∧
      (∀ A : CameraMatrices n, ∀ lam : Lambda n, nonzeroOnValid lam →
        IsGenericStrong A →
          ((∀ t, F A (scaleInput lam (QInput A)) t = 0) ↔ separable lam)) := by
  refine ⟨Fintype.card (HConditionIndex n), cameraNormalizedHMapFin n hn, hConditionCoordinateDegree_eq, ?_⟩
  intro A lam hLamNZ hGeneric
  exact cameraNormalizedHMapFin_scaled_iff_separable_of_genericStrong hn A lam hGeneric hLamNZ

end Question9

