import Question9.Main

namespace Question9

/-!
`PureInputFamily` isolates a pure-input characterization layer:
the map is fixed on `InputVector n` and never uses `extractLambdaFromInput`.

For the concrete choice `swapZeroMapFin`, reverse implication is already
available from `BridgeRecoverability`. We add a forward-completeness
assumption and obtain a full `↔` package.
-/

def SwapZeroForwardCompleteness
    (n : Nat)
    (hn : 5 ≤ n) : Prop :=
  ∀ A : CameraMatrices n, ∀ lam : Lambda n,
    separable lam →
      ∀ t : Fin (Fintype.card (SwapZeroIndex n)),
        swapZeroMapFin n hn (scaleInput lam (QInput A)) t = 0

theorem swapZeroMapFin_zero_iff_separable_of_bridgeRecoverability_and_forward
    {n : Nat}
    (hn : 5 ≤ n)
    (R : BridgeRecoverability n)
    (hForward : SwapZeroForwardCompleteness n hn)
    (A : CameraMatrices n)
    (lam : Lambda n)
    (hNZ : nonzeroOnValid lam)
    (hGeneric : IsGenericStrong A) :
    (∀ t : Fin (Fintype.card (SwapZeroIndex n)),
      swapZeroMapFin n hn (scaleInput lam (QInput A)) t = 0) ↔ separable lam := by
  constructor
  · intro hZero
    exact separable_of_swapZeroMapFin_zero_of_bridgeRecoverability
      R hn A lam hNZ hGeneric hZero
  · intro hSep
    exact hForward A lam hSep

theorem swapZeroMapFin_zero_iff_separable_of_bridgeExtractors_and_forward
    {n : Nat}
    (hn : 5 ≤ n)
    (E : BridgeExtractors n)
    (hForward : SwapZeroForwardCompleteness n hn)
    (A : CameraMatrices n)
    (lam : Lambda n)
    (hNZ : nonzeroOnValid lam)
    (hGeneric : IsGenericStrong A) :
    (∀ t : Fin (Fintype.card (SwapZeroIndex n)),
      swapZeroMapFin n hn (scaleInput lam (QInput A)) t = 0) ↔ separable lam := by
  exact swapZeroMapFin_zero_iff_separable_of_bridgeRecoverability_and_forward
    hn (bridgeRecoverability_of_bridgeExtractors E) hForward A lam hNZ hGeneric

theorem swapZeroMapFin_zero_iff_separable_of_permutedHExtractors_and_forward
    {n : Nat}
    (hn : 5 ≤ n)
    (E : PermutedHExtractors n)
    (hForward : SwapZeroForwardCompleteness n hn)
    (A : CameraMatrices n)
    (lam : Lambda n)
    (hNZ : nonzeroOnValid lam)
    (hGeneric : IsGenericStrong A) :
    (∀ t : Fin (Fintype.card (SwapZeroIndex n)),
      swapZeroMapFin n hn (scaleInput lam (QInput A)) t = 0) ↔ separable lam := by
  exact swapZeroMapFin_zero_iff_separable_of_bridgeExtractors_and_forward
    hn E.toBridgeExtractors hForward A lam hNZ hGeneric

theorem exists_question_solution_of_swapZeroMapFin_under_assumptions
    {n : Nat}
    (hn : 5 ≤ n)
    (R : BridgeRecoverability n)
    (hForward : SwapZeroForwardCompleteness n hn) :
    ∃ m : Nat, ∃ F : InputVector n → (Fin m → ℝ),
      (pluckerCoordinateDegree = 2) ∧
      (∀ A : CameraMatrices n, ∀ lam : Lambda n, nonzeroOnValid lam →
        IsGenericStrong A →
          ((∀ t, F (scaleInput lam (QInput A)) t = 0) ↔ separable lam)) := by
  refine ⟨Fintype.card (SwapZeroIndex n), swapZeroMapFin n hn, pluckerCoordinateDegree_eq, ?_⟩
  intro A lam hNZ hGeneric
  exact swapZeroMapFin_zero_iff_separable_of_bridgeRecoverability_and_forward
    hn R hForward A lam hNZ hGeneric

theorem exists_question_solution_of_swapZeroMapFin_of_bridgeExtractors_under_forward
    {n : Nat}
    (hn : 5 ≤ n)
    (E : BridgeExtractors n)
    (hForward : SwapZeroForwardCompleteness n hn) :
    ∃ m : Nat, ∃ F : InputVector n → (Fin m → ℝ),
      (pluckerCoordinateDegree = 2) ∧
      (∀ A : CameraMatrices n, ∀ lam : Lambda n, nonzeroOnValid lam →
        IsGenericStrong A →
          ((∀ t, F (scaleInput lam (QInput A)) t = 0) ↔ separable lam)) := by
  exact exists_question_solution_of_swapZeroMapFin_under_assumptions
    hn (bridgeRecoverability_of_bridgeExtractors E) hForward

theorem exists_question_solution_of_swapZeroMapFin_of_permutedHExtractors_under_forward
    {n : Nat}
    (hn : 5 ≤ n)
    (E : PermutedHExtractors n)
    (hForward : SwapZeroForwardCompleteness n hn) :
    ∃ m : Nat, ∃ F : InputVector n → (Fin m → ℝ),
      (pluckerCoordinateDegree = 2) ∧
      (∀ A : CameraMatrices n, ∀ lam : Lambda n, nonzeroOnValid lam →
        IsGenericStrong A →
          ((∀ t, F (scaleInput lam (QInput A)) t = 0) ↔ separable lam)) := by
  exact exists_question_solution_of_swapZeroMapFin_of_bridgeExtractors_under_forward
    hn E.toBridgeExtractors hForward

end Question9

