import Question9.PureInputFamily

namespace Question9

abbrev LambdaInt (n : Nat) := Idx n → Idx n → Idx n → Idx n → ℤ

def i0_5 : Idx 5 := ⟨0, by decide⟩
def i1_5 : Idx 5 := ⟨1, by decide⟩
def i2_5 : Idx 5 := ⟨2, by decide⟩
def i3_5 : Idx 5 := ⟨3, by decide⟩
def i4_5 : Idx 5 := ⟨4, by decide⟩

def specialSupport5 (a b c d : Idx 5) : Bool :=
  (a = i0_5 && b = i1_5 && c = i2_5 && d = i3_5) ||
  (a = i0_5 && b = i1_5 && c = i3_5 && d = i2_5) ||
  (a = i1_5 && b = i0_5 && c = i2_5 && d = i3_5) ||
  (a = i2_5 && b = i0_5 && c = i1_5 && d = i3_5) ||
  (a = i2_5 && b = i1_5 && c = i0_5 && d = i3_5) ||
  (a = i3_5 && b = i1_5 && c = i0_5 && d = i2_5)

def counterLam5 : LambdaInt 5 :=
  fun a b c d => if specialSupport5 a b c d then (-1) else 1

def anchors5 : Anchors 5 := canonicalAnchors 5 (by decide)

instance (a b c d : Idx 5) : Decidable (valid a b c d) := by
  unfold valid
  infer_instance

structure SwapBalanceConditionInt (S : Anchors 5) (lam : LambdaInt 5) : Prop where
  h1Bal1 :
    ∀ a b c d, valid a b c d →
      lam a b c d * lam S.a0 S.b0 S.c0 S.d0 =
        lam c b a d * lam S.c0 S.b0 S.a0 S.d0
  h1Bal2 :
    ∀ a b c d, valid a b c d →
      lam a b S.c0 S.d0 * lam S.a0 S.b0 c d =
        lam S.c0 b a S.d0 * lam c S.b0 S.a0 d
  h2Bal1 :
    ∀ a b,
      lam a b S.c0 S.d0 * lam S.a0 S.b0 S.c0 S.d0 =
        lam b a S.c0 S.d0 * lam S.b0 S.a0 S.c0 S.d0
  h2Bal2 :
    ∀ a b,
      lam a S.b0 S.c0 S.d0 * lam S.a0 b S.c0 S.d0 =
        lam S.b0 a S.c0 S.d0 * lam b S.a0 S.c0 S.d0
  h3Bal1 :
    ∀ c d,
      lam S.a0 S.b0 c d * lam S.a0 S.b0 S.c0 S.d0 =
        lam S.a0 S.b0 d c * lam S.a0 S.b0 S.d0 S.c0
  h3Bal2 :
    ∀ c d,
      lam S.a0 S.b0 c S.d0 * lam S.a0 S.b0 S.c0 d =
        lam S.a0 S.b0 S.d0 c * lam S.a0 S.b0 d S.c0

structure BridgeConditionSetInt (S : Anchors 5) (lam : LambdaInt 5) : Prop where
  bridge1 :
    ∀ a b c d, valid a b c d →
      lam c b a d * lam S.c0 S.b0 S.a0 S.d0 =
        lam S.c0 b a S.d0 * lam c S.b0 S.a0 d
  bridge2 :
    ∀ a b,
      lam b a S.c0 S.d0 * lam S.b0 S.a0 S.c0 S.d0 =
        lam S.b0 a S.c0 S.d0 * lam b S.a0 S.c0 S.d0
  bridge3 :
    ∀ c d,
      lam S.a0 S.b0 d c * lam S.a0 S.b0 S.d0 S.c0 =
        lam S.a0 S.b0 S.d0 c * lam S.a0 S.b0 d S.c0

theorem counterLam5_satisfies_swapBalances :
    SwapBalanceConditionInt anchors5 counterLam5 := by
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩ <;> native_decide

theorem counterLam5_not_bridge :
    ¬ BridgeConditionSetInt anchors5 counterLam5 := by
  intro hBridge
  have hvalid : valid i0_5 i0_5 i0_5 i1_5 := by native_decide
  have hEq := hBridge.bridge1 i0_5 i0_5 i0_5 i1_5 hvalid
  have hNe :
      counterLam5 i0_5 i0_5 i0_5 i1_5 * counterLam5 (anchors5.c0) (anchors5.b0) (anchors5.a0) (anchors5.d0) ≠
        counterLam5 (anchors5.c0) i0_5 i0_5 (anchors5.d0) * counterLam5 i0_5 (anchors5.b0) (anchors5.a0) i1_5 := by
    native_decide
  exact hNe hEq

theorem swapBalance_not_imply_bridge_on_int5 :
    ¬ (∀ lam : LambdaInt 5,
      SwapBalanceConditionInt anchors5 lam → BridgeConditionSetInt anchors5 lam) := by
  intro h
  exact counterLam5_not_bridge (h counterLam5 counterLam5_satisfies_swapBalances)

def counterLam5Real : Lambda 5 :=
  fun a b c d => (counterLam5 a b c d : ℝ)

theorem counterLam5Real_satisfies_swapBalances :
    SwapBalanceCondition anchors5 counterLam5Real := by
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · intro a b c d hvalid
    change
      (counterLam5 a b c d : ℝ) * (counterLam5 anchors5.a0 anchors5.b0 anchors5.c0 anchors5.d0 : ℝ) =
        (counterLam5 c b a d : ℝ) * (counterLam5 anchors5.c0 anchors5.b0 anchors5.a0 anchors5.d0 : ℝ)
    exact_mod_cast (counterLam5_satisfies_swapBalances.h1Bal1 a b c d hvalid)
  · intro a b c d hvalid
    change
      (counterLam5 a b anchors5.c0 anchors5.d0 : ℝ) * (counterLam5 anchors5.a0 anchors5.b0 c d : ℝ) =
        (counterLam5 anchors5.c0 b a anchors5.d0 : ℝ) * (counterLam5 c anchors5.b0 anchors5.a0 d : ℝ)
    exact_mod_cast (counterLam5_satisfies_swapBalances.h1Bal2 a b c d hvalid)
  · intro a b
    change
      (counterLam5 a b anchors5.c0 anchors5.d0 : ℝ) * (counterLam5 anchors5.a0 anchors5.b0 anchors5.c0 anchors5.d0 : ℝ) =
        (counterLam5 b a anchors5.c0 anchors5.d0 : ℝ) * (counterLam5 anchors5.b0 anchors5.a0 anchors5.c0 anchors5.d0 : ℝ)
    exact_mod_cast (counterLam5_satisfies_swapBalances.h2Bal1 a b)
  · intro a b
    change
      (counterLam5 a anchors5.b0 anchors5.c0 anchors5.d0 : ℝ) * (counterLam5 anchors5.a0 b anchors5.c0 anchors5.d0 : ℝ) =
        (counterLam5 anchors5.b0 a anchors5.c0 anchors5.d0 : ℝ) * (counterLam5 b anchors5.a0 anchors5.c0 anchors5.d0 : ℝ)
    exact_mod_cast (counterLam5_satisfies_swapBalances.h2Bal2 a b)
  · intro c d
    change
      (counterLam5 anchors5.a0 anchors5.b0 c d : ℝ) * (counterLam5 anchors5.a0 anchors5.b0 anchors5.c0 anchors5.d0 : ℝ) =
        (counterLam5 anchors5.a0 anchors5.b0 d c : ℝ) * (counterLam5 anchors5.a0 anchors5.b0 anchors5.d0 anchors5.c0 : ℝ)
    exact_mod_cast (counterLam5_satisfies_swapBalances.h3Bal1 c d)
  · intro c d
    change
      (counterLam5 anchors5.a0 anchors5.b0 c anchors5.d0 : ℝ) * (counterLam5 anchors5.a0 anchors5.b0 anchors5.c0 d : ℝ) =
        (counterLam5 anchors5.a0 anchors5.b0 anchors5.d0 c : ℝ) * (counterLam5 anchors5.a0 anchors5.b0 d anchors5.c0 : ℝ)
    exact_mod_cast (counterLam5_satisfies_swapBalances.h3Bal2 c d)

theorem counterLam5Real_not_bridge :
    ¬ BridgeConditionSet anchors5 counterLam5Real := by
  intro hBridge
  have hvalid : valid i0_5 i0_5 i0_5 i1_5 := by native_decide
  have hEq := hBridge.bridge1 i0_5 i0_5 i0_5 i1_5 hvalid
  simp [counterLam5Real, counterLam5, specialSupport5, anchors5, canonicalAnchors,
    i0_5, i1_5, i2_5, i3_5] at hEq
  norm_num at hEq

theorem swapBalance_not_imply_bridge_on_real5 :
    ¬ (∀ lam : Lambda 5,
      SwapBalanceCondition anchors5 lam → BridgeConditionSet anchors5 lam) := by
  intro h
  exact counterLam5Real_not_bridge (h counterLam5Real counterLam5Real_satisfies_swapBalances)

theorem counterLam5Real_not_separable :
    ¬ separable counterLam5Real := by
  intro hSep
  exact counterLam5Real_not_bridge (bridgeConditionSet_of_separable anchors5 counterLam5Real hSep)

theorem counterLam5Real_nonzeroOnValid :
    nonzeroOnValid counterLam5Real := by
  intro a b c d _hvalid
  by_cases hs : specialSupport5 a b c d
  · simp [counterLam5Real, counterLam5, hs]
  · simp [counterLam5Real, counterLam5, hs]

def sepU5 : Idx 5 → ℝ :=
  fun a => if a = i0_5 then 2 else 1

def sepLam5 : Lambda 5 :=
  fun a _b _c _d => sepU5 a

theorem sepLam5_separable :
    separable sepLam5 := by
  refine ⟨sepU5, (fun _ => 1), (fun _ => 1), (fun _ => 1), ?_, ?_, ?_, ?_, ?_⟩
  · intro i
    by_cases hi : i = i0_5 <;> simp [sepU5, hi]
  · intro _i
    norm_num
  · intro _i
    norm_num
  · intro _i
    norm_num
  · intro a b c d _hvalid
    by_cases ha : a = i0_5 <;> simp [sepLam5, sepU5, ha]

theorem sepLam5_h1Bal1_failure :
    sepLam5 i0_5 i1_5 i1_5 i3_5 * sepLam5 anchors5.a0 anchors5.b0 anchors5.c0 anchors5.d0 ≠
      sepLam5 i1_5 i1_5 i0_5 i3_5 * sepLam5 anchors5.c0 anchors5.b0 anchors5.a0 anchors5.d0 := by
  have hL1 : sepLam5 i0_5 i1_5 i1_5 i3_5 = 2 := by
    simp [sepLam5, sepU5, i0_5]
  have hL2 : sepLam5 anchors5.a0 anchors5.b0 anchors5.c0 anchors5.d0 = 2 := by
    simp [anchors5, canonicalAnchors, sepLam5, sepU5, i0_5]
  have hR1 : sepLam5 i1_5 i1_5 i0_5 i3_5 = 1 := by
    simp [sepLam5, sepU5, i1_5, i0_5]
  have hR2 : sepLam5 anchors5.c0 anchors5.b0 anchors5.a0 anchors5.d0 = 1 := by
    simp [anchors5, canonicalAnchors, sepLam5, sepU5, i2_5, i0_5]
  rw [hL1, hL2, hR1, hR2]
  norm_num

theorem swapZeroMapFin_counterexample_on_sepLam5
    (A : CameraMatrices 5)
    (hGeneric : IsGenericStrong A) :
    ¬ (∀ t : Fin (Fintype.card (SwapZeroIndex 5)),
      swapZeroMapFin 5 (by decide) (scaleInput sepLam5 (QInput A)) t = 0) := by
  intro hZero
  have hZero' : ∀ idx, swapZeroMap 5 (by decide) (scaleInput sepLam5 (QInput A)) idx = 0 := by
    intro idx
    simpa [swapZeroMapFin] using hZero ((Fintype.equivFin (SwapZeroIndex 5)) idx)
  have hz :
      pluckerMap
        (fun _ : Fin 1 =>
          swap13Pattern
            (anchorQIndex i0_5 i1_5 i1_5 i3_5)
            (anchorQIndex anchors5.a0 anchors5.b0 anchors5.c0 anchors5.d0)
            (repeatedCoreIndex anchors5)
            (repeatedCoreIndex anchors5))
        (scaleInput sepLam5 (QInput A)) ⟨0, by decide⟩ = 0 := by
    simpa [swapZeroMap, swapZeroMapWithAnchors] using
      hZero' (SwapZeroIndex.h1Bal1 i0_5 i1_5 i1_5 i3_5)
  have hvalid : valid i0_5 i1_5 i1_5 i3_5 := by native_decide
  have hEq :
      sepLam5 i0_5 i1_5 i1_5 i3_5 * sepLam5 anchors5.a0 anchors5.b0 anchors5.c0 anchors5.d0 =
        sepLam5 i1_5 i1_5 i0_5 i3_5 * sepLam5 anchors5.c0 anchors5.b0 anchors5.a0 anchors5.d0 := by
    exact (concrete_h1Bal1_zero_iff_of_genericStrong
      anchors5 A sepLam5 i0_5 i1_5 i1_5 i3_5 hvalid hGeneric).1 hz
  exact sepLam5_h1Bal1_failure hEq

theorem not_swapZeroForwardCompleteness5_of_genericStrong_exists
    (hExists : ∃ A : CameraMatrices 5, IsGenericStrong A) :
    ¬ SwapZeroForwardCompleteness 5 (by decide) := by
  intro hForward
  rcases hExists with ⟨A, hGeneric⟩
  have hZero :
      ∀ t : Fin (Fintype.card (SwapZeroIndex 5)),
        swapZeroMapFin 5 (by decide) (scaleInput sepLam5 (QInput A)) t = 0 := by
    exact hForward A sepLam5 sepLam5_separable
  exact swapZeroMapFin_counterexample_on_sepLam5 A hGeneric hZero

theorem bridgeRecoverability5_contradiction
    (R : BridgeRecoverability 5)
    (A : CameraMatrices 5)
    (hGeneric : IsGenericStrong A) :
    False := by
  rcases zeroFamilies_of_swapBalance_of_genericStrong
    anchors5 A counterLam5Real hGeneric counterLam5Real_satisfies_swapBalances
    with ⟨hZeroH1Bal1, hZeroH1Bal2, hZeroH2Bal1, hZeroH2Bal2, hZeroH3Bal1, hZeroH3Bal2⟩
  have hBridge : BridgeConditionSet anchors5 counterLam5Real := by
    exact bridgeConditionSet_of_bridgeRecoverability
      R anchors5 A counterLam5Real hGeneric
      hZeroH1Bal1 hZeroH1Bal2 hZeroH2Bal1 hZeroH2Bal2 hZeroH3Bal1 hZeroH3Bal2
  exact counterLam5Real_not_bridge hBridge

theorem not_bridgeRecoverability5_of_genericStrong_exists
    (hExists : ∃ A : CameraMatrices 5, IsGenericStrong A) :
    ¬ BridgeRecoverability 5 := by
  intro R
  rcases hExists with ⟨A, hGeneric⟩
  exact bridgeRecoverability5_contradiction R A hGeneric

theorem not_bridgeExtractors5_of_genericStrong_exists
    (hExists : ∃ A : CameraMatrices 5, IsGenericStrong A) :
    ¬ BridgeExtractors 5 := by
  intro E
  have hR : BridgeRecoverability 5 := bridgeRecoverability_of_bridgeExtractors E
  exact not_bridgeRecoverability5_of_genericStrong_exists hExists hR

theorem not_permutedHExtractors5_of_genericStrong_exists
    (hExists : ∃ A : CameraMatrices 5, IsGenericStrong A) :
    ¬ PermutedHExtractors 5 := by
  intro E
  exact not_bridgeExtractors5_of_genericStrong_exists hExists E.toBridgeExtractors

end Question9
