import Question9.ScaledQ
import Question9.Generic
import Question9.Plucker
import Question9.Bridge
import Question9.FamilyWitness
import Question9.BilinearWitness

namespace Question9

open Characterization

structure BridgeExtractors (n : Nat) where
  bridge1_from_zero :
    ∀ S : Anchors n, ∀ A : CameraMatrices n, ∀ lam : Lambda n, IsGenericStrong A →
      (∀ a b c d, valid a b c d →
        pluckerMap
          (fun _ : Fin 1 =>
            swap13Pattern
              (anchorQIndex a b c d)
              (anchorQIndex S.a0 S.b0 S.c0 S.d0)
              (repeatedCoreIndex S)
              (repeatedCoreIndex S))
          (scaleInput lam (QInput A)) ⟨0, by decide⟩ = 0) →
      (∀ a b c d, valid a b c d →
        pluckerMap
          (fun _ : Fin 1 =>
            swap13Pattern
              (anchorQIndex a b S.c0 S.d0)
              (anchorQIndex S.a0 S.b0 c d)
              (repeatedCoreIndex S)
              (repeatedCoreIndex S))
          (scaleInput lam (QInput A)) ⟨0, by decide⟩ = 0) →
      ∀ a b c d, valid a b c d →
        lam c b a d * lam S.c0 S.b0 S.a0 S.d0 =
          lam S.c0 b a S.d0 * lam c S.b0 S.a0 d
  bridge2_from_zero :
    ∀ S : Anchors n, ∀ A : CameraMatrices n, ∀ lam : Lambda n, IsGenericStrong A →
      (∀ a b,
        pluckerMap
          (fun _ : Fin 1 =>
            swap12Pattern
              (anchorQIndex a b S.c0 S.d0)
              (anchorQIndex S.a0 S.b0 S.c0 S.d0)
              (repeatedCoreIndex S)
              (repeatedCoreIndex S))
          (scaleInput lam (QInput A)) ⟨0, by decide⟩ = 0) →
      (∀ a b,
        pluckerMap
          (fun _ : Fin 1 =>
            swap12Pattern
              (anchorQIndex a S.b0 S.c0 S.d0)
              (anchorQIndex S.a0 b S.c0 S.d0)
              (repeatedCoreIndex S)
              (repeatedCoreIndex S))
          (scaleInput lam (QInput A)) ⟨0, by decide⟩ = 0) →
      ∀ a b,
        lam b a S.c0 S.d0 * lam S.b0 S.a0 S.c0 S.d0 =
          lam S.b0 a S.c0 S.d0 * lam b S.a0 S.c0 S.d0
  bridge3_from_zero :
    ∀ S : Anchors n, ∀ A : CameraMatrices n, ∀ lam : Lambda n, IsGenericStrong A →
      (∀ c d,
        pluckerMap
          (fun _ : Fin 1 =>
            swap34Pattern
              (anchorQIndex S.a0 S.b0 c d)
              (anchorQIndex S.a0 S.b0 S.c0 S.d0)
              (repeatedCoreIndex S)
              (repeatedCoreIndex S))
          (scaleInput lam (QInput A)) ⟨0, by decide⟩ = 0) →
      (∀ c d,
        pluckerMap
          (fun _ : Fin 1 =>
            swap34Pattern
              (anchorQIndex S.a0 S.b0 c S.d0)
              (anchorQIndex S.a0 S.b0 S.c0 d)
              (repeatedCoreIndex S)
              (repeatedCoreIndex S))
          (scaleInput lam (QInput A)) ⟨0, by decide⟩ = 0) →
      ∀ c d,
        lam S.a0 S.b0 d c * lam S.a0 S.b0 S.d0 S.c0 =
          lam S.a0 S.b0 S.d0 c * lam S.a0 S.b0 d S.c0

structure PermutedHExtractors (n : Nat) where
  h1_swap13_from_zero :
    ∀ S : Anchors n, ∀ A : CameraMatrices n, ∀ lam : Lambda n, IsGenericStrong A →
      (∀ a b c d, valid a b c d →
        pluckerMap
          (fun _ : Fin 1 =>
            swap13Pattern
              (anchorQIndex a b c d)
              (anchorQIndex S.a0 S.b0 S.c0 S.d0)
              (repeatedCoreIndex S)
              (repeatedCoreIndex S))
          (scaleInput lam (QInput A)) ⟨0, by decide⟩ = 0) →
      (∀ a b c d, valid a b c d →
        pluckerMap
          (fun _ : Fin 1 =>
            swap13Pattern
              (anchorQIndex a b S.c0 S.d0)
              (anchorQIndex S.a0 S.b0 c d)
              (repeatedCoreIndex S)
              (repeatedCoreIndex S))
          (scaleInput lam (QInput A)) ⟨0, by decide⟩ = 0) →
      H1Condition S (swap13Lambda lam)
  h2_swap12_from_zero :
    ∀ S : Anchors n, ∀ A : CameraMatrices n, ∀ lam : Lambda n, IsGenericStrong A →
      (∀ a b,
        pluckerMap
          (fun _ : Fin 1 =>
            swap12Pattern
              (anchorQIndex a b S.c0 S.d0)
              (anchorQIndex S.a0 S.b0 S.c0 S.d0)
              (repeatedCoreIndex S)
              (repeatedCoreIndex S))
          (scaleInput lam (QInput A)) ⟨0, by decide⟩ = 0) →
      (∀ a b,
        pluckerMap
          (fun _ : Fin 1 =>
            swap12Pattern
              (anchorQIndex a S.b0 S.c0 S.d0)
              (anchorQIndex S.a0 b S.c0 S.d0)
              (repeatedCoreIndex S)
              (repeatedCoreIndex S))
          (scaleInput lam (QInput A)) ⟨0, by decide⟩ = 0) →
      H2Condition S (swap12Lambda lam)
  h3_swap34_from_zero :
    ∀ S : Anchors n, ∀ A : CameraMatrices n, ∀ lam : Lambda n, IsGenericStrong A →
      (∀ c d,
        pluckerMap
          (fun _ : Fin 1 =>
            swap34Pattern
              (anchorQIndex S.a0 S.b0 c d)
              (anchorQIndex S.a0 S.b0 S.c0 S.d0)
              (repeatedCoreIndex S)
              (repeatedCoreIndex S))
          (scaleInput lam (QInput A)) ⟨0, by decide⟩ = 0) →
      (∀ c d,
        pluckerMap
          (fun _ : Fin 1 =>
            swap34Pattern
              (anchorQIndex S.a0 S.b0 c S.d0)
              (anchorQIndex S.a0 S.b0 S.c0 d)
              (repeatedCoreIndex S)
              (repeatedCoreIndex S))
          (scaleInput lam (QInput A)) ⟨0, by decide⟩ = 0) →
      H3Condition S (swap34Lambda lam)

def PermutedHExtractors.toBridgeExtractors
    {n : Nat}
    (E : PermutedHExtractors n) : BridgeExtractors n where
  bridge1_from_zero := by
    intro S A lam hGeneric hZero1 hZero2
    exact (bridge1Condition_iff_h1_swap13 S lam).2
      (E.h1_swap13_from_zero S A lam hGeneric hZero1 hZero2)
  bridge2_from_zero := by
    intro S A lam hGeneric hZero1 hZero2
    exact (bridge2Condition_iff_h2_swap12 S lam).2
      (E.h2_swap12_from_zero S A lam hGeneric hZero1 hZero2)
  bridge3_from_zero := by
    intro S A lam hGeneric hZero1 hZero2
    exact (bridge3Condition_iff_h3_swap34 S lam).2
      (E.h3_swap34_from_zero S A lam hGeneric hZero1 hZero2)

def BridgeRecoverability (n : Nat) : Prop :=
  ∀ S : Anchors n, ∀ A : CameraMatrices n, ∀ lam : Lambda n, IsGenericStrong A →
    (∀ a b c d, valid a b c d →
      pluckerMap
        (fun _ : Fin 1 =>
          swap13Pattern
            (anchorQIndex a b c d)
            (anchorQIndex S.a0 S.b0 S.c0 S.d0)
            (repeatedCoreIndex S)
            (repeatedCoreIndex S))
        (scaleInput lam (QInput A)) ⟨0, by decide⟩ = 0) →
    (∀ a b c d, valid a b c d →
      pluckerMap
        (fun _ : Fin 1 =>
          swap13Pattern
            (anchorQIndex a b S.c0 S.d0)
            (anchorQIndex S.a0 S.b0 c d)
            (repeatedCoreIndex S)
            (repeatedCoreIndex S))
        (scaleInput lam (QInput A)) ⟨0, by decide⟩ = 0) →
    (∀ a b,
      pluckerMap
        (fun _ : Fin 1 =>
          swap12Pattern
            (anchorQIndex a b S.c0 S.d0)
            (anchorQIndex S.a0 S.b0 S.c0 S.d0)
            (repeatedCoreIndex S)
            (repeatedCoreIndex S))
        (scaleInput lam (QInput A)) ⟨0, by decide⟩ = 0) →
    (∀ a b,
      pluckerMap
        (fun _ : Fin 1 =>
          swap12Pattern
            (anchorQIndex a S.b0 S.c0 S.d0)
            (anchorQIndex S.a0 b S.c0 S.d0)
            (repeatedCoreIndex S)
            (repeatedCoreIndex S))
        (scaleInput lam (QInput A)) ⟨0, by decide⟩ = 0) →
    (∀ c d,
      pluckerMap
        (fun _ : Fin 1 =>
          swap34Pattern
            (anchorQIndex S.a0 S.b0 c d)
            (anchorQIndex S.a0 S.b0 S.c0 S.d0)
            (repeatedCoreIndex S)
            (repeatedCoreIndex S))
        (scaleInput lam (QInput A)) ⟨0, by decide⟩ = 0) →
    (∀ c d,
      pluckerMap
        (fun _ : Fin 1 =>
          swap34Pattern
            (anchorQIndex S.a0 S.b0 c S.d0)
            (anchorQIndex S.a0 S.b0 S.c0 d)
            (repeatedCoreIndex S)
            (repeatedCoreIndex S))
        (scaleInput lam (QInput A)) ⟨0, by decide⟩ = 0) →
    (∀ a b c d, valid a b c d →
      lam c b a d * lam S.c0 S.b0 S.a0 S.d0 =
        lam S.c0 b a S.d0 * lam c S.b0 S.a0 d) ∧
    (∀ a b,
      lam b a S.c0 S.d0 * lam S.b0 S.a0 S.c0 S.d0 =
        lam S.b0 a S.c0 S.d0 * lam b S.a0 S.c0 S.d0) ∧
    (∀ c d,
      lam S.a0 S.b0 d c * lam S.a0 S.b0 S.d0 S.c0 =
        lam S.a0 S.b0 S.d0 c * lam S.a0 S.b0 d S.c0)

theorem bridgeRecoverability_of_bridgeExtractors
    {n : Nat}
    (E : BridgeExtractors n) :
    BridgeRecoverability n := by
  intro S A lam hGeneric hZeroH1Bal1 hZeroH1Bal2 hZeroH2Bal1 hZeroH2Bal2 hZeroH3Bal1 hZeroH3Bal2
  refine ⟨?_, ?_, ?_⟩
  · exact E.bridge1_from_zero S A lam hGeneric hZeroH1Bal1 hZeroH1Bal2
  · exact E.bridge2_from_zero S A lam hGeneric hZeroH2Bal1 hZeroH2Bal2
  · exact E.bridge3_from_zero S A lam hGeneric hZeroH3Bal1 hZeroH3Bal2

inductive SwapZeroIndex (n : Nat) where
  | h1Bal1 : Idx n → Idx n → Idx n → Idx n → SwapZeroIndex n
  | h1Bal2 : Idx n → Idx n → Idx n → Idx n → SwapZeroIndex n
  | h2Bal1 : Idx n → Idx n → SwapZeroIndex n
  | h2Bal2 : Idx n → Idx n → SwapZeroIndex n
  | h3Bal1 : Idx n → Idx n → SwapZeroIndex n
  | h3Bal2 : Idx n → Idx n → SwapZeroIndex n
deriving DecidableEq, Fintype

noncomputable def swapZeroMapWithAnchors
    {n : Nat}
    (S : Anchors n) :
    InputVector n → (SwapZeroIndex n → ℝ) := by
  intro Y idx
  exact
    match idx with
    | .h1Bal1 a b c d =>
        pluckerRel Y
          (swap13Pattern
            (anchorQIndex a b c d)
            (anchorQIndex S.a0 S.b0 S.c0 S.d0)
            (repeatedCoreIndex S)
            (repeatedCoreIndex S))
    | .h1Bal2 a b c d =>
        pluckerRel Y
          (swap13Pattern
            (anchorQIndex a b S.c0 S.d0)
            (anchorQIndex S.a0 S.b0 c d)
            (repeatedCoreIndex S)
            (repeatedCoreIndex S))
    | .h2Bal1 a b =>
        pluckerRel Y
          (swap12Pattern
            (anchorQIndex a b S.c0 S.d0)
            (anchorQIndex S.a0 S.b0 S.c0 S.d0)
            (repeatedCoreIndex S)
            (repeatedCoreIndex S))
    | .h2Bal2 a b =>
        pluckerRel Y
          (swap12Pattern
            (anchorQIndex a S.b0 S.c0 S.d0)
            (anchorQIndex S.a0 b S.c0 S.d0)
            (repeatedCoreIndex S)
            (repeatedCoreIndex S))
    | .h3Bal1 c d =>
        pluckerRel Y
          (swap34Pattern
            (anchorQIndex S.a0 S.b0 c d)
            (anchorQIndex S.a0 S.b0 S.c0 S.d0)
            (repeatedCoreIndex S)
            (repeatedCoreIndex S))
    | .h3Bal2 c d =>
        pluckerRel Y
          (swap34Pattern
            (anchorQIndex S.a0 S.b0 c S.d0)
            (anchorQIndex S.a0 S.b0 S.c0 d)
            (repeatedCoreIndex S)
            (repeatedCoreIndex S))

noncomputable def swapZeroMap
    (n : Nat)
    (hn : 5 ≤ n) :
    InputVector n → (SwapZeroIndex n → ℝ) :=
  swapZeroMapWithAnchors (canonicalAnchors n hn)

noncomputable def swapZeroMapFin
    (n : Nat)
    (hn : 5 ≤ n) :
    InputVector n → (Fin (Fintype.card (SwapZeroIndex n)) → ℝ) :=
  fun Y t => (swapZeroMap n hn Y) ((Fintype.equivFin (SwapZeroIndex n)).symm t)

theorem main_characterization
    {n : Nat}
    (S : Anchors n)
    (lam : Lambda n)
    (hNZ : nonzeroOnValid lam) :
    FZero S lam ↔ separable lam := by
  exact Characterization.fzero_iff_separable S lam hNZ

theorem exists_uniform_polynomial_map
    (n : Nat)
    (hn : 5 ≤ n) :
    ∃ F : Lambda n → (Idx n → Idx n → Idx n → Idx n → ℝ),
      (coordinateDegree = 4) ∧
      (∀ lam, nonzeroOnValid lam →
         ((∀ a b c d, valid a b c d → F lam a b c d = 0) ↔ separable lam)) := by
  refine ⟨FMap (canonicalAnchors n hn), coordinateDegree_eq, ?_⟩
  intro lam hNZ
  simpa [FMap, FZero] using
    (Characterization.fzero_iff_separable (canonicalAnchors n hn) lam hNZ)

theorem scaled_tensor_statement
    {n : Nat}
    (S : Anchors n)
    (Q X : TensorField n)
    (lam : Lambda n)
    (hScale :
      ∀ a b c d, valid a b c d →
        X a b c d i0 i0 i0 i0 = lam a b c d * Q a b c d i0 i0 i0 i0)
    (hQNZ :
      ∀ a b c d, valid a b c d → Q a b c d i0 i0 i0 i0 ≠ 0)
    (hlamNZ : nonzeroOnValid lam) :
    FZero S (extractLambda Q X) ↔ separable (extractLambda Q X) := by
  exact scaledQ_characterization S Q X lam hScale hQNZ hlamNZ

theorem concrete_q_characterization
    {n : Nat}
    (S : Anchors n)
    (A : CameraMatrices n)
    (Y : InputVector n)
    (lam : Lambda n)
    (hScale : isScaledInput Y lam (QInput A))
    (hQNZ : ∀ a b c d, valid a b c d → QInput A (anchorQIndex a b c d) ≠ 0)
    (hLamNZ : nonzeroOnValid lam) :
    FZero S (extractLambdaFromInput (QInput A) Y) ↔
      separable (extractLambdaFromInput (QInput A) Y) := by
  exact Characterization.fzero_iff_separable S (extractLambdaFromInput (QInput A) Y)
    (extractLambdaFromInput_nonzero (QInput A) Y lam hScale hQNZ hLamNZ)

theorem concrete_q_characterization_of_generic
    {n : Nat}
    (S : Anchors n)
    (A : CameraMatrices n)
    (Y : InputVector n)
    (lam : Lambda n)
    (hScale : isScaledInput Y lam (QInput A))
    (hGeneric : IsGeneric A)
    (hLamNZ : nonzeroOnValid lam) :
    FZero S (extractLambdaFromInput (QInput A) Y) ↔
      separable (extractLambdaFromInput (QInput A) Y) := by
  exact concrete_q_characterization S A Y lam hScale
    (anchor_nonzero_of_isGeneric A hGeneric) hLamNZ

theorem concrete_q_characterization_of_genericStrong
    {n : Nat}
    (S : Anchors n)
    (A : CameraMatrices n)
    (Y : InputVector n)
    (lam : Lambda n)
    (hScale : isScaledInput Y lam (QInput A))
    (hGeneric : IsGenericStrong A)
    (hLamNZ : nonzeroOnValid lam) :
    FZero S (extractLambdaFromInput (QInput A) Y) ↔
      separable (extractLambdaFromInput (QInput A) Y) := by
  exact concrete_q_characterization_of_generic S A Y lam hScale
    (isGenericStrong_implies_isGeneric A hGeneric) hLamNZ

theorem plucker_layer_has_uniform_degree :
    pluckerCoordinateDegree = 2 := by
  exact pluckerCoordinateDegree_eq

theorem plucker_forward_for_family
    {n m : Nat}
    (patterns : Fin m → PluckerPattern n)
    (lam : Lambda n)
    (T Y : InputVector n)
    (hScale : Y = scaleInput lam T)
    (hBalanced : ∀ t, PluckerBalanced lam (patterns t))
    (hBaseZero : ∀ t, pluckerRel T (patterns t) = 0) :
    ∀ t, pluckerRel Y (patterns t) = 0 := by
  intro t
  rw [hScale]
  exact pluckerRel_scale_of_balanced lam T (patterns t) (hBalanced t) (hBaseZero t)

theorem plucker_map_forward_for_family
    {n m : Nat}
    (patterns : Fin m → PluckerPattern n)
    (lam : Lambda n)
    (T Y : InputVector n)
    (hScale : Y = scaleInput lam T)
    (hBalanced : ∀ t, PluckerBalanced lam (patterns t))
    (hBaseZero : ∀ t, pluckerRel T (patterns t) = 0) :
    ∀ t, pluckerMap patterns Y t = 0 := by
  intro t
  exact plucker_forward_for_family patterns lam T Y hScale hBalanced hBaseZero t

theorem concrete_plucker_forward_of_separable
    {n m : Nat}
    (A : CameraMatrices n)
    (patterns : Fin m → PluckerPattern n)
    (lam : Lambda n)
    (hSep : separable lam)
    (hValid : ∀ t, PatternValid (patterns t))
    (hAlign : ∀ t, ModeAligned (patterns t))
    (hBaseZero : ∀ t, pluckerRel (QInput A) (patterns t) = 0) :
    ∀ t, pluckerMap patterns (scaleInput lam (QInput A)) t = 0 := by
  intro t
  exact plucker_forward_of_separable_for_family patterns lam (QInput A) hSep hValid hAlign hBaseZero t

theorem concrete_plucker_forward_of_separable_repeated
    {n m : Nat}
    (A : CameraMatrices n)
    (patterns : Fin m → PluckerPattern n)
    (lam : Lambda n)
    (hSep : separable lam)
    (hValid : ∀ t, PatternValid (patterns t))
    (hAlign : ∀ t, ModeAligned (patterns t))
    (hRep1 : ∀ t, RepeatedFirstTwo (patterns t).p1)
    (hRep3 : ∀ t, RepeatedFirstTwo (patterns t).p3)
    (hRep5 : ∀ t, RepeatedFirstTwo (patterns t).p5) :
    ∀ t, pluckerMap patterns (scaleInput lam (QInput A)) t = 0 := by
  intro t
  exact plucker_forward_of_separable_for_repeated_family A patterns lam hSep hValid hAlign
    hRep1 hRep3 hRep5 t

theorem concrete_single_repeated_plucker_forward
    {n : Nat}
    (S : Anchors n)
    (A : CameraMatrices n)
    (lam : Lambda n)
    (hSep : separable lam) :
    pluckerMap (fun _ : Fin 1 => repeatedPattern S)
      (scaleInput lam (QInput A)) ⟨0, by decide⟩ = 0 := by
  have hAll :
      ∀ t, pluckerMap (fun _ : Fin 1 => repeatedPattern S)
        (scaleInput lam (QInput A)) t = 0 := by
    exact concrete_plucker_forward_of_separable_repeated A (fun _ : Fin 1 => repeatedPattern S) lam
      hSep
      (by intro t; simpa using repeatedPattern_valid S)
      (by intro t; simpa using repeatedPattern_modeAligned S)
      (by intro t; simpa using repeatedPattern_rep1 S)
      (by intro t; simpa using repeatedPattern_rep3 S)
      (by intro t; simpa using repeatedPattern_rep5 S)
  exact hAll ⟨0, by decide⟩

theorem concrete_plucker_forward_of_separable_swap12
    {n m : Nat}
    (A : CameraMatrices n)
    (patterns : Fin m → PluckerPattern n)
    (lam : Lambda n)
    (hSep : separable lam)
    (hValid : ∀ t, PatternValid (patterns t))
    (hCross : ∀ t, Swap12CrossAligned (patterns t))
    (hRep5 : ∀ t, RepeatedFirstTwo (patterns t).p5) :
    ∀ t, pluckerMap patterns (scaleInput lam (QInput A)) t = 0 := by
  intro t
  exact plucker_forward_of_separable_for_swap12_family A patterns lam hSep hValid hCross hRep5 t

theorem concrete_plucker_forward_of_separable_swap13
    {n m : Nat}
    (A : CameraMatrices n)
    (patterns : Fin m → PluckerPattern n)
    (lam : Lambda n)
    (hSep : separable lam)
    (hValid : ∀ t, PatternValid (patterns t))
    (hCross : ∀ t, Swap13CrossAligned (patterns t))
    (hRep5 : ∀ t, RepeatedFirstTwo (patterns t).p5) :
    ∀ t, pluckerMap patterns (scaleInput lam (QInput A)) t = 0 := by
  intro t
  exact plucker_forward_of_separable_for_swap13_family A patterns lam hSep hValid hCross hRep5 t

theorem concrete_plucker_forward_of_separable_swap34
    {n m : Nat}
    (A : CameraMatrices n)
    (patterns : Fin m → PluckerPattern n)
    (lam : Lambda n)
    (hSep : separable lam)
    (hValid : ∀ t, PatternValid (patterns t))
    (hCross : ∀ t, Swap34CrossAligned (patterns t))
    (hRep5 : ∀ t, RepeatedFirstTwo (patterns t).p5) :
    ∀ t, pluckerMap patterns (scaleInput lam (QInput A)) t = 0 := by
  intro t
  exact plucker_forward_of_separable_for_swap34_family A patterns lam hSep hValid hCross hRep5 t

theorem concrete_swap12Pattern_forward_of_separable
    {n : Nat}
    (A : CameraMatrices n)
    (lam : Lambda n)
    (p1 p2 p5 p6 : QIndex n)
    (hSep : separable lam)
    (h2a : p2.a = p1.b)
    (h2b : p2.b = p1.a)
    (h1 : validIndex p1)
    (h2 : validIndex p2)
    (h5valid : validIndex p5)
    (h6valid : validIndex p6)
    (h5rep : RepeatedFirstTwo p5) :
    pluckerMap (fun _ : Fin 1 => swap12Pattern p1 p2 p5 p6)
      (scaleInput lam (QInput A)) ⟨0, by decide⟩ = 0 := by
  have hAll :
      ∀ t, pluckerMap (fun _ : Fin 1 => swap12Pattern p1 p2 p5 p6)
        (scaleInput lam (QInput A)) t = 0 := by
    exact concrete_plucker_forward_of_separable_swap12 A
      (fun _ : Fin 1 => swap12Pattern p1 p2 p5 p6) lam hSep
      (by
        intro t
        simpa using swap12Pattern_valid p1 p2 p5 p6 h1 h2 h5valid h6valid)
      (by
        intro t
        simpa using swap12Pattern_crossAligned p1 p2 p5 p6 h2a h2b)
      (by
        intro t
        simpa using h5rep)
  exact hAll ⟨0, by decide⟩

theorem concrete_swap13Pattern_forward_of_separable
    {n : Nat}
    (A : CameraMatrices n)
    (lam : Lambda n)
    (p1 p2 p5 p6 : QIndex n)
    (hSep : separable lam)
    (h2a : p2.a = p1.c)
    (h2c : p2.c = p1.a)
    (h1 : validIndex p1)
    (h2 : validIndex p2)
    (h5valid : validIndex p5)
    (h6valid : validIndex p6)
    (h5rep : RepeatedFirstTwo p5) :
    pluckerMap (fun _ : Fin 1 => swap13Pattern p1 p2 p5 p6)
      (scaleInput lam (QInput A)) ⟨0, by decide⟩ = 0 := by
  have hAll :
      ∀ t, pluckerMap (fun _ : Fin 1 => swap13Pattern p1 p2 p5 p6)
        (scaleInput lam (QInput A)) t = 0 := by
    exact concrete_plucker_forward_of_separable_swap13 A
      (fun _ : Fin 1 => swap13Pattern p1 p2 p5 p6) lam hSep
      (by
        intro t
        simpa using swap13Pattern_valid p1 p2 p5 p6 h1 h2 h5valid h6valid)
      (by
        intro t
        simpa using swap13Pattern_crossAligned p1 p2 p5 p6 h2a h2c)
      (by
        intro t
        simpa using h5rep)
  exact hAll ⟨0, by decide⟩

theorem concrete_swap34Pattern_forward_of_separable
    {n : Nat}
    (A : CameraMatrices n)
    (lam : Lambda n)
    (p1 p2 p5 p6 : QIndex n)
    (hSep : separable lam)
    (h2c : p2.c = p1.d)
    (h2d : p2.d = p1.c)
    (h1 : validIndex p1)
    (h2 : validIndex p2)
    (h5valid : validIndex p5)
    (h6valid : validIndex p6)
    (h5rep : RepeatedFirstTwo p5) :
    pluckerMap (fun _ : Fin 1 => swap34Pattern p1 p2 p5 p6)
      (scaleInput lam (QInput A)) ⟨0, by decide⟩ = 0 := by
  have hAll :
      ∀ t, pluckerMap (fun _ : Fin 1 => swap34Pattern p1 p2 p5 p6)
        (scaleInput lam (QInput A)) t = 0 := by
    exact concrete_plucker_forward_of_separable_swap34 A
      (fun _ : Fin 1 => swap34Pattern p1 p2 p5 p6) lam hSep
      (by
        intro t
        simpa using swap34Pattern_valid p1 p2 p5 p6 h1 h2 h5valid h6valid)
      (by
        intro t
        simpa using swap34Pattern_crossAligned p1 p2 p5 p6 h2c h2d)
      (by
        intro t
        simpa using h5rep)
  exact hAll ⟨0, by decide⟩

theorem concrete_swap12_lambda_balance_of_zero
    {n : Nat}
    (A : CameraMatrices n)
    (lam : Lambda n)
    (P : PluckerPattern n)
    (hZero : pluckerMap (fun _ : Fin 1 => P) (scaleInput lam (QInput A)) ⟨0, by decide⟩ = 0)
    (h3 : P.p3 = swap12Index P.p1)
    (h4 : P.p4 = swap12Index P.p2)
    (hRep5 : RepeatedFirstTwo P.p5)
    (hQnz : QInput A P.p1 * QInput A P.p2 ≠ 0) :
    lamAt lam P.p1 * lamAt lam P.p2 = lamAt lam P.p3 * lamAt lam P.p4 := by
  have hZeroRel : pluckerRel (scaleInput lam (QInput A)) P = 0 := by
    simpa [pluckerMap] using hZero
  exact lambda_pairBalance_of_swap12_zero A lam P hZeroRel h3 h4 hRep5 hQnz

theorem concrete_swap12_lambda_balance_of_zero_of_generic_anchorRows
    {n : Nat}
    (A : CameraMatrices n)
    (lam : Lambda n)
    (P : PluckerPattern n)
    (hZero : pluckerMap (fun _ : Fin 1 => P) (scaleInput lam (QInput A)) ⟨0, by decide⟩ = 0)
    (h3 : P.p3 = swap12Index P.p1)
    (h4 : P.p4 = swap12Index P.p2)
    (hRep5 : RepeatedFirstTwo P.p5)
    (hGeneric : IsGeneric A)
    (hValid1 : validIndex P.p1)
    (hValid2 : validIndex P.p2)
    (hRows1 : AnchorRows P.p1)
    (hRows2 : AnchorRows P.p2) :
    lamAt lam P.p1 * lamAt lam P.p2 = lamAt lam P.p3 * lamAt lam P.p4 := by
  have hq1 : QInput A P.p1 ≠ 0 := qInput_nonzero_of_isGeneric_anchorRows A hGeneric P.p1 hValid1 hRows1
  have hq2 : QInput A P.p2 ≠ 0 := qInput_nonzero_of_isGeneric_anchorRows A hGeneric P.p2 hValid2 hRows2
  have hQnz : QInput A P.p1 * QInput A P.p2 ≠ 0 := mul_ne_zero hq1 hq2
  exact concrete_swap12_lambda_balance_of_zero A lam P hZero h3 h4 hRep5 hQnz

theorem concrete_swap12_family_lambda_balance_of_zero_of_generic_anchorRows
    {n m : Nat}
    (A : CameraMatrices n)
    (lam : Lambda n)
    (patterns : Fin m → PluckerPattern n)
    (hZero : ∀ t, pluckerMap patterns (scaleInput lam (QInput A)) t = 0)
    (h3 : ∀ t, (patterns t).p3 = swap12Index (patterns t).p1)
    (h4 : ∀ t, (patterns t).p4 = swap12Index (patterns t).p2)
    (hRep5 : ∀ t, RepeatedFirstTwo (patterns t).p5)
    (hGeneric : IsGeneric A)
    (hValid1 : ∀ t, validIndex (patterns t).p1)
    (hValid2 : ∀ t, validIndex (patterns t).p2)
    (hRows1 : ∀ t, AnchorRows (patterns t).p1)
    (hRows2 : ∀ t, AnchorRows (patterns t).p2) :
    ∀ t, lamAt lam (patterns t).p1 * lamAt lam (patterns t).p2 =
      lamAt lam (patterns t).p3 * lamAt lam (patterns t).p4 := by
  intro t
  have hq1 : QInput A (patterns t).p1 ≠ 0 := by
    exact qInput_nonzero_of_isGeneric_anchorRows A hGeneric (patterns t).p1 (hValid1 t) (hRows1 t)
  have hq2 : QInput A (patterns t).p2 ≠ 0 := by
    exact qInput_nonzero_of_isGeneric_anchorRows A hGeneric (patterns t).p2 (hValid2 t) (hRows2 t)
  have hQnz : QInput A (patterns t).p1 * QInput A (patterns t).p2 ≠ 0 := mul_ne_zero hq1 hq2
  have hZeroRel : pluckerRel (scaleInput lam (QInput A)) (patterns t) = 0 := by
    simpa [pluckerMap] using hZero t
  exact lambda_pairBalance_of_swap12_zero A lam (patterns t) hZeroRel (h3 t) (h4 t) (hRep5 t) hQnz

theorem concrete_swap12_lambda_balance_of_zero_of_genericStrong
    {n : Nat}
    (A : CameraMatrices n)
    (lam : Lambda n)
    (P : PluckerPattern n)
    (hZero : pluckerMap (fun _ : Fin 1 => P) (scaleInput lam (QInput A)) ⟨0, by decide⟩ = 0)
    (h3 : P.p3 = swap12Index P.p1)
    (h4 : P.p4 = swap12Index P.p2)
    (hRep5 : RepeatedFirstTwo P.p5)
    (hGeneric : IsGenericStrong A)
    (hValid1 : validIndex P.p1)
    (hValid2 : validIndex P.p2) :
    lamAt lam P.p1 * lamAt lam P.p2 = lamAt lam P.p3 * lamAt lam P.p4 := by
  have hq1 : QInput A P.p1 ≠ 0 := qInput_nonzero_of_isGenericStrong A hGeneric P.p1 hValid1
  have hq2 : QInput A P.p2 ≠ 0 := qInput_nonzero_of_isGenericStrong A hGeneric P.p2 hValid2
  have hQnz : QInput A P.p1 * QInput A P.p2 ≠ 0 := mul_ne_zero hq1 hq2
  exact concrete_swap12_lambda_balance_of_zero A lam P hZero h3 h4 hRep5 hQnz

theorem concrete_swap12_family_lambda_balance_of_zero_of_genericStrong
    {n m : Nat}
    (A : CameraMatrices n)
    (lam : Lambda n)
    (patterns : Fin m → PluckerPattern n)
    (hZero : ∀ t, pluckerMap patterns (scaleInput lam (QInput A)) t = 0)
    (h3 : ∀ t, (patterns t).p3 = swap12Index (patterns t).p1)
    (h4 : ∀ t, (patterns t).p4 = swap12Index (patterns t).p2)
    (hRep5 : ∀ t, RepeatedFirstTwo (patterns t).p5)
    (hGeneric : IsGenericStrong A)
    (hValid1 : ∀ t, validIndex (patterns t).p1)
    (hValid2 : ∀ t, validIndex (patterns t).p2) :
    ∀ t, lamAt lam (patterns t).p1 * lamAt lam (patterns t).p2 =
      lamAt lam (patterns t).p3 * lamAt lam (patterns t).p4 := by
  intro t
  have hq1 : QInput A (patterns t).p1 ≠ 0 := qInput_nonzero_of_isGenericStrong A hGeneric (patterns t).p1 (hValid1 t)
  have hq2 : QInput A (patterns t).p2 ≠ 0 := qInput_nonzero_of_isGenericStrong A hGeneric (patterns t).p2 (hValid2 t)
  have hQnz : QInput A (patterns t).p1 * QInput A (patterns t).p2 ≠ 0 := mul_ne_zero hq1 hq2
  have hZeroRel : pluckerRel (scaleInput lam (QInput A)) (patterns t) = 0 := by
    simpa [pluckerMap] using hZero t
  exact lambda_pairBalance_of_swap12_zero A lam (patterns t) hZeroRel (h3 t) (h4 t) (hRep5 t) hQnz

theorem concrete_swap13_lambda_balance_of_zero
    {n : Nat}
    (A : CameraMatrices n)
    (lam : Lambda n)
    (P : PluckerPattern n)
    (hZero : pluckerMap (fun _ : Fin 1 => P) (scaleInput lam (QInput A)) ⟨0, by decide⟩ = 0)
    (h3 : P.p3 = swap13Index P.p1)
    (h4 : P.p4 = swap13Index P.p2)
    (hRep5 : RepeatedFirstTwo P.p5)
    (hQnz : QInput A P.p1 * QInput A P.p2 ≠ 0) :
    lamAt lam P.p1 * lamAt lam P.p2 = lamAt lam P.p3 * lamAt lam P.p4 := by
  have hZeroRel : pluckerRel (scaleInput lam (QInput A)) P = 0 := by
    simpa [pluckerMap] using hZero
  exact lambda_pairBalance_of_swap13_zero A lam P hZeroRel h3 h4 hRep5 hQnz

theorem concrete_swap13_lambda_balance_of_zero_of_generic_anchorRows
    {n : Nat}
    (A : CameraMatrices n)
    (lam : Lambda n)
    (P : PluckerPattern n)
    (hZero : pluckerMap (fun _ : Fin 1 => P) (scaleInput lam (QInput A)) ⟨0, by decide⟩ = 0)
    (h3 : P.p3 = swap13Index P.p1)
    (h4 : P.p4 = swap13Index P.p2)
    (hRep5 : RepeatedFirstTwo P.p5)
    (hGeneric : IsGeneric A)
    (hValid1 : validIndex P.p1)
    (hValid2 : validIndex P.p2)
    (hRows1 : AnchorRows P.p1)
    (hRows2 : AnchorRows P.p2) :
    lamAt lam P.p1 * lamAt lam P.p2 = lamAt lam P.p3 * lamAt lam P.p4 := by
  have hq1 : QInput A P.p1 ≠ 0 := qInput_nonzero_of_isGeneric_anchorRows A hGeneric P.p1 hValid1 hRows1
  have hq2 : QInput A P.p2 ≠ 0 := qInput_nonzero_of_isGeneric_anchorRows A hGeneric P.p2 hValid2 hRows2
  have hQnz : QInput A P.p1 * QInput A P.p2 ≠ 0 := mul_ne_zero hq1 hq2
  exact concrete_swap13_lambda_balance_of_zero A lam P hZero h3 h4 hRep5 hQnz

theorem concrete_swap13_family_lambda_balance_of_zero_of_generic_anchorRows
    {n m : Nat}
    (A : CameraMatrices n)
    (lam : Lambda n)
    (patterns : Fin m → PluckerPattern n)
    (hZero : ∀ t, pluckerMap patterns (scaleInput lam (QInput A)) t = 0)
    (h3 : ∀ t, (patterns t).p3 = swap13Index (patterns t).p1)
    (h4 : ∀ t, (patterns t).p4 = swap13Index (patterns t).p2)
    (hRep5 : ∀ t, RepeatedFirstTwo (patterns t).p5)
    (hGeneric : IsGeneric A)
    (hValid1 : ∀ t, validIndex (patterns t).p1)
    (hValid2 : ∀ t, validIndex (patterns t).p2)
    (hRows1 : ∀ t, AnchorRows (patterns t).p1)
    (hRows2 : ∀ t, AnchorRows (patterns t).p2) :
    ∀ t, lamAt lam (patterns t).p1 * lamAt lam (patterns t).p2 =
      lamAt lam (patterns t).p3 * lamAt lam (patterns t).p4 := by
  intro t
  have hq1 : QInput A (patterns t).p1 ≠ 0 := by
    exact qInput_nonzero_of_isGeneric_anchorRows A hGeneric (patterns t).p1 (hValid1 t) (hRows1 t)
  have hq2 : QInput A (patterns t).p2 ≠ 0 := by
    exact qInput_nonzero_of_isGeneric_anchorRows A hGeneric (patterns t).p2 (hValid2 t) (hRows2 t)
  have hQnz : QInput A (patterns t).p1 * QInput A (patterns t).p2 ≠ 0 := mul_ne_zero hq1 hq2
  have hZeroRel : pluckerRel (scaleInput lam (QInput A)) (patterns t) = 0 := by
    simpa [pluckerMap] using hZero t
  exact lambda_pairBalance_of_swap13_zero A lam (patterns t) hZeroRel (h3 t) (h4 t) (hRep5 t) hQnz

theorem concrete_swap13_lambda_balance_of_zero_of_genericStrong
    {n : Nat}
    (A : CameraMatrices n)
    (lam : Lambda n)
    (P : PluckerPattern n)
    (hZero : pluckerMap (fun _ : Fin 1 => P) (scaleInput lam (QInput A)) ⟨0, by decide⟩ = 0)
    (h3 : P.p3 = swap13Index P.p1)
    (h4 : P.p4 = swap13Index P.p2)
    (hRep5 : RepeatedFirstTwo P.p5)
    (hGeneric : IsGenericStrong A)
    (hValid1 : validIndex P.p1)
    (hValid2 : validIndex P.p2) :
    lamAt lam P.p1 * lamAt lam P.p2 = lamAt lam P.p3 * lamAt lam P.p4 := by
  have hq1 : QInput A P.p1 ≠ 0 := qInput_nonzero_of_isGenericStrong A hGeneric P.p1 hValid1
  have hq2 : QInput A P.p2 ≠ 0 := qInput_nonzero_of_isGenericStrong A hGeneric P.p2 hValid2
  have hQnz : QInput A P.p1 * QInput A P.p2 ≠ 0 := mul_ne_zero hq1 hq2
  exact concrete_swap13_lambda_balance_of_zero A lam P hZero h3 h4 hRep5 hQnz

theorem concrete_swap13_family_lambda_balance_of_zero_of_genericStrong
    {n m : Nat}
    (A : CameraMatrices n)
    (lam : Lambda n)
    (patterns : Fin m → PluckerPattern n)
    (hZero : ∀ t, pluckerMap patterns (scaleInput lam (QInput A)) t = 0)
    (h3 : ∀ t, (patterns t).p3 = swap13Index (patterns t).p1)
    (h4 : ∀ t, (patterns t).p4 = swap13Index (patterns t).p2)
    (hRep5 : ∀ t, RepeatedFirstTwo (patterns t).p5)
    (hGeneric : IsGenericStrong A)
    (hValid1 : ∀ t, validIndex (patterns t).p1)
    (hValid2 : ∀ t, validIndex (patterns t).p2) :
    ∀ t, lamAt lam (patterns t).p1 * lamAt lam (patterns t).p2 =
      lamAt lam (patterns t).p3 * lamAt lam (patterns t).p4 := by
  intro t
  have hq1 : QInput A (patterns t).p1 ≠ 0 := qInput_nonzero_of_isGenericStrong A hGeneric (patterns t).p1 (hValid1 t)
  have hq2 : QInput A (patterns t).p2 ≠ 0 := qInput_nonzero_of_isGenericStrong A hGeneric (patterns t).p2 (hValid2 t)
  have hQnz : QInput A (patterns t).p1 * QInput A (patterns t).p2 ≠ 0 := mul_ne_zero hq1 hq2
  have hZeroRel : pluckerRel (scaleInput lam (QInput A)) (patterns t) = 0 := by
    simpa [pluckerMap] using hZero t
  exact lambda_pairBalance_of_swap13_zero A lam (patterns t) hZeroRel (h3 t) (h4 t) (hRep5 t) hQnz

theorem concrete_h1Bal1_of_swap13_zero_of_genericStrong
    {n : Nat}
    (S : Anchors n)
    (A : CameraMatrices n)
    (lam : Lambda n)
    (a b c d : Idx n)
    (hvalid : valid a b c d)
    (hGeneric : IsGenericStrong A)
    (hZero :
      pluckerMap
        (fun _ : Fin 1 =>
          swap13Pattern
            (anchorQIndex a b c d)
            (anchorQIndex S.a0 S.b0 S.c0 S.d0)
            (repeatedCoreIndex S)
            (repeatedCoreIndex S))
        (scaleInput lam (QInput A)) ⟨0, by decide⟩ = 0) :
    lam a b c d * lam S.a0 S.b0 S.c0 S.d0 =
      lam c b a d * lam S.c0 S.b0 S.a0 S.d0 := by
  have hBal := concrete_swap13_lambda_balance_of_zero_of_genericStrong A lam
      (swap13Pattern
        (anchorQIndex a b c d)
        (anchorQIndex S.a0 S.b0 S.c0 S.d0)
        (repeatedCoreIndex S)
        (repeatedCoreIndex S))
      hZero
      (by simp [swap13Pattern])
      (by simp [swap13Pattern])
      (by simp [swap13Pattern, repeatedCoreIndex_repeatedFirstTwo])
      hGeneric
      (by simpa [anchorQIndex] using hvalid)
      (by simpa [anchorQIndex] using S.valid_anchor)
  simpa [lamAt, swap13Pattern, anchorQIndex, swap13Index, repeatedCoreIndex] using hBal

theorem concrete_h1Bal2_of_swap13_zero_of_genericStrong
    {n : Nat}
    (S : Anchors n)
    (A : CameraMatrices n)
    (lam : Lambda n)
    (a b c d : Idx n)
    (hGeneric : IsGenericStrong A)
    (hZero :
      pluckerMap
        (fun _ : Fin 1 =>
          swap13Pattern
            (anchorQIndex a b S.c0 S.d0)
            (anchorQIndex S.a0 S.b0 c d)
            (repeatedCoreIndex S)
            (repeatedCoreIndex S))
        (scaleInput lam (QInput A)) ⟨0, by decide⟩ = 0) :
    lam a b S.c0 S.d0 * lam S.a0 S.b0 c d =
      lam S.c0 b a S.d0 * lam c S.b0 S.a0 d := by
  have hvalid1 : valid a b S.c0 S.d0 := by
    intro hall
    exact S.hcd hall.2.2
  have hvalid2 : valid S.a0 S.b0 c d := by
    intro hall
    exact S.hab hall.1
  have hBal := concrete_swap13_lambda_balance_of_zero_of_genericStrong A lam
      (swap13Pattern
        (anchorQIndex a b S.c0 S.d0)
        (anchorQIndex S.a0 S.b0 c d)
        (repeatedCoreIndex S)
        (repeatedCoreIndex S))
      hZero
      (by simp [swap13Pattern])
      (by simp [swap13Pattern])
      (by simp [swap13Pattern, repeatedCoreIndex_repeatedFirstTwo])
      hGeneric
      (by simpa [anchorQIndex] using hvalid1)
      (by simpa [anchorQIndex] using hvalid2)
  simpa [lamAt, swap13Pattern, anchorQIndex, swap13Index, repeatedCoreIndex] using hBal

theorem concrete_swap13_zero_iff_lambda_balance_of_genericStrong
    {n : Nat}
    (A : CameraMatrices n)
    (lam : Lambda n)
    (P : PluckerPattern n)
    (h3 : P.p3 = swap13Index P.p1)
    (h4 : P.p4 = swap13Index P.p2)
    (hRep5 : RepeatedFirstTwo P.p5)
    (hGeneric : IsGenericStrong A)
    (hValid1 : validIndex P.p1)
    (hValid2 : validIndex P.p2) :
    pluckerMap (fun _ : Fin 1 => P) (scaleInput lam (QInput A)) ⟨0, by decide⟩ = 0 ↔
      lamAt lam P.p1 * lamAt lam P.p2 = lamAt lam P.p3 * lamAt lam P.p4 := by
  have hq1 : QInput A P.p1 ≠ 0 := qInput_nonzero_of_isGenericStrong A hGeneric P.p1 hValid1
  have hq2 : QInput A P.p2 ≠ 0 := qInput_nonzero_of_isGenericStrong A hGeneric P.p2 hValid2
  have hQnz : QInput A P.p1 * QInput A P.p2 ≠ 0 := mul_ne_zero hq1 hq2
  constructor
  · intro hZero
    exact concrete_swap13_lambda_balance_of_zero A lam P hZero h3 h4 hRep5 hQnz
  · intro hBal
    have hZeroRel : pluckerRel (scaleInput lam (QInput A)) P = 0 := by
      exact (plucker_zero_iff_lambda_pairBalance_of_swap13 A lam P h3 h4 hRep5 hQnz).2 hBal
    simpa [pluckerMap] using hZeroRel

theorem concrete_h1Bal1_zero_iff_of_genericStrong
    {n : Nat}
    (S : Anchors n)
    (A : CameraMatrices n)
    (lam : Lambda n)
    (a b c d : Idx n)
    (hvalid : valid a b c d)
    (hGeneric : IsGenericStrong A) :
    pluckerMap
      (fun _ : Fin 1 =>
        swap13Pattern
          (anchorQIndex a b c d)
          (anchorQIndex S.a0 S.b0 S.c0 S.d0)
          (repeatedCoreIndex S)
          (repeatedCoreIndex S))
      (scaleInput lam (QInput A)) ⟨0, by decide⟩ = 0
      ↔
      lam a b c d * lam S.a0 S.b0 S.c0 S.d0 =
        lam c b a d * lam S.c0 S.b0 S.a0 S.d0 := by
  have hiff := concrete_swap13_zero_iff_lambda_balance_of_genericStrong A lam
      (swap13Pattern
        (anchorQIndex a b c d)
        (anchorQIndex S.a0 S.b0 S.c0 S.d0)
        (repeatedCoreIndex S)
        (repeatedCoreIndex S))
      (by simp [swap13Pattern])
      (by simp [swap13Pattern])
      (by simp [swap13Pattern, repeatedCoreIndex_repeatedFirstTwo])
      hGeneric
      (by simpa [anchorQIndex] using hvalid)
      (by simpa [anchorQIndex] using S.valid_anchor)
  simpa [lamAt, swap13Pattern, anchorQIndex, swap13Index, repeatedCoreIndex] using hiff

theorem concrete_h1Bal2_zero_iff_of_genericStrong
    {n : Nat}
    (S : Anchors n)
    (A : CameraMatrices n)
    (lam : Lambda n)
    (a b c d : Idx n)
    (hGeneric : IsGenericStrong A) :
    pluckerMap
      (fun _ : Fin 1 =>
        swap13Pattern
          (anchorQIndex a b S.c0 S.d0)
          (anchorQIndex S.a0 S.b0 c d)
          (repeatedCoreIndex S)
          (repeatedCoreIndex S))
      (scaleInput lam (QInput A)) ⟨0, by decide⟩ = 0
      ↔
      lam a b S.c0 S.d0 * lam S.a0 S.b0 c d =
        lam S.c0 b a S.d0 * lam c S.b0 S.a0 d := by
  have hvalid1 : valid a b S.c0 S.d0 := by
    intro hall
    exact S.hcd hall.2.2
  have hvalid2 : valid S.a0 S.b0 c d := by
    intro hall
    exact S.hab hall.1
  have hiff := concrete_swap13_zero_iff_lambda_balance_of_genericStrong A lam
      (swap13Pattern
        (anchorQIndex a b S.c0 S.d0)
        (anchorQIndex S.a0 S.b0 c d)
        (repeatedCoreIndex S)
        (repeatedCoreIndex S))
      (by simp [swap13Pattern])
      (by simp [swap13Pattern])
      (by simp [swap13Pattern, repeatedCoreIndex_repeatedFirstTwo])
      hGeneric
      (by simpa [anchorQIndex] using hvalid1)
      (by simpa [anchorQIndex] using hvalid2)
  simpa [lamAt, swap13Pattern, anchorQIndex, swap13Index, repeatedCoreIndex] using hiff

theorem concrete_h2Bal1_of_swap12_zero_of_genericStrong
    {n : Nat}
    (S : Anchors n)
    (A : CameraMatrices n)
    (lam : Lambda n)
    (a b : Idx n)
    (hGeneric : IsGenericStrong A)
    (hZero :
      pluckerMap
        (fun _ : Fin 1 =>
          swap12Pattern
            (anchorQIndex a b S.c0 S.d0)
            (anchorQIndex S.a0 S.b0 S.c0 S.d0)
            (repeatedCoreIndex S)
            (repeatedCoreIndex S))
        (scaleInput lam (QInput A)) ⟨0, by decide⟩ = 0) :
    lam a b S.c0 S.d0 * lam S.a0 S.b0 S.c0 S.d0 =
      lam b a S.c0 S.d0 * lam S.b0 S.a0 S.c0 S.d0 := by
  have hvalid1 : valid a b S.c0 S.d0 := by
    intro hall
    exact S.hcd hall.2.2
  have hBal := concrete_swap12_lambda_balance_of_zero_of_genericStrong A lam
      (swap12Pattern
        (anchorQIndex a b S.c0 S.d0)
        (anchorQIndex S.a0 S.b0 S.c0 S.d0)
        (repeatedCoreIndex S)
        (repeatedCoreIndex S))
      hZero
      (by simp [swap12Pattern])
      (by simp [swap12Pattern])
      (by simp [swap12Pattern, repeatedCoreIndex_repeatedFirstTwo])
      hGeneric
      (by simpa [anchorQIndex] using hvalid1)
      (by simpa [anchorQIndex] using S.valid_anchor)
  simpa [lamAt, swap12Pattern, anchorQIndex, swap12Index, repeatedCoreIndex] using hBal

theorem concrete_swap12_zero_iff_lambda_balance_of_genericStrong
    {n : Nat}
    (A : CameraMatrices n)
    (lam : Lambda n)
    (P : PluckerPattern n)
    (h3 : P.p3 = swap12Index P.p1)
    (h4 : P.p4 = swap12Index P.p2)
    (hRep5 : RepeatedFirstTwo P.p5)
    (hGeneric : IsGenericStrong A)
    (hValid1 : validIndex P.p1)
    (hValid2 : validIndex P.p2) :
    pluckerMap (fun _ : Fin 1 => P) (scaleInput lam (QInput A)) ⟨0, by decide⟩ = 0 ↔
      lamAt lam P.p1 * lamAt lam P.p2 = lamAt lam P.p3 * lamAt lam P.p4 := by
  have hq1 : QInput A P.p1 ≠ 0 := qInput_nonzero_of_isGenericStrong A hGeneric P.p1 hValid1
  have hq2 : QInput A P.p2 ≠ 0 := qInput_nonzero_of_isGenericStrong A hGeneric P.p2 hValid2
  have hQnz : QInput A P.p1 * QInput A P.p2 ≠ 0 := mul_ne_zero hq1 hq2
  constructor
  · intro hZero
    exact concrete_swap12_lambda_balance_of_zero A lam P hZero h3 h4 hRep5 hQnz
  · intro hBal
    have hZeroRel : pluckerRel (scaleInput lam (QInput A)) P = 0 := by
      exact (plucker_zero_iff_lambda_pairBalance_of_swap12 A lam P h3 h4 hRep5 hQnz).2 hBal
    simpa [pluckerMap] using hZeroRel

theorem concrete_h2Bal2_of_swap12_zero_of_genericStrong
    {n : Nat}
    (S : Anchors n)
    (A : CameraMatrices n)
    (lam : Lambda n)
    (a b : Idx n)
    (hGeneric : IsGenericStrong A)
    (hZero :
      pluckerMap
        (fun _ : Fin 1 =>
          swap12Pattern
            (anchorQIndex a S.b0 S.c0 S.d0)
            (anchorQIndex S.a0 b S.c0 S.d0)
            (repeatedCoreIndex S)
            (repeatedCoreIndex S))
        (scaleInput lam (QInput A)) ⟨0, by decide⟩ = 0) :
    lam a S.b0 S.c0 S.d0 * lam S.a0 b S.c0 S.d0 =
      lam S.b0 a S.c0 S.d0 * lam b S.a0 S.c0 S.d0 := by
  have hBal := concrete_swap12_lambda_balance_of_zero_of_genericStrong A lam
      (swap12Pattern
        (anchorQIndex a S.b0 S.c0 S.d0)
        (anchorQIndex S.a0 b S.c0 S.d0)
        (repeatedCoreIndex S)
        (repeatedCoreIndex S))
      hZero
      (by simp [swap12Pattern])
      (by simp [swap12Pattern])
      (by simp [swap12Pattern, repeatedCoreIndex_repeatedFirstTwo])
      hGeneric
      (by simpa [anchorQIndex] using S.valid_a_slice a)
      (by simpa [anchorQIndex] using S.valid_b_slice b)
  simpa [lamAt, swap12Pattern, anchorQIndex, swap12Index, repeatedCoreIndex] using hBal

theorem concrete_h2Bal1_zero_iff_of_genericStrong
    {n : Nat}
    (S : Anchors n)
    (A : CameraMatrices n)
    (lam : Lambda n)
    (a b : Idx n)
    (hGeneric : IsGenericStrong A) :
    pluckerMap
      (fun _ : Fin 1 =>
        swap12Pattern
          (anchorQIndex a b S.c0 S.d0)
          (anchorQIndex S.a0 S.b0 S.c0 S.d0)
          (repeatedCoreIndex S)
          (repeatedCoreIndex S))
      (scaleInput lam (QInput A)) ⟨0, by decide⟩ = 0
      ↔
      lam a b S.c0 S.d0 * lam S.a0 S.b0 S.c0 S.d0 =
        lam b a S.c0 S.d0 * lam S.b0 S.a0 S.c0 S.d0 := by
  have hvalid1 : valid a b S.c0 S.d0 := by
    intro hall
    exact S.hcd hall.2.2
  have hiff := concrete_swap12_zero_iff_lambda_balance_of_genericStrong A lam
      (swap12Pattern
        (anchorQIndex a b S.c0 S.d0)
        (anchorQIndex S.a0 S.b0 S.c0 S.d0)
        (repeatedCoreIndex S)
        (repeatedCoreIndex S))
      (by simp [swap12Pattern])
      (by simp [swap12Pattern])
      (by simp [swap12Pattern, repeatedCoreIndex_repeatedFirstTwo])
      hGeneric
      (by simpa [anchorQIndex] using hvalid1)
      (by simpa [anchorQIndex] using S.valid_anchor)
  simpa [lamAt, swap12Pattern, anchorQIndex, swap12Index, repeatedCoreIndex] using hiff

theorem concrete_h2Bal2_zero_iff_of_genericStrong
    {n : Nat}
    (S : Anchors n)
    (A : CameraMatrices n)
    (lam : Lambda n)
    (a b : Idx n)
    (hGeneric : IsGenericStrong A) :
    pluckerMap
      (fun _ : Fin 1 =>
        swap12Pattern
          (anchorQIndex a S.b0 S.c0 S.d0)
          (anchorQIndex S.a0 b S.c0 S.d0)
          (repeatedCoreIndex S)
          (repeatedCoreIndex S))
      (scaleInput lam (QInput A)) ⟨0, by decide⟩ = 0
      ↔
      lam a S.b0 S.c0 S.d0 * lam S.a0 b S.c0 S.d0 =
        lam S.b0 a S.c0 S.d0 * lam b S.a0 S.c0 S.d0 := by
  have hiff := concrete_swap12_zero_iff_lambda_balance_of_genericStrong A lam
      (swap12Pattern
        (anchorQIndex a S.b0 S.c0 S.d0)
        (anchorQIndex S.a0 b S.c0 S.d0)
        (repeatedCoreIndex S)
        (repeatedCoreIndex S))
      (by simp [swap12Pattern])
      (by simp [swap12Pattern])
      (by simp [swap12Pattern, repeatedCoreIndex_repeatedFirstTwo])
      hGeneric
      (by simpa [anchorQIndex] using S.valid_a_slice a)
      (by simpa [anchorQIndex] using S.valid_b_slice b)
  simpa [lamAt, swap12Pattern, anchorQIndex, swap12Index, repeatedCoreIndex] using hiff

theorem concrete_h2_of_swap12_zeros_and_bridge_of_genericStrong
    {n : Nat}
    (S : Anchors n)
    (A : CameraMatrices n)
    (lam : Lambda n)
    (hGeneric : IsGenericStrong A)
    (hZeroBal1 :
      ∀ a b,
        pluckerMap
          (fun _ : Fin 1 =>
            swap12Pattern
              (anchorQIndex a b S.c0 S.d0)
              (anchorQIndex S.a0 S.b0 S.c0 S.d0)
              (repeatedCoreIndex S)
              (repeatedCoreIndex S))
          (scaleInput lam (QInput A)) ⟨0, by decide⟩ = 0)
    (hZeroBal2 :
      ∀ a b,
        pluckerMap
          (fun _ : Fin 1 =>
            swap12Pattern
              (anchorQIndex a S.b0 S.c0 S.d0)
              (anchorQIndex S.a0 b S.c0 S.d0)
              (repeatedCoreIndex S)
              (repeatedCoreIndex S))
          (scaleInput lam (QInput A)) ⟨0, by decide⟩ = 0)
    (hBridge :
      ∀ a b,
        lam b a S.c0 S.d0 * lam S.b0 S.a0 S.c0 S.d0 =
          lam S.b0 a S.c0 S.d0 * lam b S.a0 S.c0 S.d0) :
    ∀ a b,
      lam a b S.c0 S.d0 * lam S.a0 S.b0 S.c0 S.d0 =
        lam a S.b0 S.c0 S.d0 * lam S.a0 b S.c0 S.d0 := by
  have hBal1 :
      ∀ a b,
        lam a b S.c0 S.d0 * lam S.a0 S.b0 S.c0 S.d0 =
          lam b a S.c0 S.d0 * lam S.b0 S.a0 S.c0 S.d0 := by
    intro a b
    exact concrete_h2Bal1_of_swap12_zero_of_genericStrong S A lam a b hGeneric
      (hZeroBal1 a b)
  have hBal2 :
      ∀ a b,
        lam a S.b0 S.c0 S.d0 * lam S.a0 b S.c0 S.d0 =
          lam S.b0 a S.c0 S.d0 * lam b S.a0 S.c0 S.d0 := by
    intro a b
    exact concrete_h2Bal2_of_swap12_zero_of_genericStrong S A lam a b hGeneric
      (hZeroBal2 a b)
  exact h2_of_swap12_balance_triangle S lam hBal1 hBal2 hBridge

theorem concrete_swap34_lambda_balance_of_zero
    {n : Nat}
    (A : CameraMatrices n)
    (lam : Lambda n)
    (P : PluckerPattern n)
    (hZero : pluckerMap (fun _ : Fin 1 => P) (scaleInput lam (QInput A)) ⟨0, by decide⟩ = 0)
    (h3 : P.p3 = swap34Index P.p1)
    (h4 : P.p4 = swap34Index P.p2)
    (hRep5 : RepeatedFirstTwo P.p5)
    (hQnz : QInput A P.p1 * QInput A P.p2 ≠ 0) :
    lamAt lam P.p1 * lamAt lam P.p2 = lamAt lam P.p3 * lamAt lam P.p4 := by
  have hZeroRel : pluckerRel (scaleInput lam (QInput A)) P = 0 := by
    simpa [pluckerMap] using hZero
  exact lambda_pairBalance_of_swap34_zero A lam P hZeroRel h3 h4 hRep5 hQnz

theorem concrete_swap34_lambda_balance_of_zero_of_generic_anchorRows
    {n : Nat}
    (A : CameraMatrices n)
    (lam : Lambda n)
    (P : PluckerPattern n)
    (hZero : pluckerMap (fun _ : Fin 1 => P) (scaleInput lam (QInput A)) ⟨0, by decide⟩ = 0)
    (h3 : P.p3 = swap34Index P.p1)
    (h4 : P.p4 = swap34Index P.p2)
    (hRep5 : RepeatedFirstTwo P.p5)
    (hGeneric : IsGeneric A)
    (hValid1 : validIndex P.p1)
    (hValid2 : validIndex P.p2)
    (hRows1 : AnchorRows P.p1)
    (hRows2 : AnchorRows P.p2) :
    lamAt lam P.p1 * lamAt lam P.p2 = lamAt lam P.p3 * lamAt lam P.p4 := by
  have hq1 : QInput A P.p1 ≠ 0 := qInput_nonzero_of_isGeneric_anchorRows A hGeneric P.p1 hValid1 hRows1
  have hq2 : QInput A P.p2 ≠ 0 := qInput_nonzero_of_isGeneric_anchorRows A hGeneric P.p2 hValid2 hRows2
  have hQnz : QInput A P.p1 * QInput A P.p2 ≠ 0 := mul_ne_zero hq1 hq2
  exact concrete_swap34_lambda_balance_of_zero A lam P hZero h3 h4 hRep5 hQnz

theorem concrete_swap34_family_lambda_balance_of_zero_of_generic_anchorRows
    {n m : Nat}
    (A : CameraMatrices n)
    (lam : Lambda n)
    (patterns : Fin m → PluckerPattern n)
    (hZero : ∀ t, pluckerMap patterns (scaleInput lam (QInput A)) t = 0)
    (h3 : ∀ t, (patterns t).p3 = swap34Index (patterns t).p1)
    (h4 : ∀ t, (patterns t).p4 = swap34Index (patterns t).p2)
    (hRep5 : ∀ t, RepeatedFirstTwo (patterns t).p5)
    (hGeneric : IsGeneric A)
    (hValid1 : ∀ t, validIndex (patterns t).p1)
    (hValid2 : ∀ t, validIndex (patterns t).p2)
    (hRows1 : ∀ t, AnchorRows (patterns t).p1)
    (hRows2 : ∀ t, AnchorRows (patterns t).p2) :
    ∀ t, lamAt lam (patterns t).p1 * lamAt lam (patterns t).p2 =
      lamAt lam (patterns t).p3 * lamAt lam (patterns t).p4 := by
  intro t
  have hq1 : QInput A (patterns t).p1 ≠ 0 := by
    exact qInput_nonzero_of_isGeneric_anchorRows A hGeneric (patterns t).p1 (hValid1 t) (hRows1 t)
  have hq2 : QInput A (patterns t).p2 ≠ 0 := by
    exact qInput_nonzero_of_isGeneric_anchorRows A hGeneric (patterns t).p2 (hValid2 t) (hRows2 t)
  have hQnz : QInput A (patterns t).p1 * QInput A (patterns t).p2 ≠ 0 := mul_ne_zero hq1 hq2
  have hZeroRel : pluckerRel (scaleInput lam (QInput A)) (patterns t) = 0 := by
    simpa [pluckerMap] using hZero t
  exact lambda_pairBalance_of_swap34_zero A lam (patterns t) hZeroRel (h3 t) (h4 t) (hRep5 t) hQnz

theorem concrete_swap34_lambda_balance_of_zero_of_genericStrong
    {n : Nat}
    (A : CameraMatrices n)
    (lam : Lambda n)
    (P : PluckerPattern n)
    (hZero : pluckerMap (fun _ : Fin 1 => P) (scaleInput lam (QInput A)) ⟨0, by decide⟩ = 0)
    (h3 : P.p3 = swap34Index P.p1)
    (h4 : P.p4 = swap34Index P.p2)
    (hRep5 : RepeatedFirstTwo P.p5)
    (hGeneric : IsGenericStrong A)
    (hValid1 : validIndex P.p1)
    (hValid2 : validIndex P.p2) :
    lamAt lam P.p1 * lamAt lam P.p2 = lamAt lam P.p3 * lamAt lam P.p4 := by
  have hq1 : QInput A P.p1 ≠ 0 := qInput_nonzero_of_isGenericStrong A hGeneric P.p1 hValid1
  have hq2 : QInput A P.p2 ≠ 0 := qInput_nonzero_of_isGenericStrong A hGeneric P.p2 hValid2
  have hQnz : QInput A P.p1 * QInput A P.p2 ≠ 0 := mul_ne_zero hq1 hq2
  exact concrete_swap34_lambda_balance_of_zero A lam P hZero h3 h4 hRep5 hQnz

theorem concrete_swap34_family_lambda_balance_of_zero_of_genericStrong
    {n m : Nat}
    (A : CameraMatrices n)
    (lam : Lambda n)
    (patterns : Fin m → PluckerPattern n)
    (hZero : ∀ t, pluckerMap patterns (scaleInput lam (QInput A)) t = 0)
    (h3 : ∀ t, (patterns t).p3 = swap34Index (patterns t).p1)
    (h4 : ∀ t, (patterns t).p4 = swap34Index (patterns t).p2)
    (hRep5 : ∀ t, RepeatedFirstTwo (patterns t).p5)
    (hGeneric : IsGenericStrong A)
    (hValid1 : ∀ t, validIndex (patterns t).p1)
    (hValid2 : ∀ t, validIndex (patterns t).p2) :
    ∀ t, lamAt lam (patterns t).p1 * lamAt lam (patterns t).p2 =
      lamAt lam (patterns t).p3 * lamAt lam (patterns t).p4 := by
  intro t
  have hq1 : QInput A (patterns t).p1 ≠ 0 := qInput_nonzero_of_isGenericStrong A hGeneric (patterns t).p1 (hValid1 t)
  have hq2 : QInput A (patterns t).p2 ≠ 0 := qInput_nonzero_of_isGenericStrong A hGeneric (patterns t).p2 (hValid2 t)
  have hQnz : QInput A (patterns t).p1 * QInput A (patterns t).p2 ≠ 0 := mul_ne_zero hq1 hq2
  have hZeroRel : pluckerRel (scaleInput lam (QInput A)) (patterns t) = 0 := by
    simpa [pluckerMap] using hZero t
  exact lambda_pairBalance_of_swap34_zero A lam (patterns t) hZeroRel (h3 t) (h4 t) (hRep5 t) hQnz

theorem concrete_h3Bal1_of_swap34_zero_of_genericStrong
    {n : Nat}
    (S : Anchors n)
    (A : CameraMatrices n)
    (lam : Lambda n)
    (c d : Idx n)
    (hGeneric : IsGenericStrong A)
    (hZero :
      pluckerMap
        (fun _ : Fin 1 =>
          swap34Pattern
            (anchorQIndex S.a0 S.b0 c d)
            (anchorQIndex S.a0 S.b0 S.c0 S.d0)
            (repeatedCoreIndex S)
            (repeatedCoreIndex S))
        (scaleInput lam (QInput A)) ⟨0, by decide⟩ = 0) :
    lam S.a0 S.b0 c d * lam S.a0 S.b0 S.c0 S.d0 =
      lam S.a0 S.b0 d c * lam S.a0 S.b0 S.d0 S.c0 := by
  have hvalid1 : valid S.a0 S.b0 c d := by
    intro hall
    exact S.hab hall.1
  have hBal := concrete_swap34_lambda_balance_of_zero_of_genericStrong A lam
      (swap34Pattern
        (anchorQIndex S.a0 S.b0 c d)
        (anchorQIndex S.a0 S.b0 S.c0 S.d0)
        (repeatedCoreIndex S)
        (repeatedCoreIndex S))
      hZero
      (by simp [swap34Pattern])
      (by simp [swap34Pattern])
      (by simp [swap34Pattern, repeatedCoreIndex_repeatedFirstTwo])
      hGeneric
      (by simpa [anchorQIndex] using hvalid1)
      (by simpa [anchorQIndex] using S.valid_anchor)
  simpa [lamAt, swap34Pattern, anchorQIndex, swap34Index, repeatedCoreIndex] using hBal

theorem concrete_swap34_zero_iff_lambda_balance_of_genericStrong
    {n : Nat}
    (A : CameraMatrices n)
    (lam : Lambda n)
    (P : PluckerPattern n)
    (h3 : P.p3 = swap34Index P.p1)
    (h4 : P.p4 = swap34Index P.p2)
    (hRep5 : RepeatedFirstTwo P.p5)
    (hGeneric : IsGenericStrong A)
    (hValid1 : validIndex P.p1)
    (hValid2 : validIndex P.p2) :
    pluckerMap (fun _ : Fin 1 => P) (scaleInput lam (QInput A)) ⟨0, by decide⟩ = 0 ↔
      lamAt lam P.p1 * lamAt lam P.p2 = lamAt lam P.p3 * lamAt lam P.p4 := by
  have hq1 : QInput A P.p1 ≠ 0 := qInput_nonzero_of_isGenericStrong A hGeneric P.p1 hValid1
  have hq2 : QInput A P.p2 ≠ 0 := qInput_nonzero_of_isGenericStrong A hGeneric P.p2 hValid2
  have hQnz : QInput A P.p1 * QInput A P.p2 ≠ 0 := mul_ne_zero hq1 hq2
  constructor
  · intro hZero
    exact concrete_swap34_lambda_balance_of_zero A lam P hZero h3 h4 hRep5 hQnz
  · intro hBal
    have hZeroRel : pluckerRel (scaleInput lam (QInput A)) P = 0 := by
      exact (plucker_zero_iff_lambda_pairBalance_of_swap34 A lam P h3 h4 hRep5 hQnz).2 hBal
    simpa [pluckerMap] using hZeroRel

theorem concrete_h3Bal2_of_swap34_zero_of_genericStrong
    {n : Nat}
    (S : Anchors n)
    (A : CameraMatrices n)
    (lam : Lambda n)
    (c d : Idx n)
    (hGeneric : IsGenericStrong A)
    (hZero :
      pluckerMap
        (fun _ : Fin 1 =>
          swap34Pattern
            (anchorQIndex S.a0 S.b0 c S.d0)
            (anchorQIndex S.a0 S.b0 S.c0 d)
            (repeatedCoreIndex S)
            (repeatedCoreIndex S))
        (scaleInput lam (QInput A)) ⟨0, by decide⟩ = 0) :
    lam S.a0 S.b0 c S.d0 * lam S.a0 S.b0 S.c0 d =
      lam S.a0 S.b0 S.d0 c * lam S.a0 S.b0 d S.c0 := by
  have hvalid1 : valid S.a0 S.b0 c S.d0 := by
    intro hall
    exact S.hab hall.1
  have hvalid2 : valid S.a0 S.b0 S.c0 d := by
    intro hall
    exact S.hab hall.1
  have hBal := concrete_swap34_lambda_balance_of_zero_of_genericStrong A lam
      (swap34Pattern
        (anchorQIndex S.a0 S.b0 c S.d0)
        (anchorQIndex S.a0 S.b0 S.c0 d)
        (repeatedCoreIndex S)
        (repeatedCoreIndex S))
      hZero
      (by simp [swap34Pattern])
      (by simp [swap34Pattern])
      (by simp [swap34Pattern, repeatedCoreIndex_repeatedFirstTwo])
      hGeneric
      (by simpa [anchorQIndex] using hvalid1)
      (by simpa [anchorQIndex] using hvalid2)
  simpa [lamAt, swap34Pattern, anchorQIndex, swap34Index, repeatedCoreIndex] using hBal

theorem concrete_h3Bal1_zero_iff_of_genericStrong
    {n : Nat}
    (S : Anchors n)
    (A : CameraMatrices n)
    (lam : Lambda n)
    (c d : Idx n)
    (hGeneric : IsGenericStrong A) :
    pluckerMap
      (fun _ : Fin 1 =>
        swap34Pattern
          (anchorQIndex S.a0 S.b0 c d)
          (anchorQIndex S.a0 S.b0 S.c0 S.d0)
          (repeatedCoreIndex S)
          (repeatedCoreIndex S))
      (scaleInput lam (QInput A)) ⟨0, by decide⟩ = 0
      ↔
      lam S.a0 S.b0 c d * lam S.a0 S.b0 S.c0 S.d0 =
        lam S.a0 S.b0 d c * lam S.a0 S.b0 S.d0 S.c0 := by
  have hvalid1 : valid S.a0 S.b0 c d := by
    intro hall
    exact S.hab hall.1
  have hiff := concrete_swap34_zero_iff_lambda_balance_of_genericStrong A lam
      (swap34Pattern
        (anchorQIndex S.a0 S.b0 c d)
        (anchorQIndex S.a0 S.b0 S.c0 S.d0)
        (repeatedCoreIndex S)
        (repeatedCoreIndex S))
      (by simp [swap34Pattern])
      (by simp [swap34Pattern])
      (by simp [swap34Pattern, repeatedCoreIndex_repeatedFirstTwo])
      hGeneric
      (by simpa [anchorQIndex] using hvalid1)
      (by simpa [anchorQIndex] using S.valid_anchor)
  simpa [lamAt, swap34Pattern, anchorQIndex, swap34Index, repeatedCoreIndex] using hiff

theorem concrete_h3Bal2_zero_iff_of_genericStrong
    {n : Nat}
    (S : Anchors n)
    (A : CameraMatrices n)
    (lam : Lambda n)
    (c d : Idx n)
    (hGeneric : IsGenericStrong A) :
    pluckerMap
      (fun _ : Fin 1 =>
        swap34Pattern
          (anchorQIndex S.a0 S.b0 c S.d0)
          (anchorQIndex S.a0 S.b0 S.c0 d)
          (repeatedCoreIndex S)
          (repeatedCoreIndex S))
      (scaleInput lam (QInput A)) ⟨0, by decide⟩ = 0
      ↔
      lam S.a0 S.b0 c S.d0 * lam S.a0 S.b0 S.c0 d =
        lam S.a0 S.b0 S.d0 c * lam S.a0 S.b0 d S.c0 := by
  have hvalid1 : valid S.a0 S.b0 c S.d0 := by
    intro hall
    exact S.hab hall.1
  have hvalid2 : valid S.a0 S.b0 S.c0 d := by
    intro hall
    exact S.hab hall.1
  have hiff := concrete_swap34_zero_iff_lambda_balance_of_genericStrong A lam
      (swap34Pattern
        (anchorQIndex S.a0 S.b0 c S.d0)
        (anchorQIndex S.a0 S.b0 S.c0 d)
        (repeatedCoreIndex S)
        (repeatedCoreIndex S))
      (by simp [swap34Pattern])
      (by simp [swap34Pattern])
      (by simp [swap34Pattern, repeatedCoreIndex_repeatedFirstTwo])
      hGeneric
      (by simpa [anchorQIndex] using hvalid1)
      (by simpa [anchorQIndex] using hvalid2)
  simpa [lamAt, swap34Pattern, anchorQIndex, swap34Index, repeatedCoreIndex] using hiff

structure SwapBalanceCondition
    {n : Nat}
    (S : Anchors n)
    (lam : Lambda n) : Prop where
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

structure HConditionSet
    {n : Nat}
    (S : Anchors n)
    (lam : Lambda n) : Prop where
  h1 :
    ∀ a b c d, valid a b c d →
      lam a b c d * lam S.a0 S.b0 S.c0 S.d0 =
        lam a b S.c0 S.d0 * lam S.a0 S.b0 c d
  h2 :
    ∀ a b,
      lam a b S.c0 S.d0 * lam S.a0 S.b0 S.c0 S.d0 =
        lam a S.b0 S.c0 S.d0 * lam S.a0 b S.c0 S.d0
  h3 :
    ∀ c d,
      lam S.a0 S.b0 c d * lam S.a0 S.b0 S.c0 S.d0 =
        lam S.a0 S.b0 c S.d0 * lam S.a0 S.b0 S.c0 d

theorem separable_of_hConditionSet
    {n : Nat}
    (S : Anchors n)
    (lam : Lambda n)
    (hNZ : nonzeroOnValid lam)
    (hH : HConditionSet S lam) :
    separable lam := by
  exact separable_of_three_bilinear_identities S lam hNZ hH.h1 hH.h2 hH.h3

theorem hConditionSet_of_separable
    {n : Nat}
    (S : Anchors n)
    (lam : Lambda n)
    (hSep : separable lam) :
    HConditionSet S lam := by
  exact ⟨
    h1Condition_of_separable S lam hSep,
    h2Condition_of_separable S lam hSep,
    h3Condition_of_separable S lam hSep
  ⟩

structure BridgeConditionSet
    {n : Nat}
    (S : Anchors n)
    (lam : Lambda n) : Prop where
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

theorem bridgeConditionSet_of_hConditions_and_swapBalance
    {n : Nat}
    (S : Anchors n)
    (lam : Lambda n)
    (hH : HConditionSet S lam)
    (hBal : SwapBalanceCondition S lam) :
    BridgeConditionSet S lam := by
  refine ⟨?_, ?_, ?_⟩
  · exact bridge1_of_h1_and_swap13_balances S lam hH.h1 hBal.h1Bal1 hBal.h1Bal2
  · exact bridge2_of_h2_and_swap12_balances S lam hH.h2 hBal.h2Bal1 hBal.h2Bal2
  · exact bridge3_of_h3_and_swap34_balances S lam hH.h3 hBal.h3Bal1 hBal.h3Bal2

theorem hConditionSet_of_swapBalance_and_bridgeConditions
    {n : Nat}
    (S : Anchors n)
    (lam : Lambda n)
    (hBal : SwapBalanceCondition S lam)
    (hBridge : BridgeConditionSet S lam) :
    HConditionSet S lam := by
  refine ⟨?_, ?_, ?_⟩
  · exact h1_of_swap13_balance_triangle S lam hBal.h1Bal1 hBal.h1Bal2 hBridge.bridge1
  · exact h2_of_swap12_balance_triangle S lam hBal.h2Bal1 hBal.h2Bal2 hBridge.bridge2
  · exact h3_of_swap34_balance_triangle S lam hBal.h3Bal1 hBal.h3Bal2 hBridge.bridge3

theorem bridgeConditionSet_iff_hConditionSet_of_swapBalance
    {n : Nat}
    (S : Anchors n)
    (lam : Lambda n)
    (hBal : SwapBalanceCondition S lam) :
    BridgeConditionSet S lam ↔ HConditionSet S lam := by
  constructor
  · intro hBridge
    exact hConditionSet_of_swapBalance_and_bridgeConditions S lam hBal hBridge
  · intro hH
    exact bridgeConditionSet_of_hConditions_and_swapBalance S lam hH hBal

theorem hConditionSet_iff_separable
    {n : Nat}
    (S : Anchors n)
    (lam : Lambda n)
    (hNZ : nonzeroOnValid lam) :
    HConditionSet S lam ↔ separable lam := by
  constructor
  · intro hH
    exact separable_of_hConditionSet S lam hNZ hH
  · intro hSep
    exact hConditionSet_of_separable S lam hSep

theorem separable_of_swapBalance_and_bridgeConditions
    {n : Nat}
    (S : Anchors n)
    (lam : Lambda n)
    (hNZ : nonzeroOnValid lam)
    (hBal : SwapBalanceCondition S lam)
    (hBridge : BridgeConditionSet S lam) :
    separable lam := by
  have h1 :
      ∀ a b c d, valid a b c d →
        lam a b c d * lam S.a0 S.b0 S.c0 S.d0 =
          lam a b S.c0 S.d0 * lam S.a0 S.b0 c d := by
    exact h1_of_swap13_balance_triangle S lam hBal.h1Bal1 hBal.h1Bal2 hBridge.bridge1
  have h2 :
      ∀ a b,
        lam a b S.c0 S.d0 * lam S.a0 S.b0 S.c0 S.d0 =
          lam a S.b0 S.c0 S.d0 * lam S.a0 b S.c0 S.d0 := by
    exact h2_of_swap12_balance_triangle S lam hBal.h2Bal1 hBal.h2Bal2 hBridge.bridge2
  have h3 :
      ∀ c d,
        lam S.a0 S.b0 c d * lam S.a0 S.b0 S.c0 S.d0 =
          lam S.a0 S.b0 c S.d0 * lam S.a0 S.b0 S.c0 d := by
    exact h3_of_swap34_balance_triangle S lam hBal.h3Bal1 hBal.h3Bal2 hBridge.bridge3
  exact separable_of_three_bilinear_identities S lam hNZ h1 h2 h3

theorem bridgeConditionSet_of_separable
    {n : Nat}
    (S : Anchors n)
    (lam : Lambda n)
    (hSep : separable lam) :
    BridgeConditionSet S lam := by
  exact ⟨
    bridge1_of_separable S lam hSep,
    bridge2_of_separable S lam hSep,
    bridge3_of_separable S lam hSep
  ⟩

theorem bridgeConditionSet_of_bridgeRecoverability
    {n : Nat}
    (R : BridgeRecoverability n)
    (S : Anchors n)
    (A : CameraMatrices n)
    (lam : Lambda n)
    (hGeneric : IsGenericStrong A)
    (hZeroH1Bal1 :
      ∀ a b c d, valid a b c d →
        pluckerMap
          (fun _ : Fin 1 =>
            swap13Pattern
              (anchorQIndex a b c d)
              (anchorQIndex S.a0 S.b0 S.c0 S.d0)
              (repeatedCoreIndex S)
              (repeatedCoreIndex S))
          (scaleInput lam (QInput A)) ⟨0, by decide⟩ = 0)
    (hZeroH1Bal2 :
      ∀ a b c d, valid a b c d →
        pluckerMap
          (fun _ : Fin 1 =>
            swap13Pattern
              (anchorQIndex a b S.c0 S.d0)
              (anchorQIndex S.a0 S.b0 c d)
              (repeatedCoreIndex S)
              (repeatedCoreIndex S))
          (scaleInput lam (QInput A)) ⟨0, by decide⟩ = 0)
    (hZeroH2Bal1 :
      ∀ a b,
        pluckerMap
          (fun _ : Fin 1 =>
            swap12Pattern
              (anchorQIndex a b S.c0 S.d0)
              (anchorQIndex S.a0 S.b0 S.c0 S.d0)
              (repeatedCoreIndex S)
              (repeatedCoreIndex S))
          (scaleInput lam (QInput A)) ⟨0, by decide⟩ = 0)
    (hZeroH2Bal2 :
      ∀ a b,
        pluckerMap
          (fun _ : Fin 1 =>
            swap12Pattern
              (anchorQIndex a S.b0 S.c0 S.d0)
              (anchorQIndex S.a0 b S.c0 S.d0)
              (repeatedCoreIndex S)
              (repeatedCoreIndex S))
          (scaleInput lam (QInput A)) ⟨0, by decide⟩ = 0)
    (hZeroH3Bal1 :
      ∀ c d,
        pluckerMap
          (fun _ : Fin 1 =>
            swap34Pattern
              (anchorQIndex S.a0 S.b0 c d)
              (anchorQIndex S.a0 S.b0 S.c0 S.d0)
              (repeatedCoreIndex S)
              (repeatedCoreIndex S))
          (scaleInput lam (QInput A)) ⟨0, by decide⟩ = 0)
    (hZeroH3Bal2 :
      ∀ c d,
        pluckerMap
          (fun _ : Fin 1 =>
            swap34Pattern
              (anchorQIndex S.a0 S.b0 c S.d0)
              (anchorQIndex S.a0 S.b0 S.c0 d)
              (repeatedCoreIndex S)
              (repeatedCoreIndex S))
          (scaleInput lam (QInput A)) ⟨0, by decide⟩ = 0) :
    BridgeConditionSet S lam := by
  rcases R S A lam hGeneric
    hZeroH1Bal1 hZeroH1Bal2 hZeroH2Bal1 hZeroH2Bal2 hZeroH3Bal1 hZeroH3Bal2
    with ⟨hBridge1, hBridge2, hBridge3⟩
  exact ⟨hBridge1, hBridge2, hBridge3⟩

theorem swapZeroMapWithAnchors_zero_implies_swapBalance_of_genericStrong
    {n : Nat}
    (S : Anchors n)
    (A : CameraMatrices n)
    (lam : Lambda n)
    (hGeneric : IsGenericStrong A) :
    (∀ idx, swapZeroMapWithAnchors S (scaleInput lam (QInput A)) idx = 0) →
      SwapBalanceCondition S lam := by
  intro hZero
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · intro a b c d hvalid
    exact (concrete_h1Bal1_zero_iff_of_genericStrong S A lam a b c d hvalid hGeneric).1
      (by simpa [swapZeroMapWithAnchors] using hZero (SwapZeroIndex.h1Bal1 a b c d))
  · intro a b c d hvalid
    exact (concrete_h1Bal2_zero_iff_of_genericStrong S A lam a b c d hGeneric).1
      (by simpa [swapZeroMapWithAnchors] using hZero (SwapZeroIndex.h1Bal2 a b c d))
  · intro a b
    exact (concrete_h2Bal1_zero_iff_of_genericStrong S A lam a b hGeneric).1
      (by simpa [swapZeroMapWithAnchors] using hZero (SwapZeroIndex.h2Bal1 a b))
  · intro a b
    exact (concrete_h2Bal2_zero_iff_of_genericStrong S A lam a b hGeneric).1
      (by simpa [swapZeroMapWithAnchors] using hZero (SwapZeroIndex.h2Bal2 a b))
  · intro c d
    exact (concrete_h3Bal1_zero_iff_of_genericStrong S A lam c d hGeneric).1
      (by simpa [swapZeroMapWithAnchors] using hZero (SwapZeroIndex.h3Bal1 c d))
  · intro c d
    exact (concrete_h3Bal2_zero_iff_of_genericStrong S A lam c d hGeneric).1
      (by simpa [swapZeroMapWithAnchors] using hZero (SwapZeroIndex.h3Bal2 c d))

theorem swapZeroMap_zero_implies_swapBalance_of_genericStrong
    {n : Nat}
    (hn : 5 ≤ n)
    (A : CameraMatrices n)
    (lam : Lambda n)
    (hGeneric : IsGenericStrong A) :
    (∀ idx, swapZeroMap n hn (scaleInput lam (QInput A)) idx = 0) →
      SwapBalanceCondition (canonicalAnchors n hn) lam := by
  exact swapZeroMapWithAnchors_zero_implies_swapBalance_of_genericStrong
    (canonicalAnchors n hn) A lam hGeneric

theorem swapZeroMapFin_zero_implies_swapBalance_of_genericStrong
    {n : Nat}
    (hn : 5 ≤ n)
    (A : CameraMatrices n)
    (lam : Lambda n)
    (hGeneric : IsGenericStrong A)
    (hZero : ∀ t : Fin (Fintype.card (SwapZeroIndex n)),
      swapZeroMapFin n hn (scaleInput lam (QInput A)) t = 0) :
    SwapBalanceCondition (canonicalAnchors n hn) lam := by
  have hZero' : ∀ idx, swapZeroMap n hn (scaleInput lam (QInput A)) idx = 0 := by
    intro idx
    simpa [swapZeroMapFin] using hZero ((Fintype.equivFin (SwapZeroIndex n)) idx)
  exact swapZeroMap_zero_implies_swapBalance_of_genericStrong hn A lam hGeneric hZero'

theorem zeroFamilies_of_swapBalance_of_genericStrong
    {n : Nat}
    (S : Anchors n)
    (A : CameraMatrices n)
    (lam : Lambda n)
    (hGeneric : IsGenericStrong A)
    (hBal : SwapBalanceCondition S lam) :
    (∀ a b c d, valid a b c d →
      pluckerMap
        (fun _ : Fin 1 =>
          swap13Pattern
            (anchorQIndex a b c d)
            (anchorQIndex S.a0 S.b0 S.c0 S.d0)
            (repeatedCoreIndex S)
            (repeatedCoreIndex S))
        (scaleInput lam (QInput A)) ⟨0, by decide⟩ = 0) ∧
    (∀ a b c d, valid a b c d →
      pluckerMap
        (fun _ : Fin 1 =>
          swap13Pattern
            (anchorQIndex a b S.c0 S.d0)
            (anchorQIndex S.a0 S.b0 c d)
            (repeatedCoreIndex S)
            (repeatedCoreIndex S))
        (scaleInput lam (QInput A)) ⟨0, by decide⟩ = 0) ∧
    (∀ a b,
      pluckerMap
        (fun _ : Fin 1 =>
          swap12Pattern
            (anchorQIndex a b S.c0 S.d0)
            (anchorQIndex S.a0 S.b0 S.c0 S.d0)
            (repeatedCoreIndex S)
            (repeatedCoreIndex S))
        (scaleInput lam (QInput A)) ⟨0, by decide⟩ = 0) ∧
    (∀ a b,
      pluckerMap
        (fun _ : Fin 1 =>
          swap12Pattern
            (anchorQIndex a S.b0 S.c0 S.d0)
            (anchorQIndex S.a0 b S.c0 S.d0)
            (repeatedCoreIndex S)
            (repeatedCoreIndex S))
        (scaleInput lam (QInput A)) ⟨0, by decide⟩ = 0) ∧
    (∀ c d,
      pluckerMap
        (fun _ : Fin 1 =>
          swap34Pattern
            (anchorQIndex S.a0 S.b0 c d)
            (anchorQIndex S.a0 S.b0 S.c0 S.d0)
            (repeatedCoreIndex S)
            (repeatedCoreIndex S))
        (scaleInput lam (QInput A)) ⟨0, by decide⟩ = 0) ∧
    (∀ c d,
      pluckerMap
        (fun _ : Fin 1 =>
          swap34Pattern
            (anchorQIndex S.a0 S.b0 c S.d0)
            (anchorQIndex S.a0 S.b0 S.c0 d)
            (repeatedCoreIndex S)
            (repeatedCoreIndex S))
        (scaleInput lam (QInput A)) ⟨0, by decide⟩ = 0) := by
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · intro a b c d hvalid
    exact (concrete_h1Bal1_zero_iff_of_genericStrong S A lam a b c d hvalid hGeneric).2
      (hBal.h1Bal1 a b c d hvalid)
  · intro a b c d hvalid
    exact (concrete_h1Bal2_zero_iff_of_genericStrong S A lam a b c d hGeneric).2
      (hBal.h1Bal2 a b c d hvalid)
  · intro a b
    exact (concrete_h2Bal1_zero_iff_of_genericStrong S A lam a b hGeneric).2
      (hBal.h2Bal1 a b)
  · intro a b
    exact (concrete_h2Bal2_zero_iff_of_genericStrong S A lam a b hGeneric).2
      (hBal.h2Bal2 a b)
  · intro c d
    exact (concrete_h3Bal1_zero_iff_of_genericStrong S A lam c d hGeneric).2
      (hBal.h3Bal1 c d)
  · intro c d
    exact (concrete_h3Bal2_zero_iff_of_genericStrong S A lam c d hGeneric).2
      (hBal.h3Bal2 c d)

theorem separable_of_swapZeroMapWithAnchors_zero_and_bridgeConditions_of_genericStrong
    {n : Nat}
    (S : Anchors n)
    (A : CameraMatrices n)
    (lam : Lambda n)
    (hNZ : nonzeroOnValid lam)
    (hGeneric : IsGenericStrong A)
    (hZero : ∀ idx, swapZeroMapWithAnchors S (scaleInput lam (QInput A)) idx = 0)
    (hBridge : BridgeConditionSet S lam) :
    separable lam := by
  have hBal : SwapBalanceCondition S lam := by
    exact swapZeroMapWithAnchors_zero_implies_swapBalance_of_genericStrong S A lam hGeneric hZero
  exact separable_of_swapBalance_and_bridgeConditions S lam hNZ hBal hBridge

theorem separable_of_swapZeroMap_zero_and_bridgeConditions_of_genericStrong
    {n : Nat}
    (hn : 5 ≤ n)
    (A : CameraMatrices n)
    (lam : Lambda n)
    (hNZ : nonzeroOnValid lam)
    (hGeneric : IsGenericStrong A)
    (hZero : ∀ idx, swapZeroMap n hn (scaleInput lam (QInput A)) idx = 0)
    (hBridge : BridgeConditionSet (canonicalAnchors n hn) lam) :
    separable lam := by
  exact separable_of_swapZeroMapWithAnchors_zero_and_bridgeConditions_of_genericStrong
    (canonicalAnchors n hn) A lam hNZ hGeneric hZero hBridge

theorem separable_of_swapZeroMapFin_zero_and_bridgeConditions_of_genericStrong
    {n : Nat}
    (hn : 5 ≤ n)
    (A : CameraMatrices n)
    (lam : Lambda n)
    (hNZ : nonzeroOnValid lam)
    (hGeneric : IsGenericStrong A)
    (hZero : ∀ t : Fin (Fintype.card (SwapZeroIndex n)),
      swapZeroMapFin n hn (scaleInput lam (QInput A)) t = 0)
    (hBridge : BridgeConditionSet (canonicalAnchors n hn) lam) :
    separable lam := by
  have hZero' : ∀ idx, swapZeroMap n hn (scaleInput lam (QInput A)) idx = 0 := by
    intro idx
    simpa [swapZeroMapFin] using hZero ((Fintype.equivFin (SwapZeroIndex n)) idx)
  exact separable_of_swapZeroMap_zero_and_bridgeConditions_of_genericStrong
    hn A lam hNZ hGeneric hZero' hBridge

theorem concrete_h3_of_swap34_zeros_and_bridge_of_genericStrong
    {n : Nat}
    (S : Anchors n)
    (A : CameraMatrices n)
    (lam : Lambda n)
    (hGeneric : IsGenericStrong A)
    (hZeroBal1 :
      ∀ c d,
        pluckerMap
          (fun _ : Fin 1 =>
            swap34Pattern
              (anchorQIndex S.a0 S.b0 c d)
              (anchorQIndex S.a0 S.b0 S.c0 S.d0)
              (repeatedCoreIndex S)
              (repeatedCoreIndex S))
          (scaleInput lam (QInput A)) ⟨0, by decide⟩ = 0)
    (hZeroBal2 :
      ∀ c d,
        pluckerMap
          (fun _ : Fin 1 =>
            swap34Pattern
              (anchorQIndex S.a0 S.b0 c S.d0)
              (anchorQIndex S.a0 S.b0 S.c0 d)
              (repeatedCoreIndex S)
              (repeatedCoreIndex S))
          (scaleInput lam (QInput A)) ⟨0, by decide⟩ = 0)
    (hBridge :
      ∀ c d,
        lam S.a0 S.b0 d c * lam S.a0 S.b0 S.d0 S.c0 =
          lam S.a0 S.b0 S.d0 c * lam S.a0 S.b0 d S.c0) :
    ∀ c d,
      lam S.a0 S.b0 c d * lam S.a0 S.b0 S.c0 S.d0 =
        lam S.a0 S.b0 c S.d0 * lam S.a0 S.b0 S.c0 d := by
  have hBal1 :
      ∀ c d,
        lam S.a0 S.b0 c d * lam S.a0 S.b0 S.c0 S.d0 =
          lam S.a0 S.b0 d c * lam S.a0 S.b0 S.d0 S.c0 := by
    intro c d
    exact concrete_h3Bal1_of_swap34_zero_of_genericStrong S A lam c d hGeneric
      (hZeroBal1 c d)
  have hBal2 :
      ∀ c d,
        lam S.a0 S.b0 c S.d0 * lam S.a0 S.b0 S.c0 d =
          lam S.a0 S.b0 S.d0 c * lam S.a0 S.b0 d S.c0 := by
    intro c d
    exact concrete_h3Bal2_of_swap34_zero_of_genericStrong S A lam c d hGeneric
      (hZeroBal2 c d)
  exact h3_of_swap34_balance_triangle S lam hBal1 hBal2 hBridge

theorem concrete_separable_of_three_bilinear_identities
    {n : Nat}
    (S : Anchors n)
    (lam : Lambda n)
    (hNZ : nonzeroOnValid lam)
    (h1 :
      ∀ a b c d, valid a b c d →
        lam a b c d * lam S.a0 S.b0 S.c0 S.d0 =
          lam a b S.c0 S.d0 * lam S.a0 S.b0 c d)
    (h2 :
      ∀ a b,
        lam a b S.c0 S.d0 * lam S.a0 S.b0 S.c0 S.d0 =
          lam a S.b0 S.c0 S.d0 * lam S.a0 b S.c0 S.d0)
    (h3 :
      ∀ c d,
        lam S.a0 S.b0 c d * lam S.a0 S.b0 S.c0 S.d0 =
          lam S.a0 S.b0 c S.d0 * lam S.a0 S.b0 S.c0 d) :
    separable lam := by
  exact separable_of_three_bilinear_identities S lam hNZ h1 h2 h3

theorem concrete_h2_of_swap12_balance_triangle
    {n : Nat}
    (S : Anchors n)
    (lam : Lambda n)
    (hBal1 :
      ∀ a b,
        lam a b S.c0 S.d0 * lam S.a0 S.b0 S.c0 S.d0 =
          lam b a S.c0 S.d0 * lam S.b0 S.a0 S.c0 S.d0)
    (hBal2 :
      ∀ a b,
        lam a S.b0 S.c0 S.d0 * lam S.a0 b S.c0 S.d0 =
          lam S.b0 a S.c0 S.d0 * lam b S.a0 S.c0 S.d0)
    (hBridge :
      ∀ a b,
        lam b a S.c0 S.d0 * lam S.b0 S.a0 S.c0 S.d0 =
          lam S.b0 a S.c0 S.d0 * lam b S.a0 S.c0 S.d0) :
    ∀ a b,
      lam a b S.c0 S.d0 * lam S.a0 S.b0 S.c0 S.d0 =
        lam a S.b0 S.c0 S.d0 * lam S.a0 b S.c0 S.d0 := by
  exact h2_of_swap12_balance_triangle S lam hBal1 hBal2 hBridge

theorem concrete_h1_of_swap13_balance_triangle
    {n : Nat}
    (S : Anchors n)
    (lam : Lambda n)
    (hBal1 :
      ∀ a b c d, valid a b c d →
        lam a b c d * lam S.a0 S.b0 S.c0 S.d0 =
          lam c b a d * lam S.c0 S.b0 S.a0 S.d0)
    (hBal2 :
      ∀ a b c d, valid a b c d →
        lam a b S.c0 S.d0 * lam S.a0 S.b0 c d =
          lam S.c0 b a S.d0 * lam c S.b0 S.a0 d)
    (hBridge :
      ∀ a b c d, valid a b c d →
        lam c b a d * lam S.c0 S.b0 S.a0 S.d0 =
          lam S.c0 b a S.d0 * lam c S.b0 S.a0 d) :
    ∀ a b c d, valid a b c d →
      lam a b c d * lam S.a0 S.b0 S.c0 S.d0 =
        lam a b S.c0 S.d0 * lam S.a0 S.b0 c d := by
  exact h1_of_swap13_balance_triangle S lam hBal1 hBal2 hBridge

theorem concrete_h1_of_swap13_zeros_and_bridge_of_genericStrong
    {n : Nat}
    (S : Anchors n)
    (A : CameraMatrices n)
    (lam : Lambda n)
    (hGeneric : IsGenericStrong A)
    (hZeroBal1 :
      ∀ a b c d, valid a b c d →
        pluckerMap
          (fun _ : Fin 1 =>
            swap13Pattern
              (anchorQIndex a b c d)
              (anchorQIndex S.a0 S.b0 S.c0 S.d0)
              (repeatedCoreIndex S)
              (repeatedCoreIndex S))
          (scaleInput lam (QInput A)) ⟨0, by decide⟩ = 0)
    (hZeroBal2 :
      ∀ a b c d, valid a b c d →
        pluckerMap
          (fun _ : Fin 1 =>
            swap13Pattern
              (anchorQIndex a b S.c0 S.d0)
              (anchorQIndex S.a0 S.b0 c d)
              (repeatedCoreIndex S)
              (repeatedCoreIndex S))
          (scaleInput lam (QInput A)) ⟨0, by decide⟩ = 0)
    (hBridge :
      ∀ a b c d, valid a b c d →
        lam c b a d * lam S.c0 S.b0 S.a0 S.d0 =
          lam S.c0 b a S.d0 * lam c S.b0 S.a0 d) :
    ∀ a b c d, valid a b c d →
      lam a b c d * lam S.a0 S.b0 S.c0 S.d0 =
        lam a b S.c0 S.d0 * lam S.a0 S.b0 c d := by
  have hBal1 :
      ∀ a b c d, valid a b c d →
        lam a b c d * lam S.a0 S.b0 S.c0 S.d0 =
          lam c b a d * lam S.c0 S.b0 S.a0 S.d0 := by
    intro a b c d hvalid
    exact concrete_h1Bal1_of_swap13_zero_of_genericStrong S A lam a b c d hvalid hGeneric
      (hZeroBal1 a b c d hvalid)
  have hBal2 :
      ∀ a b c d, valid a b c d →
        lam a b S.c0 S.d0 * lam S.a0 S.b0 c d =
          lam S.c0 b a S.d0 * lam c S.b0 S.a0 d := by
    intro a b c d hvalid
    exact concrete_h1Bal2_of_swap13_zero_of_genericStrong S A lam a b c d hGeneric
      (hZeroBal2 a b c d hvalid)
  exact concrete_h1_of_swap13_balance_triangle S lam hBal1 hBal2 hBridge

theorem concrete_h3_of_swap34_balance_triangle
    {n : Nat}
    (S : Anchors n)
    (lam : Lambda n)
    (hBal1 :
      ∀ c d,
        lam S.a0 S.b0 c d * lam S.a0 S.b0 S.c0 S.d0 =
          lam S.a0 S.b0 d c * lam S.a0 S.b0 S.d0 S.c0)
    (hBal2 :
      ∀ c d,
        lam S.a0 S.b0 c S.d0 * lam S.a0 S.b0 S.c0 d =
          lam S.a0 S.b0 S.d0 c * lam S.a0 S.b0 d S.c0)
    (hBridge :
      ∀ c d,
        lam S.a0 S.b0 d c * lam S.a0 S.b0 S.d0 S.c0 =
          lam S.a0 S.b0 S.d0 c * lam S.a0 S.b0 d S.c0) :
    ∀ c d,
      lam S.a0 S.b0 c d * lam S.a0 S.b0 S.c0 S.d0 =
        lam S.a0 S.b0 c S.d0 * lam S.a0 S.b0 S.c0 d := by
  exact h3_of_swap34_balance_triangle S lam hBal1 hBal2 hBridge

theorem concrete_separable_of_swap_balance_triangles
    {n : Nat}
    (S : Anchors n)
    (lam : Lambda n)
    (hNZ : nonzeroOnValid lam)
    (h1Bal1 :
      ∀ a b c d, valid a b c d →
        lam a b c d * lam S.a0 S.b0 S.c0 S.d0 =
          lam c b a d * lam S.c0 S.b0 S.a0 S.d0)
    (h1Bal2 :
      ∀ a b c d, valid a b c d →
        lam a b S.c0 S.d0 * lam S.a0 S.b0 c d =
          lam S.c0 b a S.d0 * lam c S.b0 S.a0 d)
    (h1Bridge :
      ∀ a b c d, valid a b c d →
        lam c b a d * lam S.c0 S.b0 S.a0 S.d0 =
          lam S.c0 b a S.d0 * lam c S.b0 S.a0 d)
    (h2Bal1 :
      ∀ a b,
        lam a b S.c0 S.d0 * lam S.a0 S.b0 S.c0 S.d0 =
          lam b a S.c0 S.d0 * lam S.b0 S.a0 S.c0 S.d0)
    (h2Bal2 :
      ∀ a b,
        lam a S.b0 S.c0 S.d0 * lam S.a0 b S.c0 S.d0 =
          lam S.b0 a S.c0 S.d0 * lam b S.a0 S.c0 S.d0)
    (h2Bridge :
      ∀ a b,
        lam b a S.c0 S.d0 * lam S.b0 S.a0 S.c0 S.d0 =
          lam S.b0 a S.c0 S.d0 * lam b S.a0 S.c0 S.d0)
    (h3Bal1 :
      ∀ c d,
        lam S.a0 S.b0 c d * lam S.a0 S.b0 S.c0 S.d0 =
          lam S.a0 S.b0 d c * lam S.a0 S.b0 S.d0 S.c0)
    (h3Bal2 :
      ∀ c d,
        lam S.a0 S.b0 c S.d0 * lam S.a0 S.b0 S.c0 d =
          lam S.a0 S.b0 S.d0 c * lam S.a0 S.b0 d S.c0)
    (h3Bridge :
      ∀ c d,
        lam S.a0 S.b0 d c * lam S.a0 S.b0 S.d0 S.c0 =
          lam S.a0 S.b0 S.d0 c * lam S.a0 S.b0 d S.c0) :
    separable lam := by
  have h1 :
      ∀ a b c d, valid a b c d →
        lam a b c d * lam S.a0 S.b0 S.c0 S.d0 =
          lam a b S.c0 S.d0 * lam S.a0 S.b0 c d := by
    exact concrete_h1_of_swap13_balance_triangle S lam h1Bal1 h1Bal2 h1Bridge
  have h2 :
      ∀ a b,
        lam a b S.c0 S.d0 * lam S.a0 S.b0 S.c0 S.d0 =
          lam a S.b0 S.c0 S.d0 * lam S.a0 b S.c0 S.d0 := by
    exact concrete_h2_of_swap12_balance_triangle S lam h2Bal1 h2Bal2 h2Bridge
  have h3 :
      ∀ c d,
        lam S.a0 S.b0 c d * lam S.a0 S.b0 S.c0 S.d0 =
          lam S.a0 S.b0 c S.d0 * lam S.a0 S.b0 S.c0 d := by
    exact concrete_h3_of_swap34_balance_triangle S lam h3Bal1 h3Bal2 h3Bridge
  exact concrete_separable_of_three_bilinear_identities S lam hNZ h1 h2 h3

theorem concrete_separable_of_swap_zeros_and_bridges_of_genericStrong
    {n : Nat}
    (S : Anchors n)
    (A : CameraMatrices n)
    (lam : Lambda n)
    (hNZ : nonzeroOnValid lam)
    (hGeneric : IsGenericStrong A)
    (hZeroH1Bal1 :
      ∀ a b c d, valid a b c d →
        pluckerMap
          (fun _ : Fin 1 =>
            swap13Pattern
              (anchorQIndex a b c d)
              (anchorQIndex S.a0 S.b0 S.c0 S.d0)
              (repeatedCoreIndex S)
              (repeatedCoreIndex S))
          (scaleInput lam (QInput A)) ⟨0, by decide⟩ = 0)
    (hZeroH1Bal2 :
      ∀ a b c d, valid a b c d →
        pluckerMap
          (fun _ : Fin 1 =>
            swap13Pattern
              (anchorQIndex a b S.c0 S.d0)
              (anchorQIndex S.a0 S.b0 c d)
              (repeatedCoreIndex S)
              (repeatedCoreIndex S))
          (scaleInput lam (QInput A)) ⟨0, by decide⟩ = 0)
    (hBridge1 :
      ∀ a b c d, valid a b c d →
        lam c b a d * lam S.c0 S.b0 S.a0 S.d0 =
          lam S.c0 b a S.d0 * lam c S.b0 S.a0 d)
    (hZeroH2Bal1 :
      ∀ a b,
        pluckerMap
          (fun _ : Fin 1 =>
            swap12Pattern
              (anchorQIndex a b S.c0 S.d0)
              (anchorQIndex S.a0 S.b0 S.c0 S.d0)
              (repeatedCoreIndex S)
              (repeatedCoreIndex S))
          (scaleInput lam (QInput A)) ⟨0, by decide⟩ = 0)
    (hZeroH2Bal2 :
      ∀ a b,
        pluckerMap
          (fun _ : Fin 1 =>
            swap12Pattern
              (anchorQIndex a S.b0 S.c0 S.d0)
              (anchorQIndex S.a0 b S.c0 S.d0)
              (repeatedCoreIndex S)
              (repeatedCoreIndex S))
          (scaleInput lam (QInput A)) ⟨0, by decide⟩ = 0)
    (hBridge2 :
      ∀ a b,
        lam b a S.c0 S.d0 * lam S.b0 S.a0 S.c0 S.d0 =
          lam S.b0 a S.c0 S.d0 * lam b S.a0 S.c0 S.d0)
    (hZeroH3Bal1 :
      ∀ c d,
        pluckerMap
          (fun _ : Fin 1 =>
            swap34Pattern
              (anchorQIndex S.a0 S.b0 c d)
              (anchorQIndex S.a0 S.b0 S.c0 S.d0)
              (repeatedCoreIndex S)
              (repeatedCoreIndex S))
          (scaleInput lam (QInput A)) ⟨0, by decide⟩ = 0)
    (hZeroH3Bal2 :
      ∀ c d,
        pluckerMap
          (fun _ : Fin 1 =>
            swap34Pattern
              (anchorQIndex S.a0 S.b0 c S.d0)
              (anchorQIndex S.a0 S.b0 S.c0 d)
              (repeatedCoreIndex S)
              (repeatedCoreIndex S))
          (scaleInput lam (QInput A)) ⟨0, by decide⟩ = 0)
    (hBridge3 :
      ∀ c d,
        lam S.a0 S.b0 d c * lam S.a0 S.b0 S.d0 S.c0 =
          lam S.a0 S.b0 S.d0 c * lam S.a0 S.b0 d S.c0) :
    separable lam := by
  have h1 :
      ∀ a b c d, valid a b c d →
        lam a b c d * lam S.a0 S.b0 S.c0 S.d0 =
          lam a b S.c0 S.d0 * lam S.a0 S.b0 c d := by
    exact concrete_h1_of_swap13_zeros_and_bridge_of_genericStrong S A lam hGeneric
      hZeroH1Bal1 hZeroH1Bal2 hBridge1
  have h2 :
      ∀ a b,
        lam a b S.c0 S.d0 * lam S.a0 S.b0 S.c0 S.d0 =
          lam a S.b0 S.c0 S.d0 * lam S.a0 b S.c0 S.d0 := by
    exact concrete_h2_of_swap12_zeros_and_bridge_of_genericStrong S A lam hGeneric
      hZeroH2Bal1 hZeroH2Bal2 hBridge2
  have h3 :
      ∀ c d,
        lam S.a0 S.b0 c d * lam S.a0 S.b0 S.c0 S.d0 =
          lam S.a0 S.b0 c S.d0 * lam S.a0 S.b0 S.c0 d := by
    exact concrete_h3_of_swap34_zeros_and_bridge_of_genericStrong S A lam hGeneric
      hZeroH3Bal1 hZeroH3Bal2 hBridge3
  exact concrete_separable_of_three_bilinear_identities S lam hNZ h1 h2 h3

theorem concrete_bridges_of_separable
    {n : Nat}
    (S : Anchors n)
    (lam : Lambda n)
    (hSep : separable lam) :
    (∀ a b c d, valid a b c d →
      lam c b a d * lam S.c0 S.b0 S.a0 S.d0 =
        lam S.c0 b a S.d0 * lam c S.b0 S.a0 d) ∧
    (∀ a b,
      lam b a S.c0 S.d0 * lam S.b0 S.a0 S.c0 S.d0 =
        lam S.b0 a S.c0 S.d0 * lam b S.a0 S.c0 S.d0) ∧
    (∀ c d,
      lam S.a0 S.b0 d c * lam S.a0 S.b0 S.d0 S.c0 =
        lam S.a0 S.b0 S.d0 c * lam S.a0 S.b0 d S.c0) := by
  refine ⟨?_, ?_, ?_⟩
  · exact bridge1_of_separable S lam hSep
  · exact bridge2_of_separable S lam hSep
  · exact bridge3_of_separable S lam hSep

theorem concrete_bridges_of_separable_via_swaps
    {n : Nat}
    (S : Anchors n)
    (lam : Lambda n)
    (hSep : separable lam) :
    (∀ a b c d, valid a b c d →
      lam c b a d * lam S.c0 S.b0 S.a0 S.d0 =
        lam S.c0 b a S.d0 * lam c S.b0 S.a0 d) ∧
    (∀ a b,
      lam b a S.c0 S.d0 * lam S.b0 S.a0 S.c0 S.d0 =
        lam S.b0 a S.c0 S.d0 * lam b S.a0 S.c0 S.d0) ∧
    (∀ c d,
      lam S.a0 S.b0 d c * lam S.a0 S.b0 S.d0 S.c0 =
        lam S.a0 S.b0 S.d0 c * lam S.a0 S.b0 d S.c0) := by
  have h1swap : H1Condition S (swap13Lambda lam) := by
    exact h1Condition_of_separable S (swap13Lambda lam)
      (separable_swap13 lam hSep)
  have h2swap : H2Condition S (swap12Lambda lam) := by
    exact h2Condition_of_separable S (swap12Lambda lam)
      (separable_swap12 lam hSep)
  have h3swap : H3Condition S (swap34Lambda lam) := by
    exact h3Condition_of_separable S (swap34Lambda lam)
      (separable_swap34 lam hSep)
  refine ⟨?_, ?_, ?_⟩
  · exact (bridge1Condition_iff_h1_swap13 S lam).2 h1swap
  · exact (bridge2Condition_iff_h2_swap12 S lam).2 h2swap
  · exact (bridge3Condition_iff_h3_swap34 S lam).2 h3swap

theorem concrete_separable_of_swap_zeros_of_genericStrong
    {n : Nat}
    (E : BridgeExtractors n)
    (S : Anchors n)
    (A : CameraMatrices n)
    (lam : Lambda n)
    (hNZ : nonzeroOnValid lam)
    (hGeneric : IsGenericStrong A)
    (hZeroH1Bal1 :
      ∀ a b c d, valid a b c d →
        pluckerMap
          (fun _ : Fin 1 =>
            swap13Pattern
              (anchorQIndex a b c d)
              (anchorQIndex S.a0 S.b0 S.c0 S.d0)
              (repeatedCoreIndex S)
              (repeatedCoreIndex S))
          (scaleInput lam (QInput A)) ⟨0, by decide⟩ = 0)
    (hZeroH1Bal2 :
      ∀ a b c d, valid a b c d →
        pluckerMap
          (fun _ : Fin 1 =>
            swap13Pattern
              (anchorQIndex a b S.c0 S.d0)
              (anchorQIndex S.a0 S.b0 c d)
              (repeatedCoreIndex S)
              (repeatedCoreIndex S))
          (scaleInput lam (QInput A)) ⟨0, by decide⟩ = 0)
    (hZeroH2Bal1 :
      ∀ a b,
        pluckerMap
          (fun _ : Fin 1 =>
            swap12Pattern
              (anchorQIndex a b S.c0 S.d0)
              (anchorQIndex S.a0 S.b0 S.c0 S.d0)
              (repeatedCoreIndex S)
              (repeatedCoreIndex S))
          (scaleInput lam (QInput A)) ⟨0, by decide⟩ = 0)
    (hZeroH2Bal2 :
      ∀ a b,
        pluckerMap
          (fun _ : Fin 1 =>
            swap12Pattern
              (anchorQIndex a S.b0 S.c0 S.d0)
              (anchorQIndex S.a0 b S.c0 S.d0)
              (repeatedCoreIndex S)
              (repeatedCoreIndex S))
          (scaleInput lam (QInput A)) ⟨0, by decide⟩ = 0)
    (hZeroH3Bal1 :
      ∀ c d,
        pluckerMap
          (fun _ : Fin 1 =>
            swap34Pattern
              (anchorQIndex S.a0 S.b0 c d)
              (anchorQIndex S.a0 S.b0 S.c0 S.d0)
              (repeatedCoreIndex S)
              (repeatedCoreIndex S))
          (scaleInput lam (QInput A)) ⟨0, by decide⟩ = 0)
    (hZeroH3Bal2 :
      ∀ c d,
        pluckerMap
          (fun _ : Fin 1 =>
            swap34Pattern
              (anchorQIndex S.a0 S.b0 c S.d0)
              (anchorQIndex S.a0 S.b0 S.c0 d)
              (repeatedCoreIndex S)
              (repeatedCoreIndex S))
          (scaleInput lam (QInput A)) ⟨0, by decide⟩ = 0) :
    separable lam := by
  have hBridge1 :
      ∀ a b c d, valid a b c d →
        lam c b a d * lam S.c0 S.b0 S.a0 S.d0 =
          lam S.c0 b a S.d0 * lam c S.b0 S.a0 d := by
    exact E.bridge1_from_zero S A lam hGeneric hZeroH1Bal1 hZeroH1Bal2
  have hBridge2 :
      ∀ a b,
        lam b a S.c0 S.d0 * lam S.b0 S.a0 S.c0 S.d0 =
          lam S.b0 a S.c0 S.d0 * lam b S.a0 S.c0 S.d0 := by
    exact E.bridge2_from_zero S A lam hGeneric hZeroH2Bal1 hZeroH2Bal2
  have hBridge3 :
      ∀ c d,
        lam S.a0 S.b0 d c * lam S.a0 S.b0 S.d0 S.c0 =
          lam S.a0 S.b0 S.d0 c * lam S.a0 S.b0 d S.c0 := by
    exact E.bridge3_from_zero S A lam hGeneric hZeroH3Bal1 hZeroH3Bal2
  exact concrete_separable_of_swap_zeros_and_bridges_of_genericStrong S A lam hNZ hGeneric
    hZeroH1Bal1 hZeroH1Bal2 hBridge1 hZeroH2Bal1 hZeroH2Bal2 hBridge2
    hZeroH3Bal1 hZeroH3Bal2 hBridge3

theorem concrete_separable_of_swap_zeros_of_bridgeRecoverability
    {n : Nat}
    (R : BridgeRecoverability n)
    (S : Anchors n)
    (A : CameraMatrices n)
    (lam : Lambda n)
    (hNZ : nonzeroOnValid lam)
    (hGeneric : IsGenericStrong A)
    (hZeroH1Bal1 :
      ∀ a b c d, valid a b c d →
        pluckerMap
          (fun _ : Fin 1 =>
            swap13Pattern
              (anchorQIndex a b c d)
              (anchorQIndex S.a0 S.b0 S.c0 S.d0)
              (repeatedCoreIndex S)
              (repeatedCoreIndex S))
          (scaleInput lam (QInput A)) ⟨0, by decide⟩ = 0)
    (hZeroH1Bal2 :
      ∀ a b c d, valid a b c d →
        pluckerMap
          (fun _ : Fin 1 =>
            swap13Pattern
              (anchorQIndex a b S.c0 S.d0)
              (anchorQIndex S.a0 S.b0 c d)
              (repeatedCoreIndex S)
              (repeatedCoreIndex S))
          (scaleInput lam (QInput A)) ⟨0, by decide⟩ = 0)
    (hZeroH2Bal1 :
      ∀ a b,
        pluckerMap
          (fun _ : Fin 1 =>
            swap12Pattern
              (anchorQIndex a b S.c0 S.d0)
              (anchorQIndex S.a0 S.b0 S.c0 S.d0)
              (repeatedCoreIndex S)
              (repeatedCoreIndex S))
          (scaleInput lam (QInput A)) ⟨0, by decide⟩ = 0)
    (hZeroH2Bal2 :
      ∀ a b,
        pluckerMap
          (fun _ : Fin 1 =>
            swap12Pattern
              (anchorQIndex a S.b0 S.c0 S.d0)
              (anchorQIndex S.a0 b S.c0 S.d0)
              (repeatedCoreIndex S)
              (repeatedCoreIndex S))
          (scaleInput lam (QInput A)) ⟨0, by decide⟩ = 0)
    (hZeroH3Bal1 :
      ∀ c d,
        pluckerMap
          (fun _ : Fin 1 =>
            swap34Pattern
              (anchorQIndex S.a0 S.b0 c d)
              (anchorQIndex S.a0 S.b0 S.c0 S.d0)
              (repeatedCoreIndex S)
              (repeatedCoreIndex S))
          (scaleInput lam (QInput A)) ⟨0, by decide⟩ = 0)
    (hZeroH3Bal2 :
      ∀ c d,
        pluckerMap
          (fun _ : Fin 1 =>
            swap34Pattern
              (anchorQIndex S.a0 S.b0 c S.d0)
              (anchorQIndex S.a0 S.b0 S.c0 d)
              (repeatedCoreIndex S)
              (repeatedCoreIndex S))
          (scaleInput lam (QInput A)) ⟨0, by decide⟩ = 0) :
    separable lam := by
  have hBridge : BridgeConditionSet S lam := by
    exact bridgeConditionSet_of_bridgeRecoverability R S A lam hGeneric
      hZeroH1Bal1 hZeroH1Bal2 hZeroH2Bal1 hZeroH2Bal2 hZeroH3Bal1 hZeroH3Bal2
  exact concrete_separable_of_swap_zeros_and_bridges_of_genericStrong S A lam hNZ hGeneric
    hZeroH1Bal1 hZeroH1Bal2 hBridge.bridge1 hZeroH2Bal1 hZeroH2Bal2 hBridge.bridge2
    hZeroH3Bal1 hZeroH3Bal2 hBridge.bridge3

theorem separable_of_swapZeroMapWithAnchors_zero_of_genericStrong
    {n : Nat}
    (E : BridgeExtractors n)
    (S : Anchors n)
    (A : CameraMatrices n)
    (lam : Lambda n)
    (hNZ : nonzeroOnValid lam)
    (hGeneric : IsGenericStrong A)
    (hZero : ∀ idx, swapZeroMapWithAnchors S (scaleInput lam (QInput A)) idx = 0) :
    separable lam := by
  have hZeroH1Bal1 :
      ∀ a b c d, valid a b c d →
        pluckerMap
          (fun _ : Fin 1 =>
            swap13Pattern
              (anchorQIndex a b c d)
              (anchorQIndex S.a0 S.b0 S.c0 S.d0)
              (repeatedCoreIndex S)
              (repeatedCoreIndex S))
          (scaleInput lam (QInput A)) ⟨0, by decide⟩ = 0 := by
    intro a b c d _hvalid
    simpa [swapZeroMapWithAnchors] using hZero (SwapZeroIndex.h1Bal1 a b c d)
  have hZeroH1Bal2 :
      ∀ a b c d, valid a b c d →
        pluckerMap
          (fun _ : Fin 1 =>
            swap13Pattern
              (anchorQIndex a b S.c0 S.d0)
              (anchorQIndex S.a0 S.b0 c d)
              (repeatedCoreIndex S)
              (repeatedCoreIndex S))
          (scaleInput lam (QInput A)) ⟨0, by decide⟩ = 0 := by
    intro a b c d _hvalid
    simpa [swapZeroMapWithAnchors] using hZero (SwapZeroIndex.h1Bal2 a b c d)
  have hZeroH2Bal1 :
      ∀ a b,
        pluckerMap
          (fun _ : Fin 1 =>
            swap12Pattern
              (anchorQIndex a b S.c0 S.d0)
              (anchorQIndex S.a0 S.b0 S.c0 S.d0)
              (repeatedCoreIndex S)
              (repeatedCoreIndex S))
          (scaleInput lam (QInput A)) ⟨0, by decide⟩ = 0 := by
    intro a b
    simpa [swapZeroMapWithAnchors] using hZero (SwapZeroIndex.h2Bal1 a b)
  have hZeroH2Bal2 :
      ∀ a b,
        pluckerMap
          (fun _ : Fin 1 =>
            swap12Pattern
              (anchorQIndex a S.b0 S.c0 S.d0)
              (anchorQIndex S.a0 b S.c0 S.d0)
              (repeatedCoreIndex S)
              (repeatedCoreIndex S))
          (scaleInput lam (QInput A)) ⟨0, by decide⟩ = 0 := by
    intro a b
    simpa [swapZeroMapWithAnchors] using hZero (SwapZeroIndex.h2Bal2 a b)
  have hZeroH3Bal1 :
      ∀ c d,
        pluckerMap
          (fun _ : Fin 1 =>
            swap34Pattern
              (anchorQIndex S.a0 S.b0 c d)
              (anchorQIndex S.a0 S.b0 S.c0 S.d0)
              (repeatedCoreIndex S)
              (repeatedCoreIndex S))
          (scaleInput lam (QInput A)) ⟨0, by decide⟩ = 0 := by
    intro c d
    simpa [swapZeroMapWithAnchors] using hZero (SwapZeroIndex.h3Bal1 c d)
  have hZeroH3Bal2 :
      ∀ c d,
        pluckerMap
          (fun _ : Fin 1 =>
            swap34Pattern
              (anchorQIndex S.a0 S.b0 c S.d0)
              (anchorQIndex S.a0 S.b0 S.c0 d)
              (repeatedCoreIndex S)
              (repeatedCoreIndex S))
          (scaleInput lam (QInput A)) ⟨0, by decide⟩ = 0 := by
    intro c d
    simpa [swapZeroMapWithAnchors] using hZero (SwapZeroIndex.h3Bal2 c d)
  exact concrete_separable_of_swap_zeros_of_genericStrong E S A lam hNZ hGeneric
    hZeroH1Bal1 hZeroH1Bal2 hZeroH2Bal1 hZeroH2Bal2 hZeroH3Bal1 hZeroH3Bal2

theorem separable_of_swapZeroMap_zero_of_genericStrong
    {n : Nat}
    (E : BridgeExtractors n)
    (hn : 5 ≤ n)
    (A : CameraMatrices n)
    (lam : Lambda n)
    (hNZ : nonzeroOnValid lam)
    (hGeneric : IsGenericStrong A)
    (hZero : ∀ idx, swapZeroMap n hn (scaleInput lam (QInput A)) idx = 0) :
    separable lam := by
  exact separable_of_swapZeroMapWithAnchors_zero_of_genericStrong
    E (canonicalAnchors n hn) A lam hNZ hGeneric hZero

theorem separable_of_swapZeroMapFin_zero_of_genericStrong
    {n : Nat}
    (E : BridgeExtractors n)
    (hn : 5 ≤ n)
    (A : CameraMatrices n)
    (lam : Lambda n)
    (hNZ : nonzeroOnValid lam)
    (hGeneric : IsGenericStrong A)
    (hZero : ∀ t : Fin (Fintype.card (SwapZeroIndex n)),
      swapZeroMapFin n hn (scaleInput lam (QInput A)) t = 0) :
    separable lam := by
  have hZero' : ∀ idx, swapZeroMap n hn (scaleInput lam (QInput A)) idx = 0 := by
    intro idx
    simpa [swapZeroMapFin] using hZero ((Fintype.equivFin (SwapZeroIndex n)) idx)
  exact separable_of_swapZeroMap_zero_of_genericStrong E hn A lam hNZ hGeneric hZero'

theorem separable_of_swapZeroMapFin_zero_of_permutedHExtractors
    {n : Nat}
    (E : PermutedHExtractors n)
    (hn : 5 ≤ n)
    (A : CameraMatrices n)
    (lam : Lambda n)
    (hNZ : nonzeroOnValid lam)
    (hGeneric : IsGenericStrong A)
    (hZero : ∀ t : Fin (Fintype.card (SwapZeroIndex n)),
      swapZeroMapFin n hn (scaleInput lam (QInput A)) t = 0) :
    separable lam := by
  exact separable_of_swapZeroMapFin_zero_of_genericStrong
    E.toBridgeExtractors hn A lam hNZ hGeneric hZero

theorem separable_of_swapZeroMapWithAnchors_zero_of_bridgeRecoverability
    {n : Nat}
    (R : BridgeRecoverability n)
    (S : Anchors n)
    (A : CameraMatrices n)
    (lam : Lambda n)
    (hNZ : nonzeroOnValid lam)
    (hGeneric : IsGenericStrong A)
    (hZero : ∀ idx, swapZeroMapWithAnchors S (scaleInput lam (QInput A)) idx = 0) :
    separable lam := by
  have hZeroH1Bal1 :
      ∀ a b c d, valid a b c d →
        pluckerMap
          (fun _ : Fin 1 =>
            swap13Pattern
              (anchorQIndex a b c d)
              (anchorQIndex S.a0 S.b0 S.c0 S.d0)
              (repeatedCoreIndex S)
              (repeatedCoreIndex S))
          (scaleInput lam (QInput A)) ⟨0, by decide⟩ = 0 := by
    intro a b c d _hvalid
    simpa [swapZeroMapWithAnchors] using hZero (SwapZeroIndex.h1Bal1 a b c d)
  have hZeroH1Bal2 :
      ∀ a b c d, valid a b c d →
        pluckerMap
          (fun _ : Fin 1 =>
            swap13Pattern
              (anchorQIndex a b S.c0 S.d0)
              (anchorQIndex S.a0 S.b0 c d)
              (repeatedCoreIndex S)
              (repeatedCoreIndex S))
          (scaleInput lam (QInput A)) ⟨0, by decide⟩ = 0 := by
    intro a b c d _hvalid
    simpa [swapZeroMapWithAnchors] using hZero (SwapZeroIndex.h1Bal2 a b c d)
  have hZeroH2Bal1 :
      ∀ a b,
        pluckerMap
          (fun _ : Fin 1 =>
            swap12Pattern
              (anchorQIndex a b S.c0 S.d0)
              (anchorQIndex S.a0 S.b0 S.c0 S.d0)
              (repeatedCoreIndex S)
              (repeatedCoreIndex S))
          (scaleInput lam (QInput A)) ⟨0, by decide⟩ = 0 := by
    intro a b
    simpa [swapZeroMapWithAnchors] using hZero (SwapZeroIndex.h2Bal1 a b)
  have hZeroH2Bal2 :
      ∀ a b,
        pluckerMap
          (fun _ : Fin 1 =>
            swap12Pattern
              (anchorQIndex a S.b0 S.c0 S.d0)
              (anchorQIndex S.a0 b S.c0 S.d0)
              (repeatedCoreIndex S)
              (repeatedCoreIndex S))
          (scaleInput lam (QInput A)) ⟨0, by decide⟩ = 0 := by
    intro a b
    simpa [swapZeroMapWithAnchors] using hZero (SwapZeroIndex.h2Bal2 a b)
  have hZeroH3Bal1 :
      ∀ c d,
        pluckerMap
          (fun _ : Fin 1 =>
            swap34Pattern
              (anchorQIndex S.a0 S.b0 c d)
              (anchorQIndex S.a0 S.b0 S.c0 S.d0)
              (repeatedCoreIndex S)
              (repeatedCoreIndex S))
          (scaleInput lam (QInput A)) ⟨0, by decide⟩ = 0 := by
    intro c d
    simpa [swapZeroMapWithAnchors] using hZero (SwapZeroIndex.h3Bal1 c d)
  have hZeroH3Bal2 :
      ∀ c d,
        pluckerMap
          (fun _ : Fin 1 =>
            swap34Pattern
              (anchorQIndex S.a0 S.b0 c S.d0)
              (anchorQIndex S.a0 S.b0 S.c0 d)
              (repeatedCoreIndex S)
              (repeatedCoreIndex S))
          (scaleInput lam (QInput A)) ⟨0, by decide⟩ = 0 := by
    intro c d
    simpa [swapZeroMapWithAnchors] using hZero (SwapZeroIndex.h3Bal2 c d)
  exact concrete_separable_of_swap_zeros_of_bridgeRecoverability R S A lam hNZ hGeneric
    hZeroH1Bal1 hZeroH1Bal2 hZeroH2Bal1 hZeroH2Bal2 hZeroH3Bal1 hZeroH3Bal2

theorem separable_of_swapZeroMap_zero_of_bridgeRecoverability
    {n : Nat}
    (R : BridgeRecoverability n)
    (hn : 5 ≤ n)
    (A : CameraMatrices n)
    (lam : Lambda n)
    (hNZ : nonzeroOnValid lam)
    (hGeneric : IsGenericStrong A)
    (hZero : ∀ idx, swapZeroMap n hn (scaleInput lam (QInput A)) idx = 0) :
    separable lam := by
  exact separable_of_swapZeroMapWithAnchors_zero_of_bridgeRecoverability
    R (canonicalAnchors n hn) A lam hNZ hGeneric hZero

theorem separable_of_swapZeroMapFin_zero_of_bridgeRecoverability
    {n : Nat}
    (R : BridgeRecoverability n)
    (hn : 5 ≤ n)
    (A : CameraMatrices n)
    (lam : Lambda n)
    (hNZ : nonzeroOnValid lam)
    (hGeneric : IsGenericStrong A)
    (hZero : ∀ t : Fin (Fintype.card (SwapZeroIndex n)),
      swapZeroMapFin n hn (scaleInput lam (QInput A)) t = 0) :
    separable lam := by
  have hZero' : ∀ idx, swapZeroMap n hn (scaleInput lam (QInput A)) idx = 0 := by
    intro idx
    simpa [swapZeroMapFin] using hZero ((Fintype.equivFin (SwapZeroIndex n)) idx)
  exact separable_of_swapZeroMap_zero_of_bridgeRecoverability
    R hn A lam hNZ hGeneric hZero'

theorem exists_reverse_solution_of_bridgeRecoverability
    {n : Nat}
    (hn : 5 ≤ n)
    (R : BridgeRecoverability n) :
    ∃ m : Nat, ∃ F : InputVector n → (Fin m → ℝ),
      (pluckerCoordinateDegree = 2) ∧
      (∀ A : CameraMatrices n, ∀ lam : Lambda n, nonzeroOnValid lam →
        IsGenericStrong A →
          ((∀ t, F (scaleInput lam (QInput A)) t = 0) → separable lam)) := by
  refine ⟨Fintype.card (SwapZeroIndex n), swapZeroMapFin n hn, pluckerCoordinateDegree_eq, ?_⟩
  intro A lam hNZ hGeneric hZero
  exact separable_of_swapZeroMapFin_zero_of_bridgeRecoverability
    R hn A lam hNZ hGeneric hZero

theorem exists_reverse_solution_of_bridgeExtractors
    {n : Nat}
    (hn : 5 ≤ n)
    (E : BridgeExtractors n) :
    ∃ m : Nat, ∃ F : InputVector n → (Fin m → ℝ),
      (pluckerCoordinateDegree = 2) ∧
      (∀ A : CameraMatrices n, ∀ lam : Lambda n, nonzeroOnValid lam →
        IsGenericStrong A →
          ((∀ t, F (scaleInput lam (QInput A)) t = 0) → separable lam)) := by
  refine ⟨Fintype.card (SwapZeroIndex n), swapZeroMapFin n hn, pluckerCoordinateDegree_eq, ?_⟩
  intro A lam hNZ hGeneric hZero
  have hZero' : ∀ idx, swapZeroMap n hn (scaleInput lam (QInput A)) idx = 0 := by
    intro idx
    simpa [swapZeroMapFin] using hZero ((Fintype.equivFin (SwapZeroIndex n)) idx)
  exact separable_of_swapZeroMap_zero_of_genericStrong E hn A lam hNZ hGeneric hZero'

theorem exists_reverse_solution_of_permutedHExtractors
    {n : Nat}
    (hn : 5 ≤ n)
    (E : PermutedHExtractors n) :
    ∃ m : Nat, ∃ F : InputVector n → (Fin m → ℝ),
      (pluckerCoordinateDegree = 2) ∧
      (∀ A : CameraMatrices n, ∀ lam : Lambda n, nonzeroOnValid lam →
        IsGenericStrong A →
          ((∀ t, F (scaleInput lam (QInput A)) t = 0) → separable lam)) := by
  exact exists_reverse_solution_of_bridgeExtractors hn E.toBridgeExtractors

theorem concrete_separable_of_family_zero_via_three_bilinear
    {n m : Nat}
    (S : Anchors n)
    (A : CameraMatrices n)
    (lam : Lambda n)
    (Phi : InputVector n → (Fin m → ℝ))
    (hNZ : nonzeroOnValid lam)
    (hZero : ∀ t, Phi (scaleInput lam (QInput A)) t = 0)
    (h1_from_zero :
      (∀ t, Phi (scaleInput lam (QInput A)) t = 0) →
        ∀ a b c d, valid a b c d →
          lam a b c d * lam S.a0 S.b0 S.c0 S.d0 =
            lam a b S.c0 S.d0 * lam S.a0 S.b0 c d)
    (h2_from_zero :
      (∀ t, Phi (scaleInput lam (QInput A)) t = 0) →
        ∀ a b,
          lam a b S.c0 S.d0 * lam S.a0 S.b0 S.c0 S.d0 =
            lam a S.b0 S.c0 S.d0 * lam S.a0 b S.c0 S.d0)
    (h3_from_zero :
      (∀ t, Phi (scaleInput lam (QInput A)) t = 0) →
        ∀ c d,
          lam S.a0 S.b0 c d * lam S.a0 S.b0 S.c0 S.d0 =
            lam S.a0 S.b0 c S.d0 * lam S.a0 S.b0 S.c0 d) :
    separable lam := by
  exact concrete_separable_of_three_bilinear_identities S lam hNZ
    (h1_from_zero hZero) (h2_from_zero hZero) (h3_from_zero hZero)

theorem concrete_iff_of_pluckerMap_via_three_bilinear
    {n m : Nat}
    (S : Anchors n)
    (A : CameraMatrices n)
    (patterns : Fin m → PluckerPattern n)
    (lam : Lambda n)
    (hNZ : nonzeroOnValid lam)
    (hZero_of_sep : separable lam → ∀ t, pluckerMap patterns (scaleInput lam (QInput A)) t = 0)
    (h1_from_zero :
      (∀ t, pluckerMap patterns (scaleInput lam (QInput A)) t = 0) →
        ∀ a b c d, valid a b c d →
          lam a b c d * lam S.a0 S.b0 S.c0 S.d0 =
            lam a b S.c0 S.d0 * lam S.a0 S.b0 c d)
    (h2_from_zero :
      (∀ t, pluckerMap patterns (scaleInput lam (QInput A)) t = 0) →
        ∀ a b,
          lam a b S.c0 S.d0 * lam S.a0 S.b0 S.c0 S.d0 =
            lam a S.b0 S.c0 S.d0 * lam S.a0 b S.c0 S.d0)
    (h3_from_zero :
      (∀ t, pluckerMap patterns (scaleInput lam (QInput A)) t = 0) →
        ∀ c d,
          lam S.a0 S.b0 c d * lam S.a0 S.b0 S.c0 S.d0 =
            lam S.a0 S.b0 c S.d0 * lam S.a0 S.b0 S.c0 d) :
    (∀ t, pluckerMap patterns (scaleInput lam (QInput A)) t = 0) ↔ separable lam := by
  constructor
  · intro hZero
    exact concrete_separable_of_family_zero_via_three_bilinear S A lam (pluckerMap patterns) hNZ hZero
      h1_from_zero h2_from_zero h3_from_zero
  · intro hSep
    exact hZero_of_sep hSep

theorem concrete_iff_of_family_witness
    {n m : Nat}
    (W : PluckerFamilyWitness n m)
    (S : Anchors n)
    (A : CameraMatrices n)
    (lam : Lambda n)
    (hLamNZ : nonzeroOnValid lam) :
    (∀ t, familyMap W (scaleInput lam (QInput A)) t = 0) ↔ separable lam := by
  exact scaled_q_iff_separable_of_witness W S A lam hLamNZ

theorem concrete_iff_of_bilinear_witness
    {n m : Nat}
    (W : BilinearFamilyWitness n m)
    (S : Anchors n)
    (A : CameraMatrices n)
    (lam : Lambda n)
    (hLamNZ : nonzeroOnValid lam) :
    (∀ t, W.map (scaleInput lam (QInput A)) t = 0) ↔ separable lam := by
  exact family_zero_iff_separable_of_bilinearWitness W S A lam hLamNZ

theorem exists_question_solution_of_familyWitness
    {n : Nat}
    (_hn : 5 ≤ n)
    (hW : Sigma fun m : Nat => PluckerFamilyWitness n m) :
    ∃ m : Nat, ∃ F : InputVector n → (Fin m → ℝ),
      (pluckerCoordinateDegree = 2) ∧
      (∀ A : CameraMatrices n, ∀ lam : Lambda n, nonzeroOnValid lam →
        ((∀ t, F (scaleInput lam (QInput A)) t = 0) ↔ separable lam)) := by
  rcases hW with ⟨m, W⟩
  refine ⟨m, familyMap W, pluckerCoordinateDegree_eq, ?_⟩
  intro A lam hLamNZ
  simpa [familyMap] using scaled_q_iff_separable_of_witness W (canonicalAnchors n (by omega)) A lam hLamNZ

theorem exists_question_solution_of_bilinearWitness
    {n : Nat}
    (_hn : 5 ≤ n)
    (hW : Sigma fun m : Nat => BilinearFamilyWitness n m) :
    ∃ m : Nat, ∃ F : InputVector n → (Fin m → ℝ),
      (pluckerCoordinateDegree = 2) ∧
      (∀ A : CameraMatrices n, ∀ lam : Lambda n, nonzeroOnValid lam →
        ((∀ t, F (scaleInput lam (QInput A)) t = 0) ↔ separable lam)) := by
  rcases hW with ⟨m, W⟩
  refine ⟨m, W.map, pluckerCoordinateDegree_eq, ?_⟩
  intro A lam hLamNZ
  exact concrete_iff_of_bilinear_witness W (canonicalAnchors n (by omega)) A lam hLamNZ

end Question9
