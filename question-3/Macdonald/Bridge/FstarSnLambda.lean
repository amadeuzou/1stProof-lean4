import Macdonald.Bridge.FstarSpecialized
import Macdonald.Bridge.SnLambda

namespace Macdonald
namespace Bridge

open Question3
open Nonsymmetric
open scoped BigOperators

noncomputable section

section FstarOnSnLambda

variable {m n : ℕ} {R : Type*} [CommRing R] [IsDomain R]

def FstarSpecializedData.piOnSn
    (data : FstarSpecializedData m n R)
    (lam : BoundedWord m n) :
    SnLambdaState lam → ℝ := fun u =>
  data.pi u.1

theorem FstarSpecializedData.weightExchangeOnWords
    (data : FstarSpecializedData m n R) :
    Question3.WeightExchange
      (Species := Fin m)
      data.evalWeight data.spec.x data.spec.t := by
  exact weightExchange_bounded_of_qOneSpecialization
    (ev := data.spec.ev)
    (weight := data.weight)
    (tR := data.spec.tR)
    (x := data.spec.x)
    (t := data.spec.t)
    data.hExchange
    (by
      intro i h
      exact data.spec.map_exchangeRatio i h)

theorem FstarSpecializedData.stationary_on_SnLambda
    (data : FstarSpecializedData m n R)
    (lam : BoundedWord m n) :
    ∀ y : SnLambdaState lam,
      (∑ w, data.piOnSn lam w * transitionRateSn data.spec.x data.spec.t lam w y)
        =
      data.piOnSn lam y * (∑ z, transitionRateSn data.spec.x data.spec.t lam y z) := by
  exact Macdonald.Bridge.stationary_on_SnLambda
    (asepWeight := data.evalWeight) (lam := lam)
    (x := data.spec.x) (t := data.spec.t) (Pstar := data.Pstar)
    data.weightExchangeOnWords data.hDen

theorem FstarSpecializedData.nontrivial_on_SnLambda
    (data : FstarSpecializedData m n R)
    (lam : BoundedWord m n)
    (hInv : ∃ a : AdjIndex n, lam (leftIndex a) > lam (rightIndex a)) :
    ∃ w : SnLambdaState lam, ∃ a : AdjIndex n,
      w.1 ≠ swapAt w.1 a ∧ 0 < localRate data.spec.x data.spec.t w.1 a := by
  exact Macdonald.Bridge.nontrivial_on_SnLambda
    (lam := lam) (x := data.spec.x) (t := data.spec.t)
    data.hPos hInv

theorem FstarSpecializedData.question3_full_on_SnLambda
    (data : FstarSpecializedData m n R)
    (lam : BoundedWord m n)
    (hInv : ∃ a : AdjIndex n, lam (leftIndex a) > lam (rightIndex a)) :
    (∀ y : SnLambdaState lam,
      (∑ w, data.piOnSn lam w * transitionRateSn data.spec.x data.spec.t lam w y)
        =
      data.piOnSn lam y * (∑ z, transitionRateSn data.spec.x data.spec.t lam y z))
    ∧
    (∃ w : SnLambdaState lam, ∃ a : AdjIndex n,
      w.1 ≠ swapAt w.1 a ∧ 0 < localRate data.spec.x data.spec.t w.1 a) := by
  constructor
  · exact data.stationary_on_SnLambda lam
  · exact data.nontrivial_on_SnLambda lam hInv

structure FstarSnLambdaData (m n : ℕ) (R : Type*) [CommRing R] [IsDomain R] where
  core : FstarSpecializedData m n R
  lam : BoundedWord m n
  hInv : ∃ a : AdjIndex n, lam (leftIndex a) > lam (rightIndex a)

def FstarSnLambdaData.pi
    (data : FstarSnLambdaData m n R) : SnLambdaState data.lam → ℝ :=
  data.core.piOnSn data.lam

theorem FstarSnLambdaData.question3_full
    (data : FstarSnLambdaData m n R) :
    (∀ y : SnLambdaState data.lam,
      (∑ w, data.pi w *
        transitionRateSn data.core.spec.x data.core.spec.t data.lam w y)
        =
      data.pi y *
        (∑ z, transitionRateSn data.core.spec.x data.core.spec.t data.lam y z))
    ∧
    (∃ w : SnLambdaState data.lam, ∃ a : AdjIndex n,
      w.1 ≠ swapAt w.1 a ∧
      0 < localRate data.core.spec.x data.core.spec.t w.1 a) := by
  simpa [FstarSnLambdaData.pi] using
    data.core.question3_full_on_SnLambda data.lam data.hInv

theorem FstarSnLambdaData.stationary
    (data : FstarSnLambdaData m n R) :
    ∀ y : SnLambdaState data.lam,
      (∑ w, data.pi w *
        transitionRateSn data.core.spec.x data.core.spec.t data.lam w y)
        =
      data.pi y *
        (∑ z, transitionRateSn data.core.spec.x data.core.spec.t data.lam y z) :=
  (data.question3_full).1

theorem FstarSnLambdaData.nontrivial
    (data : FstarSnLambdaData m n R) :
    ∃ w : SnLambdaState data.lam, ∃ a : AdjIndex n,
      w.1 ≠ swapAt w.1 a ∧ 0 < localRate data.core.spec.x data.core.spec.t w.1 a :=
  (data.question3_full).2

theorem FstarSpecializedData.question3_full_on_SnLambda_of_restricted
    (data : FstarSpecializedData m n R)
    (lam : BoundedWord m n)
    (hn : 2 ≤ n)
    (hRes : IsRestrictedWord lam) :
    (∀ y : SnLambdaState lam,
      (∑ w, data.piOnSn lam w * transitionRateSn data.spec.x data.spec.t lam w y)
        =
      data.piOnSn lam y * (∑ z, transitionRateSn data.spec.x data.spec.t lam y z))
    ∧
    (∃ w : SnLambdaState lam, ∃ a : AdjIndex n,
      w.1 ≠ swapAt w.1 a ∧ 0 < localRate data.spec.x data.spec.t w.1 a) := by
  exact data.question3_full_on_SnLambda
    lam
    (exists_local_inversion_of_strictAdjacent
      (lam := lam) (hn := hn) hRes.1)

def twoSiteCanonicalCore
    (spec : LocalRatioSpecialization 2 R)
    (Pstar : ℝ)
    (hm : 2 ≤ m)
    (hDen : Question3.DenomNonzero spec.x spec.t)
    (hPos : ∀ a : AdjIndex 2, 0 < Question3.ratePlus spec.x spec.t a) :
    FstarSpecializedData m 2 R where
  weight := Nonsymmetric.twoSiteCanonicalWeight (R := R) spec.tR
  spec := spec
  Pstar := Pstar
  hm := hm
  hn := by decide
  hExchange := Nonsymmetric.exchangeRelationQOne_twoSiteCanonical (R := R) spec.tR
  hDen := hDen
  hPos := hPos

theorem question3_full_twoSiteCanonical_on_SnLambda
    (spec : LocalRatioSpecialization 2 R)
    (Pstar : ℝ)
    (hm : 2 ≤ m)
    (lam : BoundedWord m 2)
    (hInv : ∃ a : AdjIndex 2, lam (leftIndex a) > lam (rightIndex a))
    (hDen : Question3.DenomNonzero spec.x spec.t)
    (hPos : ∀ a : AdjIndex 2, 0 < Question3.ratePlus spec.x spec.t a) :
    (∀ y : SnLambdaState lam,
      (∑ w,
        (twoSiteCanonicalCore (m := m) (R := R) spec Pstar hm hDen hPos).piOnSn lam w
          * transitionRateSn spec.x spec.t lam w y)
        =
      (twoSiteCanonicalCore (m := m) (R := R) spec Pstar hm hDen hPos).piOnSn lam y
        * (∑ z, transitionRateSn spec.x spec.t lam y z))
    ∧
    (∃ w : SnLambdaState lam, ∃ a : AdjIndex 2,
      w.1 ≠ swapAt w.1 a ∧ 0 < localRate spec.x spec.t w.1 a) := by
  let data : FstarSpecializedData m 2 R :=
    twoSiteCanonicalCore (m := m) (R := R) spec Pstar hm hDen hPos
  exact data.question3_full_on_SnLambda lam hInv

theorem question3_full_twoSiteCanonical_on_SnLambda_of_restricted
    (spec : LocalRatioSpecialization 2 R)
    (Pstar : ℝ)
    (hm : 2 ≤ m)
    (lam : BoundedWord m 2)
    (hRes : IsRestrictedWord lam)
    (hDen : Question3.DenomNonzero spec.x spec.t)
    (hPos : ∀ a : AdjIndex 2, 0 < Question3.ratePlus spec.x spec.t a) :
    (∀ y : SnLambdaState lam,
      (∑ w,
        (twoSiteCanonicalCore (m := m) (R := R) spec Pstar hm hDen hPos).piOnSn lam w
          * transitionRateSn spec.x spec.t lam w y)
        =
      (twoSiteCanonicalCore (m := m) (R := R) spec Pstar hm hDen hPos).piOnSn lam y
        * (∑ z, transitionRateSn spec.x spec.t lam y z))
    ∧
    (∃ w : SnLambdaState lam, ∃ a : AdjIndex 2,
      w.1 ≠ swapAt w.1 a ∧ 0 < localRate spec.x spec.t w.1 a) := by
  have hInv : ∃ a : AdjIndex 2, lam (leftIndex a) > lam (rightIndex a) := by
    exact exists_local_inversion_of_strictAdjacent
      (lam := lam) (hn := by decide) hRes.1
  exact question3_full_twoSiteCanonical_on_SnLambda
    (m := m) (R := R)
    spec Pstar hm lam hInv hDen hPos

end FstarOnSnLambda

end

end Bridge
end Macdonald
