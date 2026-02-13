import Macdonald.Bridge.FstarWorkflow

namespace Macdonald
namespace Bridge

open Question3
open Nonsymmetric

noncomputable section

section TwoSiteCanonical

variable {m : ℕ} {R : Type*} [CommRing R] [IsDomain R]

def twoSiteCanonicalSpecializedData
    (spec : LocalRatioSpecialization 2 R)
    (Pstar : ℝ)
    (hm : 2 ≤ m)
    (hDen : Question3.DenomNonzero spec.x spec.t)
    (hPos : ∀ a : Question3.AdjIndex 2, 0 < Question3.ratePlus spec.x spec.t a) :
    FstarSpecializedData m 2 R :=
  buildFstarSpecializedData
    (m := m) (n := 2) (R := R)
    (Nonsymmetric.twoSiteCanonicalWeight (R := R) spec.tR)
    spec Pstar hm (by decide)
    (Nonsymmetric.exchangeRelationQOne_twoSiteCanonical (R := R) spec.tR)
    hDen hPos

theorem question3_full_twoSite_canonical_auto
    (spec : LocalRatioSpecialization 2 R)
    (Pstar : ℝ)
    (hm : 2 ≤ m)
    (hDen : Question3.DenomNonzero spec.x spec.t)
    (hPos : ∀ a : Question3.AdjIndex 2, 0 < Question3.ratePlus spec.x spec.t a) :
    (∀ y : BoundedWord m 2,
      (∑ w,
        (twoSiteCanonicalSpecializedData (m := m) (R := R)
          spec Pstar hm hDen hPos).pi w
          * Question3.transitionRate spec.x spec.t w y)
        =
      (twoSiteCanonicalSpecializedData (m := m) (R := R)
        spec Pstar hm hDen hPos).pi y
          * (∑ z, Question3.transitionRate spec.x spec.t y z))
    ∧
    (∃ w : BoundedWord m 2, ∃ a : Question3.AdjIndex 2,
      w ≠ Question3.swapAt w a ∧ 0 < Question3.localRate spec.x spec.t w a) := by
  exact (twoSiteCanonicalSpecializedData
    (m := m) (R := R)
    spec Pstar hm hDen hPos).question3_full

theorem stationary_twoSite_canonical_auto
    (spec : LocalRatioSpecialization 2 R)
    (Pstar : ℝ)
    (hm : 2 ≤ m)
    (hDen : Question3.DenomNonzero spec.x spec.t)
    (hPos : ∀ a : Question3.AdjIndex 2, 0 < Question3.ratePlus spec.x spec.t a) :
    ∀ y : BoundedWord m 2,
      (∑ w,
        (twoSiteCanonicalSpecializedData (m := m) (R := R)
          spec Pstar hm hDen hPos).pi w
          * Question3.transitionRate spec.x spec.t w y)
        =
      (twoSiteCanonicalSpecializedData (m := m) (R := R)
        spec Pstar hm hDen hPos).pi y
          * (∑ z, Question3.transitionRate spec.x spec.t y z) := by
  intro y
  exact (question3_full_twoSite_canonical_auto
    (m := m) (R := R)
    spec Pstar hm hDen hPos).1 y

theorem nontrivial_twoSite_canonical_auto
    (spec : LocalRatioSpecialization 2 R)
    (Pstar : ℝ)
    (hm : 2 ≤ m)
    (hDen : Question3.DenomNonzero spec.x spec.t)
    (hPos : ∀ a : Question3.AdjIndex 2, 0 < Question3.ratePlus spec.x spec.t a) :
    ∃ w : BoundedWord m 2, ∃ a : Question3.AdjIndex 2,
      w ≠ Question3.swapAt w a ∧ 0 < Question3.localRate spec.x spec.t w a := by
  exact (question3_full_twoSite_canonical_auto
    (m := m) (R := R)
    spec Pstar hm hDen hPos).2

end TwoSiteCanonical

end

end Bridge
end Macdonald
