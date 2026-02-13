import Macdonald.Bridge.Specialization

namespace Macdonald
namespace Bridge

open Question3
open Nonsymmetric

noncomputable section

section FstarSpecializedTemplate

variable {m n : ℕ} {R : Type*} [CommRing R] [IsDomain R]

/--
Preferred high-level template for the current formalization stage.

Compared with `FstarQOneData` (ratEval-based), this version is specialization-agnostic:
you provide a `LocalRatioSpecialization` directly, so no global localization-evaluation
nonvanishing condition is required in the input.
-/
structure FstarSpecializedData (m n : ℕ) (R : Type*) [CommRing R] [IsDomain R] where
  weight : Conventions.Composition n → Nonsymmetric.RatPoly n R
  spec : LocalRatioSpecialization n R
  Pstar : ℝ
  hm : 2 ≤ m
  hn : 2 ≤ n
  hExchange : Nonsymmetric.ExchangeRelationQOne (n := n) (R := R) weight spec.tR
  hDen : Question3.DenomNonzero spec.x spec.t
  hPos : ∀ a : Question3.AdjIndex n, 0 < Question3.ratePlus spec.x spec.t a

def FstarSpecializedData.evalWeight
    (data : FstarSpecializedData m n R) :
    BoundedWord m n → ℝ := fun u =>
  specializeCompositionWeight data.spec.ev data.weight (toComposition u)

def FstarSpecializedData.pi
    (data : FstarSpecializedData m n R) :
    BoundedWord m n → ℝ := fun u =>
  Question3.PiFromFstarPstar
    (Question3.FstarAtQ1ByDefinition data.evalWeight)
    data.Pstar u

theorem FstarSpecializedData.question3_full
    (data : FstarSpecializedData m n R) :
    (∀ y : BoundedWord m n,
      (∑ w, data.pi w * Question3.transitionRate data.spec.x data.spec.t w y)
        =
      data.pi y * (∑ z, Question3.transitionRate data.spec.x data.spec.t y z))
    ∧
    (∃ w : BoundedWord m n, ∃ a : Question3.AdjIndex n,
      w ≠ Question3.swapAt w a ∧ 0 < Question3.localRate data.spec.x data.spec.t w a) := by
  simpa [FstarSpecializedData.pi, FstarSpecializedData.evalWeight] using
    question3_full_on_bounded_words_of_specialization_auto
      (weight := data.weight) (spec := data.spec) (Pstar := data.Pstar)
      (hm := data.hm) (hn := data.hn)
      (hEx := data.hExchange) (hden := data.hDen) (hpos := data.hPos)

theorem FstarSpecializedData.stationary
    (data : FstarSpecializedData m n R) :
    ∀ y : BoundedWord m n,
      (∑ w, data.pi w * Question3.transitionRate data.spec.x data.spec.t w y)
        =
      data.pi y * (∑ z, Question3.transitionRate data.spec.x data.spec.t y z) :=
  (data.question3_full).1

theorem FstarSpecializedData.nontrivial
    (data : FstarSpecializedData m n R) :
    ∃ w : BoundedWord m n, ∃ a : Question3.AdjIndex n,
      w ≠ Question3.swapAt w a ∧ 0 < Question3.localRate data.spec.x data.spec.t w a :=
  (data.question3_full).2

end FstarSpecializedTemplate

end

end Bridge
end Macdonald
