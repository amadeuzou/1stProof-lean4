import Macdonald.Bridge.FstarSpecialized
import Macdonald.Bridge.Evaluation

namespace Macdonald
namespace Bridge

open Question3
open Nonsymmetric

noncomputable section

section Workflow

variable {m n : ℕ} {R : Type*} [CommRing R] [IsDomain R]

def FstarExchangeGoal
    (weight : Conventions.Composition n → Nonsymmetric.RatPoly n R)
    (spec : LocalRatioSpecialization n R) : Prop :=
  Nonsymmetric.ExchangeRelationQOne (n := n) (R := R) weight spec.tR

def FstarDenGoal
    (spec : LocalRatioSpecialization n R) : Prop :=
  Question3.DenomNonzero spec.x spec.t

def FstarPosGoal
    (spec : LocalRatioSpecialization n R) : Prop :=
  ∀ a : Question3.AdjIndex n, 0 < Question3.ratePlus spec.x spec.t a

def buildFstarSpecializedData
    (weight : Conventions.Composition n → Nonsymmetric.RatPoly n R)
    (spec : LocalRatioSpecialization n R)
    (Pstar : ℝ)
    (hm : 2 ≤ m) (hn : 2 ≤ n)
    (hEx : FstarExchangeGoal (n := n) (R := R) weight spec)
    (hDen : FstarDenGoal (n := n) spec)
    (hPos : FstarPosGoal (n := n) spec) :
    FstarSpecializedData m n R where
  weight := weight
  spec := spec
  Pstar := Pstar
  hm := hm
  hn := hn
  hExchange := hEx
  hDen := hDen
  hPos := hPos

theorem question3_full_of_workflow
    (weight : Conventions.Composition n → Nonsymmetric.RatPoly n R)
    (spec : LocalRatioSpecialization n R)
    (Pstar : ℝ)
    (hm : 2 ≤ m) (hn : 2 ≤ n)
    (hEx : FstarExchangeGoal (n := n) (R := R) weight spec)
    (hDen : FstarDenGoal (n := n) spec)
    (hPos : FstarPosGoal (n := n) spec) :
    (∀ y : BoundedWord m n,
      (∑ w,
        (buildFstarSpecializedData (m := m) (n := n) (R := R)
          weight spec Pstar hm hn hEx hDen hPos).pi w
            * Question3.transitionRate spec.x spec.t w y)
        =
      (buildFstarSpecializedData (m := m) (n := n) (R := R)
        weight spec Pstar hm hn hEx hDen hPos).pi y
          * (∑ z, Question3.transitionRate spec.x spec.t y z))
    ∧
    (∃ w : BoundedWord m n, ∃ a : Question3.AdjIndex n,
      w ≠ Question3.swapAt w a ∧ 0 < Question3.localRate spec.x spec.t w a) := by
  exact
    (buildFstarSpecializedData (m := m) (n := n) (R := R)
      weight spec Pstar hm hn hEx hDen hPos).question3_full

theorem stationary_of_workflow
    (weight : Conventions.Composition n → Nonsymmetric.RatPoly n R)
    (spec : LocalRatioSpecialization n R)
    (Pstar : ℝ)
    (hm : 2 ≤ m) (hn : 2 ≤ n)
    (hEx : FstarExchangeGoal (n := n) (R := R) weight spec)
    (hDen : FstarDenGoal (n := n) spec)
    (hPos : FstarPosGoal (n := n) spec) :
    ∀ y : BoundedWord m n,
      (∑ w,
        (buildFstarSpecializedData (m := m) (n := n) (R := R)
          weight spec Pstar hm hn hEx hDen hPos).pi w
            * Question3.transitionRate spec.x spec.t w y)
        =
      (buildFstarSpecializedData (m := m) (n := n) (R := R)
        weight spec Pstar hm hn hEx hDen hPos).pi y
          * (∑ z, Question3.transitionRate spec.x spec.t y z) := by
  intro y
  exact (question3_full_of_workflow
    (m := m) (n := n) (R := R)
    weight spec Pstar hm hn hEx hDen hPos).1 y

theorem nontrivial_of_workflow
    (weight : Conventions.Composition n → Nonsymmetric.RatPoly n R)
    (spec : LocalRatioSpecialization n R)
    (Pstar : ℝ)
    (hm : 2 ≤ m) (hn : 2 ≤ n)
    (hEx : FstarExchangeGoal (n := n) (R := R) weight spec)
    (hDen : FstarDenGoal (n := n) spec)
    (hPos : FstarPosGoal (n := n) spec) :
    ∃ w : BoundedWord m n, ∃ a : Question3.AdjIndex n,
      w ≠ Question3.swapAt w a ∧ 0 < Question3.localRate spec.x spec.t w a := by
  exact (question3_full_of_workflow
    (m := m) (n := n) (R := R)
    weight spec Pstar hm hn hEx hDen hPos).2

theorem question3_full_of_workflow_t_one_desc
    (weight : Conventions.Composition n → Nonsymmetric.RatPoly n R)
    (spec : LocalRatioSpecialization n R)
    (Pstar : ℝ)
    (hm : 2 ≤ m) (hn : 2 ≤ n)
    (hEx : FstarExchangeGoal (n := n) (R := R) weight spec)
    (ht : spec.t = 1)
    (hDesc : StrictAdjacentDesc spec.x) :
    ∃ hDen : FstarDenGoal (n := n) spec,
      ∃ hPos : FstarPosGoal (n := n) spec,
        (∀ y : BoundedWord m n,
          (∑ w,
            (buildFstarSpecializedData (m := m) (n := n) (R := R)
              weight spec Pstar hm hn hEx hDen hPos).pi w
                * Question3.transitionRate spec.x spec.t w y)
            =
          (buildFstarSpecializedData (m := m) (n := n) (R := R)
            weight spec Pstar hm hn hEx hDen hPos).pi y
              * (∑ z, Question3.transitionRate spec.x spec.t y z))
        ∧
        (∃ w : BoundedWord m n, ∃ a : Question3.AdjIndex n,
          w ≠ Question3.swapAt w a ∧ 0 < Question3.localRate spec.x spec.t w a) := by
  have hDen : FstarDenGoal (n := n) spec := by
    simpa [FstarDenGoal, ht] using
      (denomNonzero_one_of_strictAdjacentDesc (x := spec.x) hDesc)
  have hPos : FstarPosGoal (n := n) spec := by
    simpa [FstarPosGoal, ht] using
      (ratePlus_pos_one_of_strictAdjacentDesc (x := spec.x) hDesc)
  exact ⟨hDen, hPos, question3_full_of_workflow
    (m := m) (n := n) (R := R)
    weight spec Pstar hm hn hEx hDen hPos⟩

end Workflow

end

end Bridge
end Macdonald
