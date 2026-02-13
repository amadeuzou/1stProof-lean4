import Macdonald.Bridge.Evaluation

namespace Macdonald
namespace Bridge

open Question3
open Nonsymmetric

noncomputable section

section ProgramInput

variable {m n : ℕ}

/--
Unified input package for running the full `Question3` bridge at `q = 1`.

This gathers algebraic data (`weight`, exchange relation), analytic data (evaluation
point and non-vanishing conditions), and Markov-rate side conditions.
-/
structure QOneBridgeInput (m n : ℕ) where
  weight : Conventions.Composition n → RatR n
  x : Fin n → ℝ
  t : ℝ
  Pstar : ℝ
  hm : 2 ≤ m
  hn : 2 ≤ n
  hNz : EvalNonzeroCondition x
  hEx : Nonsymmetric.ExchangeRelationQOne (n := n) (R := ℝ) weight t
  hAdj : AdjacentDenomNonzero x t
  hpos : ∀ a : Question3.AdjIndex n, 0 < Question3.ratePlus x t a

def QOneBridgeInput.evalWeight (data : QOneBridgeInput m n) :
    BoundedWord m n → ℝ := fun u =>
  specializeCompositionWeight (ratEval data.x data.hNz) data.weight (toComposition u)

def QOneBridgeInput.pi (data : QOneBridgeInput m n) : BoundedWord m n → ℝ := fun u =>
  Question3.PiFromFstarPstar
    (Question3.FstarAtQ1ByDefinition data.evalWeight)
    data.Pstar u

theorem QOneBridgeInput.question3_full (data : QOneBridgeInput m n) :
    (∀ y : BoundedWord m n,
      (∑ w, data.pi w * Question3.transitionRate data.x data.t w y)
        =
      data.pi y * (∑ z, Question3.transitionRate data.x data.t y z))
    ∧
    (∃ w : BoundedWord m n, ∃ a : Question3.AdjIndex n,
      w ≠ Question3.swapAt w a ∧ 0 < Question3.localRate data.x data.t w a) := by
  simpa [QOneBridgeInput.pi, QOneBridgeInput.evalWeight] using
    question3_full_from_qOne_ratEval_auto_of_adjacentDenom
      (weight := data.weight)
      (x := data.x) (t := data.t) (Pstar := data.Pstar)
      (hm := data.hm) (hn := data.hn)
      (hNz := data.hNz) (hEx := data.hEx)
      (hAdj := data.hAdj) (hpos := data.hpos)

theorem QOneBridgeInput.stationary (data : QOneBridgeInput m n) :
    ∀ y : BoundedWord m n,
      (∑ w, data.pi w * Question3.transitionRate data.x data.t w y)
        =
      data.pi y * (∑ z, Question3.transitionRate data.x data.t y z) :=
  (data.question3_full).1

theorem QOneBridgeInput.nontrivial (data : QOneBridgeInput m n) :
    ∃ w : BoundedWord m n, ∃ a : Question3.AdjIndex n,
      w ≠ Question3.swapAt w a ∧ 0 < Question3.localRate data.x data.t w a :=
  (data.question3_full).2

end ProgramInput

end

end Bridge
end Macdonald
