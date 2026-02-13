import Macdonald.Bridge.Concrete

namespace Macdonald
namespace Bridge

open Question3
open Nonsymmetric

noncomputable section

section FstarTemplate

variable {m n : ℕ}

/--
Template payload for a concrete `F^*`-at-`q=1` candidate model on bounded words.

To instantiate the final theorem, users only need to provide this structure:
- rational-function weight family on compositions,
- exchange relation certificate,
- specialization/evaluation nonvanishing data,
- denominator and positivity side conditions.
-/
structure FstarQOneData (m n : ℕ) where
  weight : Conventions.Composition n → RatR n
  x : Fin n → ℝ
  t : ℝ
  Pstar : ℝ
  hm : 2 ≤ m
  hn : 2 ≤ n
  hNz : EvalNonzeroCondition x
  hExchange : Nonsymmetric.ExchangeRelationQOne (n := n) (R := ℝ) weight t
  hAdjDenom : AdjacentDenomNonzero x t
  hPos : ∀ a : Question3.AdjIndex n, 0 < Question3.ratePlus x t a

def FstarQOneData.toInput (data : FstarQOneData m n) : QOneRatEvalInput m n where
  weight := data.weight
  x := data.x
  t := data.t
  Pstar := data.Pstar
  hm := data.hm
  hn := data.hn
  hNz := data.hNz
  hEx := data.hExchange
  hAdj := data.hAdjDenom
  hpos := data.hPos

def FstarQOneData.evalWeight (data : FstarQOneData m n) :
    BoundedWord m n → ℝ :=
  data.toInput.evalWeight

def FstarQOneData.pi (data : FstarQOneData m n) : BoundedWord m n → ℝ :=
  data.toInput.pi

theorem FstarQOneData.n_eq_zero (data : FstarQOneData m n) : n = 0 :=
  eq_zero_of_EvalNonzeroCondition (x := data.x) data.hNz

theorem FstarQOneData.false_of_pos (data : FstarQOneData m n) (hn : 0 < n) : False :=
  not_EvalNonzeroCondition_of_pos (x := data.x) hn data.hNz

theorem FstarQOneData.question3_full (data : FstarQOneData m n) :
    (∀ y : BoundedWord m n,
      (∑ w, data.pi w * Question3.transitionRate data.x data.t w y)
        =
      data.pi y * (∑ z, Question3.transitionRate data.x data.t y z))
    ∧
    (∃ w : BoundedWord m n, ∃ a : Question3.AdjIndex n,
      w ≠ Question3.swapAt w a ∧ 0 < Question3.localRate data.x data.t w a) :=
  data.toInput.question3_full

theorem FstarQOneData.stationary (data : FstarQOneData m n) :
    ∀ y : BoundedWord m n,
      (∑ w, data.pi w * Question3.transitionRate data.x data.t w y)
        =
      data.pi y * (∑ z, Question3.transitionRate data.x data.t y z) :=
  data.toInput.stationary

theorem FstarQOneData.nontrivial (data : FstarQOneData m n) :
    ∃ w : BoundedWord m n, ∃ a : Question3.AdjIndex n,
      w ≠ Question3.swapAt w a ∧ 0 < Question3.localRate data.x data.t w a :=
  data.toInput.nontrivial

end FstarTemplate

end

end Bridge
end Macdonald
