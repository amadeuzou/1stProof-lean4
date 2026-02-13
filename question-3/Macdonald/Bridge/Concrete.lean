import Macdonald.Bridge.Specialization
import Macdonald.Bridge.Evaluation

namespace Macdonald
namespace Bridge

open Question3
open Nonsymmetric

noncomputable section

section RatEvalConcrete

variable {n : ℕ}

/--
Canonical specialization object induced by `ratEval`.
-/
def ratEvalSpecialization
    (x : Fin n → ℝ) (hNz : EvalNonzeroCondition x) (t : ℝ) :
    LocalRatioSpecialization n ℝ where
  ev := ratEval x hNz
  x := x
  tR := t
  t := t
  map_coeff_t := by
    exact ratEval_coeffToRat (x := x) (hNz := hNz) (r := t)
  map_ratVar := by
    intro i
    exact ratEval_ratVar (x := x) (hNz := hNz) (i := i)

theorem question3_full_from_qOne_ratEval_via_specialization_auto
    {m : ℕ}
    (weight : Conventions.Composition n → RatR n)
    (x : Fin n → ℝ) (t : ℝ) (Pstar : ℝ)
    (hm : 2 ≤ m) (hn : 2 ≤ n)
    (hNz : EvalNonzeroCondition x)
    (hEx : Nonsymmetric.ExchangeRelationQOne (n := n) (R := ℝ) weight t)
    (hAdj : AdjacentDenomNonzero x t)
    (hpos : ∀ a : Question3.AdjIndex n, 0 < Question3.ratePlus x t a) :
    (∀ y : BoundedWord m n,
      (∑ w, Question3.PiFromFstarPstar
        (Question3.FstarAtQ1ByDefinition
          (fun u : BoundedWord m n =>
            specializeCompositionWeight (ratEval x hNz) weight (toComposition u)))
          Pstar w
          * Question3.transitionRate x t w y)
        =
      Question3.PiFromFstarPstar
        (Question3.FstarAtQ1ByDefinition
          (fun u : BoundedWord m n =>
            specializeCompositionWeight (ratEval x hNz) weight (toComposition u)))
        Pstar y
        * (∑ z, Question3.transitionRate x t y z))
    ∧
    (∃ w : BoundedWord m n, ∃ a : Question3.AdjIndex n,
      w ≠ Question3.swapAt w a ∧ 0 < Question3.localRate x t w a) := by
  let spec := ratEvalSpecialization (n := n) x hNz t
  simpa [spec, ratEvalSpecialization] using
    question3_full_on_bounded_words_of_specialization_auto
      (weight := weight) (spec := spec) (Pstar := Pstar)
      hm hn hEx
      (denomNonzero_of_adjacentDenomNonzero (x := x) (t := t) hAdj)
      hpos

/--
Single-object input for the fully automatic `ratEval` bridge pipeline.
-/
structure QOneRatEvalInput (m n : ℕ) where
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

def QOneRatEvalInput.evalWeight (data : QOneRatEvalInput m n) :
    BoundedWord m n → ℝ := fun u =>
  specializeCompositionWeight (ratEval data.x data.hNz) data.weight (toComposition u)

def QOneRatEvalInput.pi (data : QOneRatEvalInput m n) : BoundedWord m n → ℝ := fun u =>
  Question3.PiFromFstarPstar
    (Question3.FstarAtQ1ByDefinition data.evalWeight)
    data.Pstar u

theorem QOneRatEvalInput.n_eq_zero (data : QOneRatEvalInput m n) : n = 0 :=
  eq_zero_of_EvalNonzeroCondition (x := data.x) data.hNz

theorem QOneRatEvalInput.false_of_pos (data : QOneRatEvalInput m n) (hn : 0 < n) : False :=
  not_EvalNonzeroCondition_of_pos (x := data.x) hn data.hNz

theorem QOneRatEvalInput.question3_full (data : QOneRatEvalInput m n) :
    (∀ y : BoundedWord m n,
      (∑ w, data.pi w * Question3.transitionRate data.x data.t w y)
        =
      data.pi y * (∑ z, Question3.transitionRate data.x data.t y z))
    ∧
    (∃ w : BoundedWord m n, ∃ a : Question3.AdjIndex n,
      w ≠ Question3.swapAt w a ∧ 0 < Question3.localRate data.x data.t w a) := by
  simpa [QOneRatEvalInput.pi, QOneRatEvalInput.evalWeight] using
    question3_full_from_qOne_ratEval_via_specialization_auto
      (weight := data.weight)
      (x := data.x) (t := data.t) (Pstar := data.Pstar)
      (hm := data.hm) (hn := data.hn)
      (hNz := data.hNz) (hEx := data.hEx)
      (hAdj := data.hAdj) (hpos := data.hpos)

theorem QOneRatEvalInput.stationary (data : QOneRatEvalInput m n) :
    ∀ y : BoundedWord m n,
      (∑ w, data.pi w * Question3.transitionRate data.x data.t w y)
        =
      data.pi y * (∑ z, Question3.transitionRate data.x data.t y z) :=
  (data.question3_full).1

theorem QOneRatEvalInput.nontrivial (data : QOneRatEvalInput m n) :
    ∃ w : BoundedWord m n, ∃ a : Question3.AdjIndex n,
      w ≠ Question3.swapAt w a ∧ 0 < Question3.localRate data.x data.t w a :=
  (data.question3_full).2

end RatEvalConcrete

end

end Bridge
end Macdonald
