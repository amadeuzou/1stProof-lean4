import Macdonald.Bridge.QOneSpecialization

namespace Macdonald
namespace Bridge

open Question3
open Nonsymmetric
open Hecke

noncomputable section

section EvalAtReal

variable {n : ℕ}

abbrev PolyR (n : ℕ) := Hecke.PolyCR n ℝ
abbrev RatR (n : ℕ) := Nonsymmetric.RatPoly n ℝ

def polyEvalHom (x : Fin n → ℝ) : PolyR n →+* ℝ :=
  MvPolynomial.eval₂Hom (RingHom.id ℝ) x

@[simp] theorem polyEvalHom_C (x : Fin n → ℝ) (r : ℝ) :
    polyEvalHom x (MvPolynomial.C r) = r := by
  simp [polyEvalHom]

@[simp] theorem polyEvalHom_X (x : Fin n → ℝ) (i : Fin n) :
    polyEvalHom x (MvPolynomial.X i) = x i := by
  simp [polyEvalHom]

/--
Sufficient condition for evaluating rational functions at `x`:
every denominator candidate from `nonZeroDivisors` stays nonzero after polynomial evaluation.
-/
def EvalNonzeroCondition (x : Fin n → ℝ) : Prop :=
  ∀ y : nonZeroDivisors (PolyR n), polyEvalHom x y ≠ 0

/--
For positive dimension, `EvalNonzeroCondition` is impossible when evaluating
all coefficients in `ℝ`: the nonzero polynomial `X_i - C(x_i)` would vanish.
-/
theorem not_EvalNonzeroCondition_of_pos
    (x : Fin n → ℝ) (hn : 0 < n) :
    ¬ EvalNonzeroCondition x := by
  intro hNz
  let i0 : Fin n := ⟨0, hn⟩
  have hsingle : (Finsupp.single i0 1 : Fin n →₀ ℕ) ≠ 0 := by
    intro hs
    have : (Finsupp.single i0 1 : Fin n →₀ ℕ) i0 = 0 := by
      simp [hs]
    simpa using this
  have h0single : (0 : Fin n →₀ ℕ) ≠ Finsupp.single i0 1 := by
    simpa [eq_comm] using hsingle
  let p : PolyR n := MvPolynomial.X i0 - MvPolynomial.C (x i0)
  have hcoeffX : MvPolynomial.coeff (Finsupp.single i0 1) (MvPolynomial.X i0 : PolyR n) = (1 : ℝ) := by
    simpa using (MvPolynomial.coeff_X (i := i0) :
      MvPolynomial.coeff (Finsupp.single i0 1) (MvPolynomial.X i0 : PolyR n) = (1 : ℝ))
  have hcoeffC : MvPolynomial.coeff (Finsupp.single i0 1) (MvPolynomial.C (x i0) : PolyR n) = 0 := by
    simp [MvPolynomial.coeff_C, h0single]
  have hp_ne_zero : p ≠ 0 := by
    intro hp
    have hcoeff : MvPolynomial.coeff (Finsupp.single i0 1) p = (1 : ℝ) := by
      simp [p, hcoeffX, hcoeffC]
    have hcoeff0 : MvPolynomial.coeff (Finsupp.single i0 1) p = 0 := by
      rw [hp]
      simp
    exact one_ne_zero (hcoeff.symm.trans hcoeff0)
  have hp_nzd : p ∈ nonZeroDivisors (PolyR n) :=
    (mem_nonZeroDivisors_iff_ne_zero).2 hp_ne_zero
  let y : nonZeroDivisors (PolyR n) := ⟨p, hp_nzd⟩
  have hy := hNz y
  have hEval : polyEvalHom x p = 0 := by
    simp [polyEvalHom, p]
  exact hy hEval

theorem eq_zero_of_EvalNonzeroCondition
    (x : Fin n → ℝ)
    (hNz : EvalNonzeroCondition x) :
    n = 0 := by
  by_contra hn0
  exact not_EvalNonzeroCondition_of_pos (x := x) (hn := Nat.pos_iff_ne_zero.mpr hn0) hNz

/--
Evaluation of rational functions at `x`, obtained by localization universal property.
-/
def ratEval (x : Fin n → ℝ) (hNz : EvalNonzeroCondition x) : RatR n →+* ℝ :=
  IsLocalization.lift (M := nonZeroDivisors (PolyR n)) (S := RatR n)
    (g := polyEvalHom x)
    (fun y => (isUnit_iff_ne_zero).2 (hNz y))

@[simp] theorem ratEval_toRat
    (x : Fin n → ℝ) (hNz : EvalNonzeroCondition x) (p : PolyR n) :
    ratEval x hNz (Hecke.toRat (n := n) (R := ℝ) p) = polyEvalHom x p := by
  simp [ratEval, Hecke.toRat]

@[simp] theorem ratEval_ratVar
    (x : Fin n → ℝ) (hNz : EvalNonzeroCondition x) (i : Fin n) :
    ratEval x hNz (Hecke.ratVar (n := n) (R := ℝ) i) = x i := by
  simp [Hecke.ratVar, polyEvalHom]

@[simp] theorem ratEval_coeffToRat
    (x : Fin n → ℝ) (hNz : EvalNonzeroCondition x) (r : ℝ) :
    ratEval x hNz (Hecke.coeffToRat (n := n) (R := ℝ) r) = r := by
  simp [Hecke.coeffToRat, polyEvalHom]

@[simp] theorem ratEval_exchangeRatio
    (x : Fin n → ℝ) (hNz : EvalNonzeroCondition x)
    (t : ℝ) (i : Fin n) (h : i.1 + 1 < n) :
    ratEval x hNz (Nonsymmetric.exchangeRatio (n := n) (R := ℝ) t i h) =
      Question3.ratio x t ⟨i, h⟩ := by
  simp [Nonsymmetric.exchangeRatio, Question3.ratio, Question3.ratePlus, Question3.rateMinus,
    Question3.leftIndex, Question3.rightIndex, Nonsymmetric.nextIndex]

/--
Local denominator condition in index form, convenient for ASEP formulas.
-/
def AdjacentDenomNonzero (x : Fin n → ℝ) (t : ℝ) : Prop :=
  ∀ (i : Fin n) (h : i.1 + 1 < n), x i - t * x (Nonsymmetric.nextIndex i h) ≠ 0

theorem denomNonzero_of_adjacentDenomNonzero
    (x : Fin n → ℝ) (t : ℝ)
    (hAdj : AdjacentDenomNonzero x t) :
    Question3.DenomNonzero x t := by
  intro a
  exact hAdj a.1 a.2

/--
`x` is strictly decreasing on adjacent indices.
-/
def StrictAdjacentDesc (x : Fin n → ℝ) : Prop :=
  ∀ (i : Fin n) (h : i.1 + 1 < n), x i > x (Nonsymmetric.nextIndex i h)

theorem adjacentDenomNonzero_one_of_strictAdjacentDesc
    (x : Fin n → ℝ)
    (hDesc : StrictAdjacentDesc x) :
    AdjacentDenomNonzero x 1 := by
  intro i h
  have hne : x i ≠ x (Nonsymmetric.nextIndex i h) := ne_of_gt (hDesc i h)
  have hsub : x i - x (Nonsymmetric.nextIndex i h) ≠ 0 := sub_ne_zero.mpr hne
  simpa [Nonsymmetric.nextIndex] using hsub

theorem denomNonzero_one_of_strictAdjacentDesc
    (x : Fin n → ℝ)
    (hDesc : StrictAdjacentDesc x) :
    Question3.DenomNonzero x 1 :=
  denomNonzero_of_adjacentDenomNonzero
    (x := x) (t := 1)
    (adjacentDenomNonzero_one_of_strictAdjacentDesc (x := x) hDesc)

theorem ratePlus_pos_one_of_strictAdjacentDesc
    (x : Fin n → ℝ)
    (hDesc : StrictAdjacentDesc x) :
    ∀ a : Question3.AdjIndex n, 0 < Question3.ratePlus x 1 a := by
  intro a
  have hgt : x a.1 > x (Nonsymmetric.nextIndex a.1 a.2) := hDesc a.1 a.2
  have hsub : 0 < x a.1 - x (Nonsymmetric.nextIndex a.1 a.2) := sub_pos.mpr hgt
  simpa [Question3.ratePlus, Question3.leftIndex, Question3.rightIndex, Nonsymmetric.nextIndex] using hsub

theorem hRatio_of_ratEval
    (x : Fin n → ℝ) (hNz : EvalNonzeroCondition x) (t : ℝ) :
    ∀ (i : Fin n) (h : i.1 + 1 < n),
      ratEval x hNz (Nonsymmetric.exchangeRatio (n := n) (R := ℝ) t i h) =
        Question3.ratio x t ⟨i, h⟩ :=
  ratEval_exchangeRatio (x := x) (hNz := hNz) (t := t)

/--
Concrete bridge theorem:
from a `q=1` exchange relation on rational weights and an evaluable point `x`,
derive the full `Question3` conclusion on bounded words.
-/
theorem question3_full_from_qOne_ratEval_auto
    {m : ℕ}
    (weight : Conventions.Composition n → RatR n)
    (x : Fin n → ℝ) (t : ℝ) (Pstar : ℝ)
    (hm : 2 ≤ m) (hn : 2 ≤ n)
    (hNz : EvalNonzeroCondition x)
    (hEx : Nonsymmetric.ExchangeRelationQOne (n := n) (R := ℝ) weight t)
    (hden : Question3.DenomNonzero x t)
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
  exact question3_full_on_bounded_words_of_qOneSpecialization_auto
    (ev := ratEval x hNz) (weight := weight) (tR := t)
    (x := x) (t := t) (Pstar := Pstar)
    hm hn hEx (hRatio_of_ratEval (x := x) (hNz := hNz) (t := t)) hden hpos

theorem question3_full_from_qOne_ratEval_auto_of_adjacentDenom
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
  exact question3_full_from_qOne_ratEval_auto
    (weight := weight) (x := x) (t := t) (Pstar := Pstar)
    hm hn hNz hEx
    (denomNonzero_of_adjacentDenomNonzero (x := x) (t := t) hAdj)
    hpos

theorem question3_full_from_qOne_ratEval_auto_t_one_of_strictAdjacentDesc
    {m : ℕ}
    (weight : Conventions.Composition n → RatR n)
    (x : Fin n → ℝ) (Pstar : ℝ)
    (hm : 2 ≤ m) (hn : 2 ≤ n)
    (hNz : EvalNonzeroCondition x)
    (hEx : Nonsymmetric.ExchangeRelationQOne (n := n) (R := ℝ) weight (1 : ℝ))
    (hDesc : StrictAdjacentDesc x) :
    (∀ y : BoundedWord m n,
      (∑ w, Question3.PiFromFstarPstar
        (Question3.FstarAtQ1ByDefinition
          (fun u : BoundedWord m n =>
            specializeCompositionWeight (ratEval x hNz) weight (toComposition u)))
          Pstar w
          * Question3.transitionRate x 1 w y)
        =
      Question3.PiFromFstarPstar
        (Question3.FstarAtQ1ByDefinition
          (fun u : BoundedWord m n =>
            specializeCompositionWeight (ratEval x hNz) weight (toComposition u)))
        Pstar y
        * (∑ z, Question3.transitionRate x 1 y z))
    ∧
    (∃ w : BoundedWord m n, ∃ a : Question3.AdjIndex n,
      w ≠ Question3.swapAt w a ∧ 0 < Question3.localRate x 1 w a) := by
  exact question3_full_from_qOne_ratEval_auto_of_adjacentDenom
    (weight := weight) (x := x) (t := 1) (Pstar := Pstar)
    hm hn hNz hEx
    (adjacentDenomNonzero_one_of_strictAdjacentDesc (x := x) hDesc)
    (ratePlus_pos_one_of_strictAdjacentDesc (x := x) hDesc)

end EvalAtReal

end

end Bridge
end Macdonald
