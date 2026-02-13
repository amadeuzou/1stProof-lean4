import Macdonald.Bridge.QOneSpecialization

namespace Macdonald
namespace Bridge

open Question3
open Nonsymmetric
open Hecke
open Conventions
open scoped BigOperators

noncomputable section

section LocalRatioSpecialization

variable {n : ℕ} {R : Type*} [CommRing R] [IsDomain R]

/--
Minimal specialization data needed to evaluate local exchange ratios.

`ev` is any ring hom from rational functions; `x`/`t` are its target parameters, and
`map_coeff_t`/`map_ratVar` pin down images of the specific generators used by the ratio formula.
-/
structure LocalRatioSpecialization (n : ℕ) (R : Type*) [CommRing R] [IsDomain R] where
  ev : Nonsymmetric.RatPoly n R →+* ℝ
  x : Fin n → ℝ
  tR : R
  t : ℝ
  map_coeff_t : ev (Hecke.coeffToRat (n := n) (R := R) tR) = t
  map_ratVar : ∀ i : Fin n, ev (Hecke.ratVar (n := n) (R := R) i) = x i

@[simp] theorem LocalRatioSpecialization.map_exchangeRatio
    (spec : LocalRatioSpecialization n R)
    (i : Fin n) (h : i.1 + 1 < n) :
    spec.ev (Nonsymmetric.exchangeRatio (n := n) (R := R) spec.tR i h) =
      Question3.ratio spec.x spec.t ⟨i, h⟩ := by
  have hC : spec.ev (Hecke.toRat (n := n) (R := R) (MvPolynomial.C spec.tR)) = spec.t := by
    simpa [Hecke.coeffToRat] using spec.map_coeff_t
  simp [Nonsymmetric.exchangeRatio, Question3.ratio, Question3.ratePlus, Question3.rateMinus,
    Question3.leftIndex, Question3.rightIndex, Nonsymmetric.nextIndex,
    hC, spec.map_ratVar]

theorem question3_full_on_bounded_words_of_specialization_auto
    {m : ℕ}
    (weight : Conventions.Composition n → Nonsymmetric.RatPoly n R)
    (spec : LocalRatioSpecialization n R)
    (Pstar : ℝ)
    (hm : 2 ≤ m) (hn : 2 ≤ n)
    (hEx : Nonsymmetric.ExchangeRelationQOne (n := n) (R := R) weight spec.tR)
    (hden : Question3.DenomNonzero spec.x spec.t)
    (hpos : ∀ a : Question3.AdjIndex n, 0 < Question3.ratePlus spec.x spec.t a) :
    (∀ y : BoundedWord m n,
      (∑ w, Question3.PiFromFstarPstar
        (Question3.FstarAtQ1ByDefinition
          (fun u : BoundedWord m n =>
            specializeCompositionWeight spec.ev weight (toComposition u)))
          Pstar w
          * Question3.transitionRate spec.x spec.t w y)
        =
      Question3.PiFromFstarPstar
        (Question3.FstarAtQ1ByDefinition
          (fun u : BoundedWord m n =>
            specializeCompositionWeight spec.ev weight (toComposition u)))
        Pstar y
        * (∑ z, Question3.transitionRate spec.x spec.t y z))
    ∧
    (∃ w : BoundedWord m n, ∃ a : Question3.AdjIndex n,
      w ≠ Question3.swapAt w a ∧ 0 < Question3.localRate spec.x spec.t w a) := by
  exact question3_full_on_bounded_words_of_qOneSpecialization_auto
    (ev := spec.ev) (weight := weight) (tR := spec.tR)
    (x := spec.x) (t := spec.t) (Pstar := Pstar)
    hm hn hEx
    (by
      intro i h
      exact spec.map_exchangeRatio i h)
    hden hpos

end LocalRatioSpecialization

end

end Bridge
end Macdonald
