import Macdonald.Bridge.Question3Finite
import Macdonald.Nonsymmetric.E

namespace Macdonald
namespace Bridge

open Question3
open Nonsymmetric
open Conventions
open scoped BigOperators

noncomputable section

section SpecializationToReal

variable {n : ℕ} {R : Type*} [CommRing R] [IsDomain R]

def specializeCompositionWeight
    (ev : Nonsymmetric.RatPoly n R →+* ℝ)
    (weight : Conventions.Composition n → Nonsymmetric.RatPoly n R) :
    Conventions.Composition n → ℝ := fun μ => ev (weight μ)

@[simp] lemma specializeCompositionWeight_apply
    (ev : Nonsymmetric.RatPoly n R →+* ℝ)
    (weight : Conventions.Composition n → Nonsymmetric.RatPoly n R)
    (μ : Conventions.Composition n) :
    specializeCompositionWeight ev weight μ = ev (weight μ) := rfl

theorem compositionExchangeReal_of_qOneSpecialization
    (ev : Nonsymmetric.RatPoly n R →+* ℝ)
    (weight : Conventions.Composition n → Nonsymmetric.RatPoly n R)
    (tR : R)
    (x : Fin n → ℝ) (t : ℝ)
    (hEx : Nonsymmetric.ExchangeRelationQOne (n := n) (R := R) weight tR)
    (hRatio :
      ∀ (i : Fin n) (h : i.1 + 1 < n),
        ev (Nonsymmetric.exchangeRatio (n := n) (R := R) tR i h) =
          Question3.ratio x t ⟨i, h⟩) :
    CompositionExchangeReal (weight := specializeCompositionWeight ev weight) x t := by
  intro μ i h hgt
  have hEx' := hEx μ i h hgt
  have hMapped :
      ev (weight (Nonsymmetric.swapComposition μ i h)) =
        ev (Nonsymmetric.exchangeRatio (n := n) (R := R) tR i h * weight μ) := by
    simpa using congrArg ev hEx'
  calc
    specializeCompositionWeight ev weight (Nonsymmetric.swapComposition μ i h)
      = ev (Nonsymmetric.exchangeRatio (n := n) (R := R) tR i h * weight μ) := hMapped
    _ = ev (Nonsymmetric.exchangeRatio (n := n) (R := R) tR i h) * ev (weight μ) := by
          simp
    _ = Question3.ratio x t ⟨i, h⟩ *
        specializeCompositionWeight ev weight μ := by
          simp [specializeCompositionWeight, hRatio]

theorem weightExchange_bounded_of_qOneSpecialization
    {m : ℕ}
    (ev : Nonsymmetric.RatPoly n R →+* ℝ)
    (weight : Conventions.Composition n → Nonsymmetric.RatPoly n R)
    (tR : R)
    (x : Fin n → ℝ) (t : ℝ)
    (hEx : Nonsymmetric.ExchangeRelationQOne (n := n) (R := R) weight tR)
    (hRatio :
      ∀ (i : Fin n) (h : i.1 + 1 < n),
        ev (Nonsymmetric.exchangeRatio (n := n) (R := R) tR i h) =
          Question3.ratio x t ⟨i, h⟩) :
    Question3.WeightExchange
      (Species := Fin m)
      (fun w : BoundedWord m n =>
        specializeCompositionWeight ev weight (toComposition w))
      x t := by
  exact weightExchange_bounded_of_compositionExchange
    (weight := specializeCompositionWeight ev weight)
    (x := x) (t := t)
    (compositionExchangeReal_of_qOneSpecialization
      (ev := ev) (weight := weight) (tR := tR) (x := x) (t := t) hEx hRatio)

theorem stationary_on_bounded_words_of_qOneSpecialization
    {m : ℕ}
    (ev : Nonsymmetric.RatPoly n R →+* ℝ)
    (weight : Conventions.Composition n → Nonsymmetric.RatPoly n R)
    (tR : R)
    (x : Fin n → ℝ) (t : ℝ) (Pstar : ℝ)
    (hEx : Nonsymmetric.ExchangeRelationQOne (n := n) (R := R) weight tR)
    (hRatio :
      ∀ (i : Fin n) (h : i.1 + 1 < n),
        ev (Nonsymmetric.exchangeRatio (n := n) (R := R) tR i h) =
          Question3.ratio x t ⟨i, h⟩)
    (hden : Question3.DenomNonzero x t) :
    ∀ y : BoundedWord m n,
      (∑ w,
        (specializeCompositionWeight ev weight (toComposition w) / Pstar) *
          Question3.transitionRate x t w y)
        =
      (specializeCompositionWeight ev weight (toComposition y) / Pstar) *
        (∑ z, Question3.transitionRate x t y z) := by
  exact stationary_on_bounded_words_of_compositionExchange
    (weight := specializeCompositionWeight ev weight)
    (x := x) (t := t) (Pstar := Pstar)
    (compositionExchangeReal_of_qOneSpecialization
      (ev := ev) (weight := weight) (tR := tR) (x := x) (t := t) hEx hRatio)
    hden

theorem question3_full_on_bounded_words_of_qOneSpecialization
    {m : ℕ}
    (ev : Nonsymmetric.RatPoly n R →+* ℝ)
    (weight : Conventions.Composition n → Nonsymmetric.RatPoly n R)
    (tR : R)
    (x : Fin n → ℝ) (t : ℝ) (Pstar : ℝ)
    (hEx : Nonsymmetric.ExchangeRelationQOne (n := n) (R := R) weight tR)
    (hRatio :
      ∀ (i : Fin n) (h : i.1 + 1 < n),
        ev (Nonsymmetric.exchangeRatio (n := n) (R := R) tR i h) =
          Question3.ratio x t ⟨i, h⟩)
    (hden : Question3.DenomNonzero x t)
    (hpos : ∀ a : Question3.AdjIndex n, 0 < Question3.ratePlus x t a)
    (hInv : ∃ w : BoundedWord m n, ∃ a : Question3.AdjIndex n,
      w (Question3.leftIndex a) > w (Question3.rightIndex a)) :
    (∀ y : BoundedWord m n,
      (∑ w, Question3.PiFromFstarPstar
        (Question3.FstarAtQ1ByDefinition
          (fun u : BoundedWord m n =>
            specializeCompositionWeight ev weight (toComposition u)))
          Pstar w
          * Question3.transitionRate x t w y)
        =
      Question3.PiFromFstarPstar
        (Question3.FstarAtQ1ByDefinition
          (fun u : BoundedWord m n =>
            specializeCompositionWeight ev weight (toComposition u)))
        Pstar y
        * (∑ z, Question3.transitionRate x t y z))
    ∧
    (∃ w : BoundedWord m n, ∃ a : Question3.AdjIndex n,
      w ≠ Question3.swapAt w a ∧ 0 < Question3.localRate x t w a) := by
  exact question3_full_on_bounded_words_of_compositionExchange
    (weight := specializeCompositionWeight ev weight)
    (x := x) (t := t) (Pstar := Pstar)
    (compositionExchangeReal_of_qOneSpecialization
      (ev := ev) (weight := weight) (tR := tR) (x := x) (t := t) hEx hRatio)
    hden hpos hInv

theorem question3_full_on_bounded_words_of_qOneSpecialization_auto
    {m : ℕ}
    (ev : Nonsymmetric.RatPoly n R →+* ℝ)
    (weight : Conventions.Composition n → Nonsymmetric.RatPoly n R)
    (tR : R)
    (x : Fin n → ℝ) (t : ℝ) (Pstar : ℝ)
    (hm : 2 ≤ m) (hn : 2 ≤ n)
    (hEx : Nonsymmetric.ExchangeRelationQOne (n := n) (R := R) weight tR)
    (hRatio :
      ∀ (i : Fin n) (h : i.1 + 1 < n),
        ev (Nonsymmetric.exchangeRatio (n := n) (R := R) tR i h) =
          Question3.ratio x t ⟨i, h⟩)
    (hden : Question3.DenomNonzero x t)
    (hpos : ∀ a : Question3.AdjIndex n, 0 < Question3.ratePlus x t a) :
    (∀ y : BoundedWord m n,
      (∑ w, Question3.PiFromFstarPstar
        (Question3.FstarAtQ1ByDefinition
          (fun u : BoundedWord m n =>
            specializeCompositionWeight ev weight (toComposition u)))
          Pstar w
          * Question3.transitionRate x t w y)
        =
      Question3.PiFromFstarPstar
        (Question3.FstarAtQ1ByDefinition
          (fun u : BoundedWord m n =>
            specializeCompositionWeight ev weight (toComposition u)))
        Pstar y
        * (∑ z, Question3.transitionRate x t y z))
    ∧
    (∃ w : BoundedWord m n, ∃ a : Question3.AdjIndex n,
      w ≠ Question3.swapAt w a ∧ 0 < Question3.localRate x t w a) := by
  exact question3_full_on_bounded_words_of_qOneSpecialization
    (ev := ev) (weight := weight) (tR := tR) (x := x) (t := t) (Pstar := Pstar)
    hEx hRatio hden hpos
    (exists_inversion_boundedWord (m := m) (n := n) hm hn)

end SpecializationToReal

end

end Bridge
end Macdonald
