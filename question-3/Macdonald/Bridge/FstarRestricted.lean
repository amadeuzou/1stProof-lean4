import Macdonald.Bridge.FstarSnLambda

namespace Macdonald
namespace Bridge

open Question3
open Nonsymmetric
open scoped BigOperators

noncomputable section

section RestrictedProgram

variable {m n : ℕ} {R : Type*} [CommRing R] [IsDomain R]

/--
Program-level input matching the paper-style statement on restricted `λ`.

This is the current best interface for plugging in a concrete `F^*` candidate:
- algebraic data (`weight`, `ExchangeRelationQOne`);
- specialization data (`spec`) and rate-side assumptions;
- a restricted reference word `lam` describing the `S_n(λ)` orbit.
-/
structure FstarCandidateOnRestricted (m n : ℕ) (R : Type*) [CommRing R] [IsDomain R] where
  weight : Conventions.Composition n → Nonsymmetric.RatPoly n R
  spec : LocalRatioSpecialization n R
  Pstar : ℝ
  hm : 2 ≤ m
  hn : 2 ≤ n
  hExchange : Nonsymmetric.ExchangeRelationQOne (n := n) (R := R) weight spec.tR
  hDen : Question3.DenomNonzero spec.x spec.t
  hPos : ∀ a : AdjIndex n, 0 < Question3.ratePlus spec.x spec.t a
  lam : BoundedWord m n
  hRestricted : IsRestrictedWord lam

def FstarCandidateOnRestricted.toCore
    (data : FstarCandidateOnRestricted m n R) :
    FstarSpecializedData m n R where
  weight := data.weight
  spec := data.spec
  Pstar := data.Pstar
  hm := data.hm
  hn := data.hn
  hExchange := data.hExchange
  hDen := data.hDen
  hPos := data.hPos

def FstarCandidateOnRestricted.toSnData
    (data : FstarCandidateOnRestricted m n R) :
    FstarSnLambdaData m n R where
  core := data.toCore
  lam := data.lam
  hInv := exists_local_inversion_of_strictAdjacent
    (lam := data.lam) (hn := data.hn) data.hRestricted.1

def FstarCandidateOnRestricted.pi
    (data : FstarCandidateOnRestricted m n R) :
    SnLambdaState data.lam → ℝ :=
  data.toSnData.pi

theorem FstarCandidateOnRestricted.question3_full
    (data : FstarCandidateOnRestricted m n R) :
    (∀ y : SnLambdaState data.lam,
      (∑ w, data.pi w *
        transitionRateSn data.spec.x data.spec.t data.lam w y)
        =
      data.pi y *
        (∑ z, transitionRateSn data.spec.x data.spec.t data.lam y z))
    ∧
    (∃ w : SnLambdaState data.lam, ∃ a : AdjIndex n,
      w.1 ≠ swapAt w.1 a ∧
      0 < localRate data.spec.x data.spec.t w.1 a) := by
  simpa [FstarCandidateOnRestricted.pi] using
    data.toSnData.question3_full

theorem FstarCandidateOnRestricted.stationary
    (data : FstarCandidateOnRestricted m n R) :
    ∀ y : SnLambdaState data.lam,
      (∑ w, data.pi w *
        transitionRateSn data.spec.x data.spec.t data.lam w y)
        =
      data.pi y *
        (∑ z, transitionRateSn data.spec.x data.spec.t data.lam y z) :=
  (data.question3_full).1

theorem FstarCandidateOnRestricted.nontrivial
    (data : FstarCandidateOnRestricted m n R) :
    ∃ w : SnLambdaState data.lam, ∃ a : AdjIndex n,
      w.1 ≠ swapAt w.1 a ∧
      0 < localRate data.spec.x data.spec.t w.1 a :=
  (data.question3_full).2

theorem FstarCandidateOnRestricted.exists_markov_chain
    (data : FstarCandidateOnRestricted m n R) :
    ∃ (pi : SnLambdaState data.lam → ℝ),
      (∀ y : SnLambdaState data.lam,
        (∑ w, pi w *
          transitionRateSn data.spec.x data.spec.t data.lam w y)
          =
        pi y *
          (∑ z, transitionRateSn data.spec.x data.spec.t data.lam y z))
      ∧
      (∃ w : SnLambdaState data.lam, ∃ a : AdjIndex n,
        w.1 ≠ swapAt w.1 a ∧
        0 < localRate data.spec.x data.spec.t w.1 a) := by
  exact ⟨data.pi, data.question3_full⟩

def twoSiteCanonicalRestrictedData
    (spec : LocalRatioSpecialization 2 R)
    (Pstar : ℝ)
    (hm : 2 ≤ m)
    (hDen : Question3.DenomNonzero spec.x spec.t)
    (hPos : ∀ a : AdjIndex 2, 0 < Question3.ratePlus spec.x spec.t a)
    (lam : BoundedWord m 2)
    (hRes : IsRestrictedWord lam) :
    FstarCandidateOnRestricted m 2 R where
  weight := Nonsymmetric.twoSiteCanonicalWeight (R := R) spec.tR
  spec := spec
  Pstar := Pstar
  hm := hm
  hn := by decide
  hExchange := Nonsymmetric.exchangeRelationQOne_twoSiteCanonical (R := R) spec.tR
  hDen := hDen
  hPos := hPos
  lam := lam
  hRestricted := hRes

theorem question3_full_twoSiteCanonical_restricted
    (spec : LocalRatioSpecialization 2 R)
    (Pstar : ℝ)
    (hm : 2 ≤ m)
    (hDen : Question3.DenomNonzero spec.x spec.t)
    (hPos : ∀ a : AdjIndex 2, 0 < Question3.ratePlus spec.x spec.t a)
    (lam : BoundedWord m 2)
    (hRes : IsRestrictedWord lam) :
    (∀ y : SnLambdaState lam,
      (∑ w,
        (twoSiteCanonicalRestrictedData (m := m) (R := R)
          spec Pstar hm hDen hPos lam hRes).pi w
          * transitionRateSn spec.x spec.t lam w y)
        =
      (twoSiteCanonicalRestrictedData (m := m) (R := R)
        spec Pstar hm hDen hPos lam hRes).pi y
        * (∑ z, transitionRateSn spec.x spec.t lam y z))
    ∧
    (∃ w : SnLambdaState lam, ∃ a : AdjIndex 2,
      w.1 ≠ swapAt w.1 a ∧
      0 < localRate spec.x spec.t w.1 a) := by
  exact (twoSiteCanonicalRestrictedData
    (m := m) (R := R)
    spec Pstar hm hDen hPos lam hRes).question3_full

end RestrictedProgram

end

end Bridge
end Macdonald
