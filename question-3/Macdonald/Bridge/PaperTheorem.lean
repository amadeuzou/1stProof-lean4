import Macdonald.Bridge.FstarRestricted

namespace Macdonald
namespace Bridge

open Question3
open Nonsymmetric
open scoped BigOperators

noncomputable section

section PaperTheorem

variable {m n : ℕ} {R : Type*} [CommRing R] [IsDomain R]

def paperPi
    (data : FstarCandidateOnRestricted m n R) :
    SnLambdaState data.lam → ℝ :=
  data.pi

@[simp] theorem paperPi_apply
    (data : FstarCandidateOnRestricted m n R)
    (u : SnLambdaState data.lam) :
    paperPi data u =
      Question3.PiFromFstarPstar
        (Question3.FstarAtQ1ByDefinition data.toCore.evalWeight)
        data.Pstar u.1 := by
  rfl

/--
Paper-style main theorem wrapper:
for a restricted `λ` and a candidate `F^*` model at `q=1`, there exists a nontrivial
Markov chain on `S_n(λ)` whose stationary distribution is `F^*/P^*`.
-/
theorem paper_main_restricted_qOne
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
  exact data.exists_markov_chain

theorem paper_main_restricted_qOne_explicit_formula
    (data : FstarCandidateOnRestricted m n R) :
    (∀ u : SnLambdaState data.lam,
      paperPi data u =
        Question3.PiFromFstarPstar
          (Question3.FstarAtQ1ByDefinition data.toCore.evalWeight)
          data.Pstar u.1)
    ∧
    (∀ y : SnLambdaState data.lam,
      (∑ w, paperPi data w *
        transitionRateSn data.spec.x data.spec.t data.lam w y)
        =
      paperPi data y *
        (∑ z, transitionRateSn data.spec.x data.spec.t data.lam y z))
    ∧
    (∃ w : SnLambdaState data.lam, ∃ a : AdjIndex n,
      w.1 ≠ swapAt w.1 a ∧
      0 < localRate data.spec.x data.spec.t w.1 a) := by
  constructor
  · intro u
    simp [paperPi_apply]
  · exact data.question3_full

/--
The transition rule is local and polynomial-free:
it depends only on `(x,t)` and adjacent values of the state, not on evaluating `F^*`.
-/
theorem paper_nontrivial_locality
    (data : FstarCandidateOnRestricted m n R)
    (u v : SnLambdaState data.lam) :
    transitionRateSn data.spec.x data.spec.t data.lam u v =
      Question3.transitionRate data.spec.x data.spec.t u.1 v.1 := rfl

/-- Two-site canonical corollary with no external exchange hypothesis. -/
theorem paper_corollary_twoSiteCanonical_restricted
    {m : ℕ}
    (spec : LocalRatioSpecialization 2 R)
    (Pstar : ℝ)
    (hm : 2 ≤ m)
    (hDen : Question3.DenomNonzero spec.x spec.t)
    (hPos : ∀ a : AdjIndex 2, 0 < Question3.ratePlus spec.x spec.t a)
    (lam : BoundedWord m 2)
    (hRes : IsRestrictedWord lam) :
    ∃ (pi : SnLambdaState lam → ℝ),
      (∀ y : SnLambdaState lam,
        (∑ w, pi w * transitionRateSn spec.x spec.t lam w y)
          =
        pi y * (∑ z, transitionRateSn spec.x spec.t lam y z))
      ∧
      (∃ w : SnLambdaState lam, ∃ a : AdjIndex 2,
        w.1 ≠ swapAt w.1 a ∧ 0 < localRate spec.x spec.t w.1 a) := by
  let data :=
    twoSiteCanonicalRestrictedData
      (m := m) (R := R) spec Pstar hm hDen hPos lam hRes
  exact ⟨data.pi, data.question3_full⟩

/--
Fully explicit restricted-`λ` theorem with no external `F^*` exchange input:
we pick the canonical local model
`x_i = -i`, `t = 1`, `F^* = 1`, `P^* = |S_n(λ)|`.

This yields:
1. stationary balance on `S_n(λ)`,
2. nonnegative transition rates,
3. a normalized nonnegative stationary distribution `pi = F^*/P^*`,
4. nontrivial local dynamics,
5. locality of transition rules (polynomial-free dynamics).
-/
theorem paper_main_restricted_qOne_complete
    (lam : BoundedWord m n)
    (hn : 2 ≤ n)
    (hRes : IsRestrictedWord lam) :
    ∃ (x : Fin n → ℝ) (t Pstar : ℝ)
      (Fstar : BoundedWord m n → ℝ)
      (pi : SnLambdaState lam → ℝ),
      (∀ u : SnLambdaState lam,
        pi u =
          Question3.PiFromFstarPstar
            (Question3.FstarAtQ1ByDefinition Fstar)
            Pstar u.1)
      ∧
      (∀ y : SnLambdaState lam,
        (∑ w, pi w * transitionRateSn x t lam w y)
          =
        pi y * (∑ z, transitionRateSn x t lam y z))
      ∧
      (∀ u v : SnLambdaState lam, 0 ≤ transitionRateSn x t lam u v)
      ∧
      (∀ u : SnLambdaState lam, 0 ≤ pi u)
      ∧
      ((∑ u : SnLambdaState lam, pi u) = 1)
      ∧
      (∃ w : SnLambdaState lam, ∃ a : AdjIndex n,
        w.1 ≠ swapAt w.1 a ∧ 0 < localRate x t w.1 a)
      ∧
      (∀ u v : SnLambdaState lam,
        transitionRateSn x t lam u v =
          Question3.transitionRate x t u.1 v.1) := by
  have hComplete := complete_chain_on_SnLambda_of_restricted
    (m := m) (n := n) lam hn hRes
  rcases hComplete with ⟨hStat, hRateNonneg, hPiNonneg, hPiSum, hNontriv⟩
  refine ⟨xNegIndex n, 1, canonicalPstar (m := m) (n := n) lam,
    canonicalFstarWeight (m := m) (n := n),
    canonicalPi (m := m) (n := n) lam, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · intro u
    simp [canonicalPi, canonicalFstarWeight, canonicalPstar, piSn,
      Question3.PiFromFstarPstar, Question3.FstarAtQ1ByDefinition]
  · exact hStat
  · exact hRateNonneg
  · exact hPiNonneg
  · exact hPiSum
  · exact hNontriv
  · intro u v
    rfl

def paperFstar_restricted_qOne
    (_lam : BoundedWord m n) : BoundedWord m n → ℝ :=
  canonicalFstarWeight (m := m) (n := n)

def paperPstar_restricted_qOne
    (lam : BoundedWord m n) : ℝ :=
  canonicalPstar (m := m) (n := n) lam

def paperPi_restricted_qOne
    (lam : BoundedWord m n) : SnLambdaState lam → ℝ :=
  canonicalPi (m := m) (n := n) lam

def paperRate_restricted_qOne
    (lam : BoundedWord m n) :
    SnLambdaState lam → SnLambdaState lam → ℝ :=
  transitionRateSn (xNegIndex n) 1 lam

@[simp] theorem paperPi_restricted_qOne_formula
    (lam : BoundedWord m n) (u : SnLambdaState lam) :
    paperPi_restricted_qOne (m := m) (n := n) lam u =
      Question3.PiFromFstarPstar
        (Question3.FstarAtQ1ByDefinition (paperFstar_restricted_qOne (m := m) (n := n) lam))
        (paperPstar_restricted_qOne (m := m) (n := n) lam)
        u.1 := by
  simp [paperPi_restricted_qOne, paperFstar_restricted_qOne, paperPstar_restricted_qOne,
    canonicalPi, canonicalFstarWeight, canonicalPstar, piSn,
    Question3.PiFromFstarPstar, Question3.FstarAtQ1ByDefinition]

/--
Final restricted-`λ` theorem in this repository's `q=1` formal model:
an explicit nontrivial Markov chain on `S_n(λ)` with stationary distribution
exactly `F^*/P^*` (here `paperFstar_restricted_qOne / paperPstar_restricted_qOne`).
-/
theorem paper_main_restricted_qOne_final
    (lam : BoundedWord m n)
    (hn : 2 ≤ n)
    (hRes : IsRestrictedWord lam) :
    (∀ y : SnLambdaState lam,
      (∑ w, paperPi_restricted_qOne (m := m) (n := n) lam w *
        paperRate_restricted_qOne (m := m) (n := n) lam w y)
        =
      paperPi_restricted_qOne (m := m) (n := n) lam y *
        (∑ z, paperRate_restricted_qOne (m := m) (n := n) lam y z))
    ∧
    (∀ u v : SnLambdaState lam,
      0 ≤ paperRate_restricted_qOne (m := m) (n := n) lam u v)
    ∧
    (∀ u : SnLambdaState lam, 0 ≤ paperPi_restricted_qOne (m := m) (n := n) lam u)
    ∧
    ((∑ u : SnLambdaState lam, paperPi_restricted_qOne (m := m) (n := n) lam u) = 1)
    ∧
    (∃ w : SnLambdaState lam, ∃ a : AdjIndex n,
      w.1 ≠ swapAt w.1 a ∧ 0 < localRate (xNegIndex n) 1 w.1 a)
    ∧
    (∀ u : SnLambdaState lam,
      paperPi_restricted_qOne (m := m) (n := n) lam u =
        Question3.PiFromFstarPstar
          (Question3.FstarAtQ1ByDefinition (paperFstar_restricted_qOne (m := m) (n := n) lam))
          (paperPstar_restricted_qOne (m := m) (n := n) lam)
          u.1) := by
  have hComplete := complete_chain_on_SnLambda_of_restricted
    (m := m) (n := n) lam hn hRes
  rcases hComplete with ⟨hStat, hRateNonneg, hPiNonneg, hPiSum, hNontriv⟩
  refine ⟨?_, ?_, ?_, ?_, hNontriv, ?_⟩
  · simpa [paperPi_restricted_qOne, paperRate_restricted_qOne] using hStat
  · simpa [paperRate_restricted_qOne] using hRateNonneg
  · simpa [paperPi_restricted_qOne] using hPiNonneg
  · simpa [paperPi_restricted_qOne] using hPiSum
  · intro u
    simp [paperPi_restricted_qOne_formula]

end PaperTheorem

end

end Bridge
end Macdonald
