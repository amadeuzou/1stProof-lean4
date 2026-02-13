import Macdonald.Bridge.FinalTheorem

namespace Macdonald
namespace Bridge

open Question3
open scoped BigOperators

noncomputable section

section LiteratureCompletion

variable {m n : ℕ} {R : Type*} [CommRing R] [IsDomain R]

def candidateTotalRate
    (data : FstarCandidateOnRestricted m n R)
    (u : SnLambdaState data.lam) : ℝ :=
  ∑ v : SnLambdaState data.lam,
    transitionRateSn data.spec.x data.spec.t data.lam u v

def candidateUniformizationBound
    (data : FstarCandidateOnRestricted m n R) : ℝ :=
  1 + ∑ u : SnLambdaState data.lam, candidateTotalRate data u

def candidateDiscreteKernel
    (data : FstarCandidateOnRestricted m n R)
    (u v : SnLambdaState data.lam) : ℝ :=
  by
    classical
    exact
      transitionRateSn data.spec.x data.spec.t data.lam u v
          / candidateUniformizationBound data
        +
      (if u = v then
        1 - candidateTotalRate data v / candidateUniformizationBound data
       else
        0)

lemma candidateTotalRate_nonneg
    (data : FstarCandidateOnRestricted m n R)
    (hPairNonneg : Question3.RatePairNonneg data.spec.x data.spec.t)
    (u : SnLambdaState data.lam) :
    0 ≤ candidateTotalRate data u := by
  unfold candidateTotalRate
  refine Finset.sum_nonneg ?_
  intro v hv
  simpa [transitionRateSn] using
    Question3.transitionRate_nonneg_of_ratePairNonneg
      (Species := Fin m)
      (x := data.spec.x) (t := data.spec.t) hPairNonneg u.1 v.1

lemma candidateUniformizationBound_pos
    (data : FstarCandidateOnRestricted m n R)
    (hPairNonneg : Question3.RatePairNonneg data.spec.x data.spec.t) :
    0 < candidateUniformizationBound data := by
  have hsum_nonneg :
      0 ≤ ∑ u : SnLambdaState data.lam, candidateTotalRate data u := by
    refine Finset.sum_nonneg ?_
    intro u hu
    exact candidateTotalRate_nonneg data hPairNonneg u
  unfold candidateUniformizationBound
  exact add_pos_of_pos_of_nonneg zero_lt_one hsum_nonneg

lemma candidateTotalRate_le_bound
    (data : FstarCandidateOnRestricted m n R)
    (hPairNonneg : Question3.RatePairNonneg data.spec.x data.spec.t)
    (u : SnLambdaState data.lam) :
    candidateTotalRate data u ≤ candidateUniformizationBound data := by
  have hle_sum :
      candidateTotalRate data u
        ≤ ∑ x : SnLambdaState data.lam, candidateTotalRate data x := by
    refine Finset.single_le_sum ?_ ?_
    · intro x hx
      exact candidateTotalRate_nonneg data hPairNonneg x
    · simp
  have hsum_le_bound :
      (∑ x : SnLambdaState data.lam, candidateTotalRate data x)
        ≤ 1 + ∑ x : SnLambdaState data.lam, candidateTotalRate data x := by
    exact le_add_of_nonneg_left (show (0 : ℝ) ≤ 1 by norm_num)
  unfold candidateUniformizationBound
  exact le_trans hle_sum hsum_le_bound

lemma candidateDiscreteKernel_nonneg
    (data : FstarCandidateOnRestricted m n R)
    (hPairNonneg : Question3.RatePairNonneg data.spec.x data.spec.t)
    (u v : SnLambdaState data.lam) :
    0 ≤ candidateDiscreteKernel data u v := by
  unfold candidateDiscreteKernel
  have hBpos : 0 < candidateUniformizationBound data :=
    candidateUniformizationBound_pos data hPairNonneg
  have hBnonneg : 0 ≤ candidateUniformizationBound data := hBpos.le
  have hRate :
      0 ≤ transitionRateSn data.spec.x data.spec.t data.lam u v := by
    simpa [transitionRateSn] using
      Question3.transitionRate_nonneg_of_ratePairNonneg
        (Species := Fin m)
        (x := data.spec.x) (t := data.spec.t) hPairNonneg u.1 v.1
  have hBase :
      0 ≤ transitionRateSn data.spec.x data.spec.t data.lam u v
        / candidateUniformizationBound data := by
    exact div_nonneg hRate hBnonneg
  by_cases huv : u = v
  · subst v
    have hdiag_le :
        candidateTotalRate data u / candidateUniformizationBound data ≤ 1 := by
      exact div_le_one_of_le₀ (candidateTotalRate_le_bound data hPairNonneg u) hBnonneg
    have hDiag : 0 ≤ 1 - candidateTotalRate data u / candidateUniformizationBound data :=
      sub_nonneg.mpr hdiag_le
    simpa [hDiag] using add_nonneg hBase hDiag
  · simp [huv, hBase]

lemma candidateDiscreteKernel_row_sum_one
    (data : FstarCandidateOnRestricted m n R)
    (u : SnLambdaState data.lam) :
    (∑ v : SnLambdaState data.lam, candidateDiscreteKernel data u v) = 1 := by
  classical
  let B : ℝ := candidateUniformizationBound data
  have hsumRate :
      (∑ v : SnLambdaState data.lam,
        transitionRateSn data.spec.x data.spec.t data.lam u v / B)
        = candidateTotalRate data u / B := by
    calc
      (∑ v : SnLambdaState data.lam,
        transitionRateSn data.spec.x data.spec.t data.lam u v / B)
          = (∑ v : SnLambdaState data.lam,
              transitionRateSn data.spec.x data.spec.t data.lam u v) * B⁻¹ := by
              simp [div_eq_mul_inv, Finset.sum_mul]
      _ = candidateTotalRate data u / B := by
            simp [candidateTotalRate, div_eq_mul_inv]
  have hsumDiag :
      (∑ v : SnLambdaState data.lam,
        (if u = v then 1 - candidateTotalRate data v / B else 0))
        = 1 - candidateTotalRate data u / B := by
    simp
  calc
    (∑ v : SnLambdaState data.lam, candidateDiscreteKernel data u v)
      =
    (∑ v : SnLambdaState data.lam,
      transitionRateSn data.spec.x data.spec.t data.lam u v / B)
      +
    (∑ v : SnLambdaState data.lam,
      (if u = v then 1 - candidateTotalRate data v / B else 0)) := by
        simp [candidateDiscreteKernel, B, Finset.sum_add_distrib]
    _ = candidateTotalRate data u / B + (1 - candidateTotalRate data u / B) := by
        rw [hsumRate, hsumDiag]
    _ = 1 := by ring

lemma candidateDiscreteKernel_stationary
    (data : FstarCandidateOnRestricted m n R)
    (y : SnLambdaState data.lam) :
    (∑ u : SnLambdaState data.lam, data.pi u * candidateDiscreteKernel data u y)
      =
    data.pi y := by
  classical
  let B : ℝ := candidateUniformizationBound data
  have hstatY :
      (∑ u : SnLambdaState data.lam,
        data.pi u * transitionRateSn data.spec.x data.spec.t data.lam u y)
        = data.pi y * candidateTotalRate data y := by
    simpa [candidateTotalRate] using data.stationary y
  have hsumRate :
      (∑ u : SnLambdaState data.lam,
        data.pi u * (transitionRateSn data.spec.x data.spec.t data.lam u y / B))
        =
      (∑ u : SnLambdaState data.lam,
        data.pi u * transitionRateSn data.spec.x data.spec.t data.lam u y) / B := by
    calc
      (∑ u : SnLambdaState data.lam,
        data.pi u * (transitionRateSn data.spec.x data.spec.t data.lam u y / B))
          = (∑ u : SnLambdaState data.lam,
              data.pi u * transitionRateSn data.spec.x data.spec.t data.lam u y) * B⁻¹ := by
              simp [div_eq_mul_inv, Finset.sum_mul, mul_assoc]
      _ = (∑ u : SnLambdaState data.lam,
            data.pi u * transitionRateSn data.spec.x data.spec.t data.lam u y) / B := by
            simp [div_eq_mul_inv]
  have hsumDiag :
      (∑ u : SnLambdaState data.lam,
        data.pi u * (if u = y then 1 - candidateTotalRate data y / B else 0))
        =
      data.pi y * (1 - candidateTotalRate data y / B) := by
    simp
  calc
    (∑ u : SnLambdaState data.lam, data.pi u * candidateDiscreteKernel data u y)
      =
    (∑ u : SnLambdaState data.lam,
      data.pi u * (transitionRateSn data.spec.x data.spec.t data.lam u y / B))
      +
    (∑ u : SnLambdaState data.lam,
      data.pi u * (if u = y then 1 - candidateTotalRate data y / B else 0)) := by
        simp [candidateDiscreteKernel, B, mul_add, Finset.sum_add_distrib]
    _ =
    ((∑ u : SnLambdaState data.lam,
      data.pi u * transitionRateSn data.spec.x data.spec.t data.lam u y) / B)
      +
    data.pi y * (1 - candidateTotalRate data y / B) := by
        rw [hsumRate, hsumDiag]
    _ = (data.pi y * candidateTotalRate data y) / B
      + data.pi y * (1 - candidateTotalRate data y / B) := by
        rw [hstatY]
    _ = data.pi y := by ring

lemma exists_positive_offdiag_candidateDiscreteKernel
    (data : FstarCandidateOnRestricted m n R)
    (hPairNonneg : Question3.RatePairNonneg data.spec.x data.spec.t) :
    ∃ u v : SnLambdaState data.lam, u ≠ v ∧ 0 < candidateDiscreteKernel data u v := by
  rcases data.nontrivial with ⟨u, a, hneq, hlocalPos⟩
  let v : SnLambdaState data.lam := ⟨swapAt u.1 a, snLambda_closed_swap u.2 a⟩
  have huv : u ≠ v := by
    intro huvEq
    apply hneq
    exact congrArg Subtype.val huvEq
  have hedgePos :
      0 < edgeKernel data.spec.x data.spec.t u.1 v.1 a := by
    simpa [edgeKernel, v] using hlocalPos
  have hedgeLe :
      edgeKernel data.spec.x data.spec.t u.1 v.1 a
        ≤ transitionRate data.spec.x data.spec.t u.1 v.1 := by
    unfold transitionRate
    refine Finset.single_le_sum ?_ (by simp)
    intro b hb
    exact Question3.edgeKernel_nonneg_of_ratePairNonneg
      (Species := Fin m)
      (x := data.spec.x) (t := data.spec.t) hPairNonneg u.1 v.1 b
  have hratePos :
      0 < transitionRate data.spec.x data.spec.t u.1 v.1 :=
    lt_of_lt_of_le hedgePos hedgeLe
  have hBpos : 0 < candidateUniformizationBound data :=
    candidateUniformizationBound_pos data hPairNonneg
  have hdivPos :
      0 < transitionRateSn data.spec.x data.spec.t data.lam u v
        / candidateUniformizationBound data := by
    simpa [transitionRateSn, v] using div_pos hratePos hBpos
  have hprobPos : 0 < candidateDiscreteKernel data u v := by
    simpa [candidateDiscreteKernel, huv, v] using hdivPos
  exact ⟨u, v, huv, hprobPos⟩

/--
Paper-level completion theorem for a concrete interpolation candidate:
if the candidate supplies exchange, rate-side nonnegativity and normalized nonnegative `pi`,
then we obtain a nontrivial discrete-time Markov chain whose stationary distribution is
exactly `F^*/P^*` on `S_n(λ)`.
-/
theorem paper_main_restricted_qOne_discrete_of_literature_assumptions
    (data : FstarCandidateOnRestricted m n R)
    (hPairNonneg : Question3.RatePairNonneg data.spec.x data.spec.t)
    (hPiNonneg : ∀ u : SnLambdaState data.lam, 0 ≤ data.pi u)
    (hPiSum : (∑ u : SnLambdaState data.lam, data.pi u) = 1) :
    ∃ (mc : DiscreteMarkovChain (SnLambdaState data.lam)),
      IsStationaryDist data.pi mc.prob
      ∧
      (∀ u v : SnLambdaState data.lam,
        mc.prob u v = candidateDiscreteKernel data u v)
      ∧
      (∀ u : SnLambdaState data.lam,
        data.pi u =
          PiFromFstarPstar
            (FstarAtQ1ByDefinition data.toCore.evalWeight)
            data.Pstar u.1)
      ∧
      (∃ u v : SnLambdaState data.lam, u ≠ v ∧ 0 < mc.prob u v) := by
  let mc : DiscreteMarkovChain (SnLambdaState data.lam) := {
    prob := candidateDiscreteKernel data
    nonneg := candidateDiscreteKernel_nonneg data hPairNonneg
    row_sum_one := candidateDiscreteKernel_row_sum_one data
  }
  refine ⟨mc, ?_, ?_, ?_, ?_⟩
  · refine ⟨hPiNonneg, hPiSum, ?_⟩
    intro y
    have hstat := candidateDiscreteKernel_stationary data y
    calc
      (∑ x : SnLambdaState data.lam, data.pi x * mc.prob x y)
        = data.pi y := by simpa [mc] using hstat
      _ = data.pi y * (∑ z : SnLambdaState data.lam, mc.prob y z) := by
            rw [mc.row_sum_one y]
            ring
  · intro u v
    rfl
  · intro u
    simpa [paperPi] using paperPi_apply data u
  · rcases exists_positive_offdiag_candidateDiscreteKernel data hPairNonneg with ⟨u, v, huv, hpos⟩
    exact ⟨u, v, huv, by simpa [mc] using hpos⟩

end LiteratureCompletion

end

end Bridge
end Macdonald
