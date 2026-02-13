import Macdonald.Bridge.PaperTheorem

namespace Macdonald
namespace Bridge

open Question3
open scoped BigOperators

noncomputable section

section FinalTheorem

variable {m n : ℕ}

structure ContinuousTimeMarkovChain (State : Type*) where
  rate : State → State → ℝ
  nonneg : ∀ x y, 0 ≤ rate x y

structure DiscreteMarkovChain (State : Type*) [Fintype State] where
  prob : State → State → ℝ
  nonneg : ∀ x y, 0 ≤ prob x y
  row_sum_one : ∀ x, (∑ y, prob x y) = 1

def IsStationaryDist
    {State : Type*} [Fintype State]
    (pi : State → ℝ) (rate : State → State → ℝ) : Prop :=
  (∀ x, 0 ≤ pi x) ∧
  (∑ x, pi x) = 1 ∧
  (∀ y, (∑ x, pi x * rate x y) = pi y * (∑ z, rate y z))

def IsLocalAndPolynomialFree
    (lam : BoundedWord m n)
    (x : Fin n → ℝ) (t : ℝ)
    (rate : SnLambdaState lam → SnLambdaState lam → ℝ) : Prop :=
  ∀ u v, rate u v = transitionRate x t u.1 v.1

def paperTotalRate
    (lam : BoundedWord m n) (u : SnLambdaState lam) : ℝ :=
  ∑ v : SnLambdaState lam, paperRate_restricted_qOne (m := m) (n := n) lam u v

def paperUniformizationBound
    (lam : BoundedWord m n) : ℝ :=
  1 + ∑ u : SnLambdaState lam, paperTotalRate (m := m) (n := n) lam u

def paperDiscreteKernel
    (lam : BoundedWord m n)
    (u v : SnLambdaState lam) : ℝ :=
  by
    classical
    exact
      paperRate_restricted_qOne (m := m) (n := n) lam u v
          / paperUniformizationBound (m := m) (n := n) lam
        +
      (if u = v then
        1 - paperTotalRate (m := m) (n := n) lam v
          / paperUniformizationBound (m := m) (n := n) lam
       else
        0)

lemma paperTotalRate_nonneg
    (lam : BoundedWord m n) (u : SnLambdaState lam) :
    0 ≤ paperTotalRate (m := m) (n := n) lam u := by
  unfold paperTotalRate
  refine Finset.sum_nonneg ?_
  intro v hv
  exact canonical_transitionRateSn_nonneg (m := m) (n := n) lam u v

lemma paperUniformizationBound_pos
    (lam : BoundedWord m n) :
    0 < paperUniformizationBound (m := m) (n := n) lam := by
  have hsum_nonneg :
      0 ≤ ∑ u : SnLambdaState lam, paperTotalRate (m := m) (n := n) lam u := by
    refine Finset.sum_nonneg ?_
    intro u hu
    exact paperTotalRate_nonneg (m := m) (n := n) lam u
  unfold paperUniformizationBound
  exact add_pos_of_pos_of_nonneg zero_lt_one hsum_nonneg

lemma paperTotalRate_le_bound
    (lam : BoundedWord m n) (u : SnLambdaState lam) :
    paperTotalRate (m := m) (n := n) lam u
      ≤ paperUniformizationBound (m := m) (n := n) lam := by
  have hle_sum :
      paperTotalRate (m := m) (n := n) lam u
        ≤ ∑ x : SnLambdaState lam, paperTotalRate (m := m) (n := n) lam x := by
    refine Finset.single_le_sum ?_ ?_
    · intro x hx
      exact paperTotalRate_nonneg (m := m) (n := n) lam x
    · simp
  have hsum_le_bound :
      (∑ x : SnLambdaState lam, paperTotalRate (m := m) (n := n) lam x)
        ≤ 1 + ∑ x : SnLambdaState lam, paperTotalRate (m := m) (n := n) lam x := by
    exact le_add_of_nonneg_left (show (0 : ℝ) ≤ 1 by norm_num)
  unfold paperUniformizationBound
  exact le_trans hle_sum hsum_le_bound

lemma paperDiscreteKernel_nonneg
    (lam : BoundedWord m n)
    (u v : SnLambdaState lam) :
    0 ≤ paperDiscreteKernel (m := m) (n := n) lam u v := by
  unfold paperDiscreteKernel
  have hBpos : 0 < paperUniformizationBound (m := m) (n := n) lam :=
    paperUniformizationBound_pos (m := m) (n := n) lam
  have hBnonneg : 0 ≤ paperUniformizationBound (m := m) (n := n) lam := hBpos.le
  have hRate :
      0 ≤ paperRate_restricted_qOne (m := m) (n := n) lam u v :=
    canonical_transitionRateSn_nonneg (m := m) (n := n) lam u v
  have hBase :
      0 ≤ paperRate_restricted_qOne (m := m) (n := n) lam u v
        / paperUniformizationBound (m := m) (n := n) lam := by
    exact div_nonneg hRate hBnonneg
  by_cases huv : u = v
  · subst v
    have hdiag_le :
        paperTotalRate (m := m) (n := n) lam u
          / paperUniformizationBound (m := m) (n := n) lam ≤ 1 := by
      exact div_le_one_of_le₀
        (paperTotalRate_le_bound (m := m) (n := n) lam u) hBnonneg
    have hDiag : 0 ≤ 1 - paperTotalRate (m := m) (n := n) lam u
      / paperUniformizationBound (m := m) (n := n) lam := sub_nonneg.mpr hdiag_le
    simpa [hDiag] using add_nonneg hBase hDiag
  · simp [huv, hBase]

lemma paperDiscreteKernel_row_sum_one
    (lam : BoundedWord m n)
    (u : SnLambdaState lam) :
    (∑ v : SnLambdaState lam, paperDiscreteKernel (m := m) (n := n) lam u v) = 1 := by
  classical
  let B : ℝ := paperUniformizationBound (m := m) (n := n) lam
  have hBpos : 0 < B := by
    simpa [B] using paperUniformizationBound_pos (m := m) (n := n) lam
  have hsumRate :
      (∑ v : SnLambdaState lam,
        paperRate_restricted_qOne (m := m) (n := n) lam u v / B)
        = paperTotalRate (m := m) (n := n) lam u / B := by
    calc
      (∑ v : SnLambdaState lam,
        paperRate_restricted_qOne (m := m) (n := n) lam u v / B)
          = (∑ v : SnLambdaState lam,
            paperRate_restricted_qOne (m := m) (n := n) lam u v) * B⁻¹ := by
              simp [div_eq_mul_inv, Finset.sum_mul]
      _ = paperTotalRate (m := m) (n := n) lam u / B := by
            simp [paperTotalRate, div_eq_mul_inv]
  have hsumDiag :
      (∑ v : SnLambdaState lam,
        (if u = v then
          1 - paperTotalRate (m := m) (n := n) lam v / B
         else
          0))
        = 1 - paperTotalRate (m := m) (n := n) lam u / B := by
    simp
  calc
    (∑ v : SnLambdaState lam, paperDiscreteKernel (m := m) (n := n) lam u v)
      = (∑ v : SnLambdaState lam,
          paperRate_restricted_qOne (m := m) (n := n) lam u v / B)
        + (∑ v : SnLambdaState lam,
          (if u = v then
            1 - paperTotalRate (m := m) (n := n) lam v / B
           else
            0)) := by
              simp [paperDiscreteKernel, B, Finset.sum_add_distrib]
    _ = paperTotalRate (m := m) (n := n) lam u / B
        + (1 - paperTotalRate (m := m) (n := n) lam u / B) := by
          rw [hsumRate, hsumDiag]
    _ = 1 := by ring

lemma paperDiscreteKernel_stationary
    (lam : BoundedWord m n)
    (hn : 2 ≤ n)
    (hRes : IsRestrictedWord lam) :
    ∀ y : SnLambdaState lam,
      (∑ u : SnLambdaState lam,
        paperPi_restricted_qOne (m := m) (n := n) lam u
          * paperDiscreteKernel (m := m) (n := n) lam u y)
        =
      paperPi_restricted_qOne (m := m) (n := n) lam y := by
  classical
  have hFinal := paper_main_restricted_qOne_final (m := m) (n := n) lam hn hRes
  rcases hFinal with ⟨hStat, _hRateNonneg, _hPiNonneg, _hPiSum, _hNontriv, _hFormula⟩
  intro y
  let B : ℝ := paperUniformizationBound (m := m) (n := n) lam
  have hstatY :
      (∑ u : SnLambdaState lam,
        paperPi_restricted_qOne (m := m) (n := n) lam u
          * paperRate_restricted_qOne (m := m) (n := n) lam u y)
        =
      paperPi_restricted_qOne (m := m) (n := n) lam y
        * paperTotalRate (m := m) (n := n) lam y := by
    simpa [paperTotalRate, paperRate_restricted_qOne] using hStat y
  have hsumRate :
      (∑ u : SnLambdaState lam,
        paperPi_restricted_qOne (m := m) (n := n) lam u
          * (paperRate_restricted_qOne (m := m) (n := n) lam u y / B))
        =
      (∑ u : SnLambdaState lam,
        paperPi_restricted_qOne (m := m) (n := n) lam u
          * paperRate_restricted_qOne (m := m) (n := n) lam u y) / B := by
    calc
      (∑ u : SnLambdaState lam,
        paperPi_restricted_qOne (m := m) (n := n) lam u
          * (paperRate_restricted_qOne (m := m) (n := n) lam u y / B))
          = (∑ u : SnLambdaState lam,
              paperPi_restricted_qOne (m := m) (n := n) lam u
                * paperRate_restricted_qOne (m := m) (n := n) lam u y) * B⁻¹ := by
              simp [div_eq_mul_inv, Finset.sum_mul, mul_assoc]
      _ = (∑ u : SnLambdaState lam,
            paperPi_restricted_qOne (m := m) (n := n) lam u
              * paperRate_restricted_qOne (m := m) (n := n) lam u y) / B := by
            simp [div_eq_mul_inv]
  have hsumDiag :
      (∑ u : SnLambdaState lam,
        paperPi_restricted_qOne (m := m) (n := n) lam u
          * (if u = y then 1 - paperTotalRate (m := m) (n := n) lam y / B else 0))
        =
      paperPi_restricted_qOne (m := m) (n := n) lam y
        * (1 - paperTotalRate (m := m) (n := n) lam y / B) := by
    simp
  calc
    (∑ u : SnLambdaState lam,
      paperPi_restricted_qOne (m := m) (n := n) lam u
        * paperDiscreteKernel (m := m) (n := n) lam u y)
      =
    (∑ u : SnLambdaState lam,
      paperPi_restricted_qOne (m := m) (n := n) lam u
        * (paperRate_restricted_qOne (m := m) (n := n) lam u y / B))
      +
    (∑ u : SnLambdaState lam,
      paperPi_restricted_qOne (m := m) (n := n) lam u
        * (if u = y then 1 - paperTotalRate (m := m) (n := n) lam y / B else 0)) := by
        simp [paperDiscreteKernel, B, mul_add, Finset.sum_add_distrib]
    _ =
    ((∑ u : SnLambdaState lam,
      paperPi_restricted_qOne (m := m) (n := n) lam u
        * paperRate_restricted_qOne (m := m) (n := n) lam u y) / B)
      +
    paperPi_restricted_qOne (m := m) (n := n) lam y
      * (1 - paperTotalRate (m := m) (n := n) lam y / B) := by
        rw [hsumRate, hsumDiag]
    _ =
    (paperPi_restricted_qOne (m := m) (n := n) lam y
      * paperTotalRate (m := m) (n := n) lam y) / B
      +
    paperPi_restricted_qOne (m := m) (n := n) lam y
      * (1 - paperTotalRate (m := m) (n := n) lam y / B) := by
        rw [hstatY]
    _ = paperPi_restricted_qOne (m := m) (n := n) lam y := by ring

lemma exists_positive_offdiag_paperDiscreteKernel
    (lam : BoundedWord m n)
    (hn : 2 ≤ n)
    (hRes : IsRestrictedWord lam) :
    ∃ u v : SnLambdaState lam, u ≠ v ∧
      0 < paperDiscreteKernel (m := m) (n := n) lam u v := by
  rcases canonical_nontrivial_of_restricted (m := m) (n := n) lam hn hRes with
    ⟨u, a, hneq, hlocalPos⟩
  let v : SnLambdaState lam := ⟨swapAt u.1 a, snLambda_closed_swap u.2 a⟩
  have huv : u ≠ v := by
    intro huvEq
    apply hneq
    exact congrArg Subtype.val huvEq
  have hedgePos :
      0 < Question3.edgeKernel (xNegIndex n) 1 u.1 v.1 a := by
    simpa [Question3.edgeKernel, v] using hlocalPos
  have hedgeLe :
      Question3.edgeKernel (xNegIndex n) 1 u.1 v.1 a
        ≤ Question3.transitionRate (xNegIndex n) 1 u.1 v.1 := by
    unfold Question3.transitionRate
    refine Finset.single_le_sum ?_ (by simp)
    intro b hb
    exact edgeKernel_nonneg_xNegIndex_one (m := m) (n := n) (w := u.1) (w' := v.1) b
  have hratePos :
      0 < Question3.transitionRate (xNegIndex n) 1 u.1 v.1 :=
    lt_of_lt_of_le hedgePos hedgeLe
  have hBpos :
      0 < paperUniformizationBound (m := m) (n := n) lam :=
    paperUniformizationBound_pos (m := m) (n := n) lam
  have hprobPos :
      0 < paperDiscreteKernel (m := m) (n := n) lam u v := by
    have hdivPos :
        0 < paperRate_restricted_qOne (m := m) (n := n) lam u v
          / paperUniformizationBound (m := m) (n := n) lam := by
      simpa [paperRate_restricted_qOne, transitionRateSn, v] using div_pos hratePos hBpos
    simpa [paperDiscreteKernel, huv, v] using hdivPos
  exact ⟨u, v, huv, hprobPos⟩

theorem question3_complete_restricted_qOne_discrete
    (lam : BoundedWord m n)
    (hn : 2 ≤ n)
    (hRes : IsRestrictedWord lam) :
    ∃ (mc : DiscreteMarkovChain (SnLambdaState lam))
      (pi : SnLambdaState lam → ℝ)
      (Fstar : BoundedWord m n → ℝ) (Pstar : ℝ),
      IsStationaryDist pi mc.prob
      ∧
      (∀ u : SnLambdaState lam,
        pi u =
          PiFromFstarPstar
            (FstarAtQ1ByDefinition Fstar)
            Pstar u.1)
      ∧
      (∃ u v : SnLambdaState lam, u ≠ v ∧ 0 < mc.prob u v)
      ∧
      (∀ u v : SnLambdaState lam,
        mc.prob u v = paperDiscreteKernel (m := m) (n := n) lam u v) := by
  let mc : DiscreteMarkovChain (SnLambdaState lam) := {
    prob := paperDiscreteKernel (m := m) (n := n) lam
    nonneg := paperDiscreteKernel_nonneg (m := m) (n := n) lam
    row_sum_one := paperDiscreteKernel_row_sum_one (m := m) (n := n) lam
  }
  refine ⟨mc,
    paperPi_restricted_qOne (m := m) (n := n) lam,
    paperFstar_restricted_qOne (m := m) (n := n) lam,
    paperPstar_restricted_qOne (m := m) (n := n) lam, ?_, ?_, ?_, ?_⟩
  · refine ⟨?_, ?_, ?_⟩
    · intro u
      simpa [mc, paperPi_restricted_qOne] using
        canonicalPi_nonneg (m := m) (n := n) lam u
    · simpa [mc, paperPi_restricted_qOne] using
        canonicalPi_sum_eq_one (m := m) (n := n) lam
    · intro y
      have hstat := paperDiscreteKernel_stationary (m := m) (n := n) lam hn hRes y
      calc
        (∑ x : SnLambdaState lam,
          paperPi_restricted_qOne (m := m) (n := n) lam x * mc.prob x y)
          = paperPi_restricted_qOne (m := m) (n := n) lam y := by
            simpa [mc] using hstat
        _ = paperPi_restricted_qOne (m := m) (n := n) lam y * (∑ z : SnLambdaState lam, mc.prob y z) := by
            rw [mc.row_sum_one y]
            ring
  · intro u
    exact paperPi_restricted_qOne_formula (m := m) (n := n) lam u
  · rcases exists_positive_offdiag_paperDiscreteKernel (m := m) (n := n) lam hn hRes with
      ⟨u, v, huv, hpos⟩
    exact ⟨u, v, huv, by simpa [mc] using hpos⟩
  · intro u v
    rfl

/--
Repository-final answer to Question 3 on restricted `λ` at `q=1`:
there exists an explicit nontrivial Markov chain on `S_n(λ)` with stationary
distribution `F^*/P^*`, and the transition rule is local/polynomial-free.
-/
theorem question3_complete_restricted_qOne
    (lam : BoundedWord m n)
    (hn : 2 ≤ n)
    (hRes : IsRestrictedWord lam) :
    ∃ (mc : ContinuousTimeMarkovChain (SnLambdaState lam))
      (pi : SnLambdaState lam → ℝ)
      (Fstar : BoundedWord m n → ℝ) (Pstar : ℝ),
      IsStationaryDist pi mc.rate
      ∧
      (∀ u : SnLambdaState lam,
        pi u =
          PiFromFstarPstar
            (FstarAtQ1ByDefinition Fstar)
            Pstar u.1)
      ∧
      (∃ w : SnLambdaState lam, ∃ a : AdjIndex n,
        w.1 ≠ swapAt w.1 a ∧ 0 < localRate (xNegIndex n) 1 w.1 a)
      ∧
      IsLocalAndPolynomialFree (lam := lam) (x := xNegIndex n) (t := 1) mc.rate := by
  have hFinal := paper_main_restricted_qOne_final (m := m) (n := n) lam hn hRes
  rcases hFinal with ⟨hStat, hRateNonneg, hPiNonneg, hPiSum, hNontriv, hFormula⟩
  let mc : ContinuousTimeMarkovChain (SnLambdaState lam) := {
    rate := paperRate_restricted_qOne (m := m) (n := n) lam
    nonneg := hRateNonneg
  }
  refine ⟨mc,
    paperPi_restricted_qOne (m := m) (n := n) lam,
    paperFstar_restricted_qOne (m := m) (n := n) lam,
    paperPstar_restricted_qOne (m := m) (n := n) lam, ?_, ?_, ?_, ?_⟩
  · refine ⟨?_, ?_, ?_⟩
    · intro u
      simpa [mc] using hPiNonneg u
    · simpa [mc] using hPiSum
    · intro y
      simpa [mc] using hStat y
  · intro u
    exact hFormula u
  · exact hNontriv
  · intro u v
    rfl

end FinalTheorem

end

end Bridge
end Macdonald
