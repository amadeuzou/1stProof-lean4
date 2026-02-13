import Mathlib.Algebra.BigOperators.Ring.Finset
import Mathlib.Algebra.Order.BigOperators.Group.Finset
import Mathlib.Data.Real.Basic
import Mathlib.Data.Fintype.BigOperators
import Mathlib.Order.Basic
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Ring

/-!
# Question 3: explicit local-swap construction (ASEP style)

This file replaces abstract exchange assumptions by an explicit local ratio model:

* spectral parameters `x : Fin n → ℝ`, parameter `t : ℝ`,
* adjacent swap dynamics on words,
* explicit ratio
  `ratio(i) = (t * x_i - x_{i+1}) / (x_i - t * x_{i+1})`,
* explicit local rates from the same numerator/denominator,
* detailed balance proved algebraically from these formulas.

To avoid formalizing full interpolation Macdonald theory, the semantic link
(`F^*`-weights are proportional to ASEP stationary weights) is encoded as a model
assumption in `ASEPWeightModel`.
-/

namespace Question3

open scoped BigOperators
noncomputable section

abbrev WordState (Species : Type*) (n : ℕ) := Fin n → Species
abbrev AdjIndex (n : ℕ) := { i : Fin n // i.1 + 1 < n }

def leftIndex {n : ℕ} (a : AdjIndex n) : Fin n := a.1

def rightIndex {n : ℕ} (a : AdjIndex n) : Fin n :=
  ⟨a.1.1 + 1, a.2⟩

def swapAt {Species : Type*} {n : ℕ}
    (w : WordState Species n) (a : AdjIndex n) :
    WordState Species n := fun i =>
  if i = leftIndex a then
    w (rightIndex a)
  else if i = rightIndex a then
    w (leftIndex a)
  else
    w i

lemma left_ne_right {n : ℕ} (a : AdjIndex n) :
    leftIndex a ≠ rightIndex a := by
  rcases a with ⟨i, hi⟩
  intro h
  exact (ne_of_lt (Nat.lt_succ_self i.1)) (congrArg Fin.val h)

@[simp] lemma swapAt_left {Species : Type*} {n : ℕ}
    (w : WordState Species n) (a : AdjIndex n) :
    swapAt w a (leftIndex a) = w (rightIndex a) := by
  simp [swapAt, leftIndex]

@[simp] lemma swapAt_right {Species : Type*} {n : ℕ}
    (w : WordState Species n) (a : AdjIndex n) :
    swapAt w a (rightIndex a) = w (leftIndex a) := by
  have hne : rightIndex a ≠ leftIndex a := by
    intro h
    exact left_ne_right a h.symm
  simp [swapAt, hne]

lemma swapAt_involutive {Species : Type*} {n : ℕ}
    (w : WordState Species n) (a : AdjIndex n) :
    swapAt (swapAt w a) a = w := by
  funext i
  by_cases hi : i = leftIndex a
  · subst hi
    simp
  · by_cases hj : i = rightIndex a
    · subst hj
      simp
    · simp [swapAt, hi, hj]

lemma swapAt_ne_of_diff {Species : Type*} {n : ℕ}
    (w : WordState Species n) (a : AdjIndex n)
    (hneq : w (leftIndex a) ≠ w (rightIndex a)) :
    swapAt w a ≠ w := by
  intro h
  have hleft : swapAt w a (leftIndex a) = w (leftIndex a) :=
    congrArg (fun f => f (leftIndex a)) h
  have heq : w (leftIndex a) = w (rightIndex a) := by
    simpa using hleft.symm
  exact hneq heq

lemma swapAt_eq_iff_rev {Species : Type*} {n : ℕ}
    (w w' : WordState Species n) (a : AdjIndex n) :
    swapAt w a = w' ↔ swapAt w' a = w := by
  constructor
  · intro h
    calc
      swapAt w' a = swapAt (swapAt w a) a := by simp [h]
      _ = w := swapAt_involutive w a
  · intro h
    calc
      swapAt w a = swapAt (swapAt w' a) a := by simp [h]
      _ = w' := swapAt_involutive w' a

section ExplicitRates

variable {Species : Type*} [LinearOrder Species]
variable {n : ℕ}

def ratePlus (x : Fin n → ℝ) (t : ℝ) (a : AdjIndex n) : ℝ :=
  t * x (leftIndex a) - x (rightIndex a)

def rateMinus (x : Fin n → ℝ) (t : ℝ) (a : AdjIndex n) : ℝ :=
  x (leftIndex a) - t * x (rightIndex a)

def ratio (x : Fin n → ℝ) (t : ℝ) (a : AdjIndex n) : ℝ :=
  ratePlus x t a / rateMinus x t a

def localRate (x : Fin n → ℝ) (t : ℝ)
    (w : WordState Species n) (a : AdjIndex n) : ℝ :=
  if w (leftIndex a) > w (rightIndex a) then
    ratePlus x t a
  else if w (leftIndex a) < w (rightIndex a) then
    rateMinus x t a
  else
    0

@[simp] lemma localRate_of_gt (x : Fin n → ℝ) (t : ℝ)
    (w : WordState Species n) (a : AdjIndex n)
    (hgt : w (leftIndex a) > w (rightIndex a)) :
    localRate x t w a = ratePlus x t a := by
  simp [localRate, hgt]

@[simp] lemma localRate_of_lt (x : Fin n → ℝ) (t : ℝ)
    (w : WordState Species n) (a : AdjIndex n)
    (hlt : w (leftIndex a) < w (rightIndex a)) :
    localRate x t w a = rateMinus x t a := by
  have hnot : ¬ w (leftIndex a) > w (rightIndex a) := not_lt_of_ge (le_of_lt hlt)
  simp [localRate, hnot, hlt]

@[simp] lemma localRate_of_eq (x : Fin n → ℝ) (t : ℝ)
    (w : WordState Species n) (a : AdjIndex n)
    (heq : w (leftIndex a) = w (rightIndex a)) :
    localRate x t w a = 0 := by
  have hnotgt : ¬ w (leftIndex a) > w (rightIndex a) := by simp [heq]
  have hnotlt : ¬ w (leftIndex a) < w (rightIndex a) := by simp [heq]
  simp [localRate, hnotgt, hnotlt]

@[simp] lemma localRate_swap_of_gt (x : Fin n → ℝ) (t : ℝ)
    (w : WordState Species n) (a : AdjIndex n)
    (hgt : w (leftIndex a) > w (rightIndex a)) :
    localRate x t (swapAt w a) a = rateMinus x t a := by
  have hlt' : (swapAt w a) (leftIndex a) < (swapAt w a) (rightIndex a) := by
    simpa using hgt
  exact localRate_of_lt x t (swapAt w a) a hlt'

@[simp] lemma localRate_swap_of_lt (x : Fin n → ℝ) (t : ℝ)
    (w : WordState Species n) (a : AdjIndex n)
    (hlt : w (leftIndex a) < w (rightIndex a)) :
    localRate x t (swapAt w a) a = ratePlus x t a := by
  have hgt' : (swapAt w a) (leftIndex a) > (swapAt w a) (rightIndex a) := by
    simpa using hlt
  exact localRate_of_gt x t (swapAt w a) a hgt'

def DenomNonzero (x : Fin n → ℝ) (t : ℝ) : Prop :=
  ∀ a : AdjIndex n, rateMinus x t a ≠ 0

lemma ratePlus_eq_rateMinus_one (x : Fin n → ℝ) (a : AdjIndex n) :
    ratePlus x 1 a = rateMinus x 1 a := by
  simp [ratePlus, rateMinus]

lemma ratio_one_of_t_one
    (x : Fin n → ℝ) (a : AdjIndex n)
    (hden : DenomNonzero x 1) :
    ratio x 1 a = 1 := by
  have hz : rateMinus x 1 a ≠ 0 := hden a
  calc
    ratio x 1 a = rateMinus x 1 a / rateMinus x 1 a := by
      simp [ratio, ratePlus_eq_rateMinus_one (x := x) (a := a)]
    _ = 1 := div_self hz

def WeightExchange
    (weight : WordState Species n → ℝ)
    (x : Fin n → ℝ) (t : ℝ) : Prop :=
  ∀ w a, w (leftIndex a) > w (rightIndex a) →
    weight (swapAt w a) = ratio x t a * weight w

lemma ratio_mul_rateMinus (x : Fin n → ℝ) (t : ℝ) (a : AdjIndex n)
    (hden : DenomNonzero x t) :
    ratio x t a * rateMinus x t a = ratePlus x t a := by
  have hz : rateMinus x t a ≠ 0 := hden a
  unfold ratio
  field_simp [hz]

theorem local_detailed_of_gt
    (weight : WordState Species n → ℝ)
    (x : Fin n → ℝ) (t : ℝ)
    (hEx : WeightExchange weight x t)
    (hden : DenomNonzero x t)
    {w : WordState Species n} {a : AdjIndex n}
    (hgt : w (leftIndex a) > w (rightIndex a)) :
    weight w * localRate x t w a =
      weight (swapAt w a) * localRate x t (swapAt w a) a := by
  calc
    weight w * localRate x t w a = weight w * ratePlus x t a := by
      simp [localRate_of_gt, hgt]
    _ = weight w * (ratio x t a * rateMinus x t a) := by
      rw [(ratio_mul_rateMinus x t a hden).symm]
    _ = (weight w * ratio x t a) * rateMinus x t a := by
      rw [mul_assoc]
    _ = (ratio x t a * weight w) * rateMinus x t a := by
      rw [mul_comm (weight w) (ratio x t a)]
    _ = weight (swapAt w a) * rateMinus x t a := by
      rw [hEx w a hgt]
    _ = weight (swapAt w a) * localRate x t (swapAt w a) a := by
      simp [hgt]

theorem local_detailed
    (weight : WordState Species n → ℝ)
    (x : Fin n → ℝ) (t : ℝ)
    (hEx : WeightExchange weight x t)
    (hden : DenomNonzero x t)
    (w : WordState Species n) (a : AdjIndex n) :
    weight w * localRate x t w a =
      weight (swapAt w a) * localRate x t (swapAt w a) a := by
  rcases lt_trichotomy (w (leftIndex a)) (w (rightIndex a)) with hlt | heq | hgt
  · have hgt' : (swapAt w a) (leftIndex a) > (swapAt w a) (rightIndex a) := by
      simpa using hlt
    have h :=
      local_detailed_of_gt weight x t hEx hden (w := swapAt w a) (a := a) hgt'
    simpa [swapAt_involutive] using h.symm
  · simp [localRate_of_eq, heq]
  · exact local_detailed_of_gt weight x t hEx hden hgt

def edgeKernel
    (x : Fin n → ℝ) (t : ℝ)
    (w w' : WordState Species n) (a : AdjIndex n) : ℝ :=
  if swapAt w a = w' then localRate x t w a else 0

def transitionRate
    (x : Fin n → ℝ) (t : ℝ)
    (w w' : WordState Species n) : ℝ :=
  ∑ a : AdjIndex n, edgeKernel x t w w' a

lemma edgeKernel_detailed
    (weight : WordState Species n → ℝ)
    (x : Fin n → ℝ) (t : ℝ)
    (hEx : WeightExchange weight x t)
    (hden : DenomNonzero x t)
    (w w' : WordState Species n) (a : AdjIndex n) :
    weight w * edgeKernel x t w w' a =
      weight w' * edgeKernel x t w' w a := by
  by_cases hww' : swapAt w a = w'
  · have hrev : swapAt w' a = w := (swapAt_eq_iff_rev w w' a).1 hww'
    have hlocal := local_detailed weight x t hEx hden w a
    have hlocal' :
        weight w * localRate x t w a =
          weight w' * localRate x t w' a := by
      simpa [hww'] using hlocal
    simpa [edgeKernel, hww', hrev] using hlocal'
  · have hrev : ¬ swapAt w' a = w := by
      intro hrev
      exact hww' ((swapAt_eq_iff_rev w w' a).2 hrev)
    simp [edgeKernel, hww', hrev]

theorem detailed_balance_explicit
    (weight : WordState Species n → ℝ)
    (x : Fin n → ℝ) (t : ℝ)
    (hEx : WeightExchange weight x t)
    (hden : DenomNonzero x t) :
    ∀ w w',
      weight w * transitionRate x t w w' =
      weight w' * transitionRate x t w' w := by
  intro w w'
  calc
    weight w * transitionRate x t w w' =
      ∑ a : AdjIndex n, weight w * edgeKernel x t w w' a := by
        simp [transitionRate, Finset.mul_sum]
    _ = ∑ a : AdjIndex n, weight w' * edgeKernel x t w' w a := by
        refine Finset.sum_congr rfl ?_
        intro a ha
        exact edgeKernel_detailed weight x t hEx hden w w' a
    _ = weight w' * transitionRate x t w' w := by
        simp [transitionRate, Finset.mul_sum]

theorem globalBalance_of_detailedBalance
    {State : Type*} [Fintype State]
    (weight : State → ℝ) (rate : State → State → ℝ)
    (hdb : ∀ x y, weight x * rate x y = weight y * rate y x) :
    ∀ y, (∑ x, weight x * rate x y) = weight y * (∑ z, rate y z) := by
  intro y
  calc
    ∑ x, weight x * rate x y = ∑ x, weight y * rate y x := by
      refine Finset.sum_congr rfl ?_
      intro x hx
      simpa [mul_assoc, mul_comm, mul_left_comm] using hdb x y
    _ = weight y * ∑ z, rate y z := by
      simpa using
        (Finset.mul_sum (s := (Finset.univ : Finset State))
          (f := fun z => rate y z) (a := weight y)).symm

theorem stationary_global_balance_explicit
    [Fintype Species]
    (weight : WordState Species n → ℝ)
    (x : Fin n → ℝ) (t : ℝ)
    (hEx : WeightExchange weight x t)
    (hden : DenomNonzero x t) :
    ∀ y,
      (∑ w, weight w * transitionRate x t w y) =
      weight y * (∑ z, transitionRate x t y z) := by
  exact globalBalance_of_detailedBalance
    (weight := weight) (rate := transitionRate x t)
    (detailed_balance_explicit weight x t hEx hden)

theorem nontrivial_local
    (x : Fin n → ℝ) (t : ℝ)
    (hpos : ∀ a : AdjIndex n, 0 < ratePlus x t a)
    (hInv : ∃ w : WordState Species n, ∃ a : AdjIndex n,
      w (leftIndex a) > w (rightIndex a)) :
    ∃ w : WordState Species n, ∃ a : AdjIndex n,
      w ≠ swapAt w a ∧ 0 < localRate x t w a := by
  rcases hInv with ⟨w, a, hgt⟩
  refine ⟨w, a, ?_, ?_⟩
  · exact (swapAt_ne_of_diff w a (ne_of_gt hgt)).symm
  · simpa [localRate_of_gt, hgt] using hpos a

def RatePairNonneg (x : Fin n → ℝ) (t : ℝ) : Prop :=
  ∀ a : AdjIndex n, 0 ≤ ratePlus x t a ∧ 0 ≤ rateMinus x t a

lemma localRate_nonneg_of_ratePairNonneg
    (x : Fin n → ℝ) (t : ℝ)
    (hNonneg : RatePairNonneg x t)
    (w : WordState Species n) (a : AdjIndex n) :
    0 ≤ localRate x t w a := by
  rcases lt_trichotomy (w (leftIndex a)) (w (rightIndex a)) with hlt | heq | hgt
  · exact (localRate_of_lt (x := x) (t := t) (w := w) (a := a) hlt).symm ▸ (hNonneg a).2
  · exact (localRate_of_eq (x := x) (t := t) (w := w) (a := a) heq).symm ▸ le_rfl
  · exact (localRate_of_gt (x := x) (t := t) (w := w) (a := a) hgt).symm ▸ (hNonneg a).1

lemma edgeKernel_nonneg_of_ratePairNonneg
    (x : Fin n → ℝ) (t : ℝ)
    (hNonneg : RatePairNonneg x t)
    (w w' : WordState Species n) (a : AdjIndex n) :
    0 ≤ edgeKernel x t w w' a := by
  by_cases hSwap : swapAt w a = w'
  · simp [edgeKernel, hSwap, localRate_nonneg_of_ratePairNonneg (x := x) (t := t) hNonneg w a]
  · simp [edgeKernel, hSwap]

lemma transitionRate_nonneg_of_ratePairNonneg
    (x : Fin n → ℝ) (t : ℝ)
    (hNonneg : RatePairNonneg x t)
    (w w' : WordState Species n) :
    0 ≤ transitionRate x t w w' := by
  unfold transitionRate
  refine Finset.sum_nonneg ?_
  intro a ha
  exact edgeKernel_nonneg_of_ratePairNonneg (x := x) (t := t) hNonneg w w' a

end ExplicitRates

section SemanticLink

variable {Species : Type*} [LinearOrder Species] [Fintype Species]
variable {n : ℕ}

def ASEPWeightModel
    (FstarWeight modelWeight : WordState Species n → ℝ) : Prop :=
  ∃ c : ℝ, c ≠ 0 ∧ ∀ w, FstarWeight w = c * modelWeight w

theorem global_balance_of_scaled_model
    (FstarWeight modelWeight : WordState Species n → ℝ)
    (x : Fin n → ℝ) (t : ℝ)
    (hModel : ASEPWeightModel FstarWeight modelWeight)
    (hGB : ∀ y,
      (∑ w, modelWeight w * transitionRate x t w y) =
      modelWeight y * (∑ z, transitionRate x t y z)) :
    ∀ y,
      (∑ w, FstarWeight w * transitionRate x t w y) =
      FstarWeight y * (∑ z, transitionRate x t y z) := by
  rcases hModel with ⟨c, _hc, hscale⟩
  intro y
  calc
    ∑ w, FstarWeight w * transitionRate x t w y =
      ∑ w, (c * modelWeight w) * transitionRate x t w y := by
        refine Finset.sum_congr rfl ?_
        intro w hw
        simp [hscale]
    _ = ∑ w, c * (modelWeight w * transitionRate x t w y) := by
        refine Finset.sum_congr rfl ?_
        intro w hw
        rw [mul_assoc]
    _ = c * ∑ w, modelWeight w * transitionRate x t w y := by
        simpa using (Finset.mul_sum (s := (Finset.univ : Finset (WordState Species n)))
          (f := fun w => modelWeight w * transitionRate x t w y) (a := c)).symm
    _ = c * (modelWeight y * (∑ z, transitionRate x t y z)) := by
        rw [hGB y]
    _ = (c * modelWeight y) * (∑ z, transitionRate x t y z) := by
        rw [mul_assoc]
    _ = FstarWeight y * (∑ z, transitionRate x t y z) := by
        rw [hscale]

theorem global_balance_normalized
    {State : Type*} [Fintype State]
    (weight : State → ℝ) (rate : State → State → ℝ) (Pstar : ℝ)
    (hGB : ∀ y,
      (∑ x, weight x * rate x y) =
      weight y * (∑ z, rate y z)) :
    ∀ y,
      (∑ x, (weight x / Pstar) * rate x y) =
      (weight y / Pstar) * (∑ z, rate y z) := by
  intro y
  calc
    ∑ x, (weight x / Pstar) * rate x y
      = ∑ x, ((Pstar⁻¹ * weight x) * rate x y) := by
          simp [div_eq_mul_inv, mul_left_comm, mul_comm]
    _ = Pstar⁻¹ * (∑ x, weight x * rate x y) := by
          simp [Finset.mul_sum, mul_assoc, mul_left_comm, mul_comm]
    _ = Pstar⁻¹ * (weight y * (∑ z, rate y z)) := by
          rw [hGB y]
    _ = (weight y / Pstar) * (∑ z, rate y z) := by
          rw [← mul_assoc, mul_comm Pstar⁻¹ (weight y)]
          simp [div_eq_mul_inv]

end SemanticLink

section DefinitionalCompletion

variable {Species : Type*} [LinearOrder Species] [Fintype Species]
variable {n : ℕ}

def FstarAtQ1ByDefinition
    (asepWeight : WordState Species n → ℝ) :
    WordState Species n → ℝ := asepWeight

def PiFromFstarPstar
    (FstarWeight : WordState Species n → ℝ) (Pstar : ℝ) :
    WordState Species n → ℝ := fun w => FstarWeight w / Pstar

/--
External-literature bridge proposition:
at `q = 1`, the interpolation `F^*`-weight satisfies the local exchange relation.
-/
def FstarWeightExchangeQ1
    (FstarWeight : WordState Species n → ℝ)
    (x : Fin n → ℝ) (t : ℝ) : Prop :=
  WeightExchange FstarWeight x t

omit [Fintype Species] in
/--
Bridge interface theorem (hypothesis-driven, no new constant assumption introduced in this file).
-/
theorem fstar_weight_exchange_q1
    (FstarWeight : WordState Species n → ℝ)
    (x : Fin n → ℝ) (t : ℝ)
    (hBridge : FstarWeightExchangeQ1 FstarWeight x t) :
    WeightExchange FstarWeight x t := hBridge

theorem question3_stationary_definitional
    (asepWeight : WordState Species n → ℝ)
    (x : Fin n → ℝ) (t : ℝ) (Pstar : ℝ)
    (hEx : WeightExchange asepWeight x t)
    (hden : DenomNonzero x t) :
    ∀ y,
      (∑ w, PiFromFstarPstar (FstarAtQ1ByDefinition asepWeight) Pstar w *
        transitionRate x t w y)
        =
      PiFromFstarPstar (FstarAtQ1ByDefinition asepWeight) Pstar y *
        (∑ z, transitionRate x t y z) := by
  intro y
  have hGB :
      ∀ y,
        (∑ w, asepWeight w * transitionRate x t w y) =
        asepWeight y * (∑ z, transitionRate x t y z) :=
    stationary_global_balance_explicit
      (weight := asepWeight) (x := x) (t := t) hEx hden
  simpa [PiFromFstarPstar, FstarAtQ1ByDefinition] using
    global_balance_normalized
      (weight := asepWeight) (rate := transitionRate x t)
      (Pstar := Pstar) hGB y

theorem question3_stationary_via_fstar_bridge
    (FstarWeight : WordState Species n → ℝ)
    (x : Fin n → ℝ) (t : ℝ) (Pstar : ℝ)
    (hBridge : FstarWeightExchangeQ1 FstarWeight x t)
    (hden : DenomNonzero x t) :
    ∀ y,
      (∑ w, PiFromFstarPstar (FstarAtQ1ByDefinition FstarWeight) Pstar w *
        transitionRate x t w y)
        =
      PiFromFstarPstar (FstarAtQ1ByDefinition FstarWeight) Pstar y *
        (∑ z, transitionRate x t y z) := by
  exact question3_stationary_definitional
    (asepWeight := FstarWeight) (x := x) (t := t) (Pstar := Pstar)
    (fstar_weight_exchange_q1 (FstarWeight := FstarWeight) (x := x) (t := t) hBridge)
    hden

omit [Fintype Species] in
theorem question3_nontrivial_definitional
    (_asepWeight : WordState Species n → ℝ)
    (x : Fin n → ℝ) (t : ℝ)
    (hpos : ∀ a : AdjIndex n, 0 < ratePlus x t a)
    (hInv : ∃ w : WordState Species n, ∃ a : AdjIndex n,
      w (leftIndex a) > w (rightIndex a)) :
    ∃ w : WordState Species n, ∃ a : AdjIndex n,
      w ≠ swapAt w a ∧ 0 < localRate x t w a := by
  exact nontrivial_local (x := x) (t := t) hpos hInv

theorem question3_full_definitional
    (asepWeight : WordState Species n → ℝ)
    (x : Fin n → ℝ) (t : ℝ) (Pstar : ℝ)
    (hEx : WeightExchange asepWeight x t)
    (hden : DenomNonzero x t)
    (hpos : ∀ a : AdjIndex n, 0 < ratePlus x t a)
    (hInv : ∃ w : WordState Species n, ∃ a : AdjIndex n,
      w (leftIndex a) > w (rightIndex a)) :
    (∀ y,
      (∑ w, PiFromFstarPstar (FstarAtQ1ByDefinition asepWeight) Pstar w *
        transitionRate x t w y)
        =
      PiFromFstarPstar (FstarAtQ1ByDefinition asepWeight) Pstar y *
        (∑ z, transitionRate x t y z))
    ∧
    (∃ w : WordState Species n, ∃ a : AdjIndex n,
      w ≠ swapAt w a ∧ 0 < localRate x t w a) := by
  constructor
  · exact question3_stationary_definitional
      (asepWeight := asepWeight) (x := x) (t := t)
      (Pstar := Pstar) hEx hden
  · exact question3_nontrivial_definitional
      (_asepWeight := asepWeight) (x := x) (t := t) hpos hInv

theorem question3_full_via_fstar_bridge
    (FstarWeight : WordState Species n → ℝ)
    (x : Fin n → ℝ) (t : ℝ) (Pstar : ℝ)
    (hBridge : FstarWeightExchangeQ1 FstarWeight x t)
    (hden : DenomNonzero x t)
    (hpos : ∀ a : AdjIndex n, 0 < ratePlus x t a)
    (hInv : ∃ w : WordState Species n, ∃ a : AdjIndex n,
      w (leftIndex a) > w (rightIndex a)) :
    (∀ y,
      (∑ w, PiFromFstarPstar (FstarAtQ1ByDefinition FstarWeight) Pstar w *
        transitionRate x t w y)
        =
      PiFromFstarPstar (FstarAtQ1ByDefinition FstarWeight) Pstar y *
        (∑ z, transitionRate x t y z))
    ∧
    (∃ w : WordState Species n, ∃ a : AdjIndex n,
      w ≠ swapAt w a ∧ 0 < localRate x t w a) := by
  exact question3_full_definitional
    (asepWeight := FstarWeight) (x := x) (t := t) (Pstar := Pstar)
    (fstar_weight_exchange_q1 (FstarWeight := FstarWeight) (x := x) (t := t) hBridge)
    hden hpos hInv

omit [Fintype Species] in
theorem weightExchange_const_one_t_one
    (x : Fin n → ℝ)
    (hden : DenomNonzero x 1) :
    WeightExchange (Species := Species) (fun _ : WordState Species n => (1 : ℝ)) x 1 := by
  intro w a _hgt
  simp [ratio_one_of_t_one (x := x) (a := a) hden]

theorem question3_full_t_one_const_weight
    (x : Fin n → ℝ) (Pstar : ℝ)
    (hden : DenomNonzero x 1)
    (hpos : ∀ a : AdjIndex n, 0 < ratePlus x 1 a)
    (hInv : ∃ w : WordState Species n, ∃ a : AdjIndex n,
      w (leftIndex a) > w (rightIndex a)) :
    (∀ y,
      (∑ w, PiFromFstarPstar
        (FstarAtQ1ByDefinition (fun _ : WordState Species n => (1 : ℝ)))
        Pstar w * transitionRate x 1 w y)
        =
      PiFromFstarPstar
        (FstarAtQ1ByDefinition (fun _ : WordState Species n => (1 : ℝ)))
        Pstar y * (∑ z, transitionRate x 1 y z))
    ∧
    (∃ w : WordState Species n, ∃ a : AdjIndex n,
      w ≠ swapAt w a ∧ 0 < localRate x 1 w a) := by
  exact question3_full_definitional
    (asepWeight := fun _ : WordState Species n => (1 : ℝ))
    (x := x) (t := 1) (Pstar := Pstar)
    (weightExchange_const_one_t_one (Species := Species) (x := x) hden)
    hden hpos hInv

def adjIndexZeroTwo : AdjIndex 2 := ⟨⟨0, by decide⟩, by decide⟩

lemma adjIndex_eq_zero_two (a : AdjIndex 2) :
    a = adjIndexZeroTwo := by
  apply Subtype.ext
  apply Fin.ext
  have hle : a.1.1 + 1 ≤ 1 := Nat.lt_succ_iff.mp a.2
  have hs : Nat.succ a.1.1 ≤ 1 := by
    simpa [Nat.succ_eq_add_one] using hle
  exact (Nat.lt_one_iff.mp (Nat.succ_le_iff.mp hs))

def twoSiteWeight (x : Fin 2 → ℝ) (t : ℝ) :
    WordState Species 2 → ℝ := fun w =>
  if w (leftIndex adjIndexZeroTwo) > w (rightIndex adjIndexZeroTwo) then
    1
  else
    ratio x t adjIndexZeroTwo

omit [Fintype Species] in
theorem weightExchange_twoSite
    (x : Fin 2 → ℝ) (t : ℝ) :
    WeightExchange (Species := Species) (twoSiteWeight (Species := Species) x t) x t := by
  intro w a hgt
  have ha : a = adjIndexZeroTwo := adjIndex_eq_zero_two a
  subst ha
  have hnot : ¬ w (rightIndex adjIndexZeroTwo) > w (leftIndex adjIndexZeroTwo) :=
    not_lt_of_ge (le_of_lt hgt)
  simp [twoSiteWeight, hgt, hnot]

theorem question3_full_twoSite_explicit
    (x : Fin 2 → ℝ) (t : ℝ) (Pstar : ℝ)
    (hden : DenomNonzero x t)
    (hpos : ∀ a : AdjIndex 2, 0 < ratePlus x t a)
    (hInv : ∃ w : WordState Species 2, ∃ a : AdjIndex 2,
      w (leftIndex a) > w (rightIndex a)) :
    (∀ y : WordState Species 2,
      (∑ w, PiFromFstarPstar
        (FstarAtQ1ByDefinition (twoSiteWeight (Species := Species) x t))
        Pstar w * transitionRate x t w y)
        =
      PiFromFstarPstar
        (FstarAtQ1ByDefinition (twoSiteWeight (Species := Species) x t))
        Pstar y * (∑ z, transitionRate x t y z))
    ∧
    (∃ w : WordState Species 2, ∃ a : AdjIndex 2,
      w ≠ swapAt w a ∧ 0 < localRate x t w a) := by
  exact question3_full_definitional
    (asepWeight := twoSiteWeight (Species := Species) x t)
    (x := x) (t := t) (Pstar := Pstar)
    (weightExchange_twoSite (Species := Species) (x := x) (t := t))
    hden hpos hInv

end DefinitionalCompletion

end

end Question3
