import Question3
import Macdonald.Nonsymmetric.E

namespace Macdonald
namespace Bridge

open Question3
open Nonsymmetric
open Conventions
open scoped BigOperators

noncomputable section

abbrev BoundedWord (m n : ℕ) := Question3.WordState (Fin m) n

def toComposition {m n : ℕ} (w : BoundedWord m n) : Conventions.Composition n :=
  fun i => (w i).1

@[simp] lemma toComposition_apply {m n : ℕ} (w : BoundedWord m n) (i : Fin n) :
    toComposition w i = (w i).1 := rfl

@[simp] lemma toComposition_swapAt {m n : ℕ}
    (w : BoundedWord m n) (a : Question3.AdjIndex n) :
    toComposition (Question3.swapAt w a) =
      Nonsymmetric.swapComposition (toComposition w) a.1 a.2 := by
  funext i
  simp [toComposition, Question3.swapAt, Nonsymmetric.swapComposition,
    Nonsymmetric.nextIndex, Question3.leftIndex, Question3.rightIndex]
  split_ifs <;> rfl

/--
Real-valued `q = 1` local exchange relation on compositions, matching
the explicit local ratio used in `Question3`.
-/
def CompositionExchangeReal
    {n : ℕ}
    (weight : Conventions.Composition n → ℝ)
    (x : Fin n → ℝ) (t : ℝ) : Prop :=
  ∀ μ (i : Fin n) (h : i.1 + 1 < n), μ i > μ (Nonsymmetric.nextIndex i h) →
    weight (Nonsymmetric.swapComposition μ i h) =
      Question3.ratio x t ⟨i, h⟩ * weight μ

theorem weightExchange_bounded_of_compositionExchange
    {m n : ℕ}
    (weight : Conventions.Composition n → ℝ)
    (x : Fin n → ℝ) (t : ℝ)
    (hEx : CompositionExchangeReal weight x t) :
    Question3.WeightExchange
      (Species := Fin m)
      (fun w : BoundedWord m n => weight (toComposition w)) x t := by
  intro w a hgt
  have hgtNat :
      toComposition w a.1 > toComposition w (Nonsymmetric.nextIndex a.1 a.2) := by
    simpa [toComposition, Nonsymmetric.nextIndex, Question3.leftIndex, Question3.rightIndex] using hgt
  have hSwap := hEx (toComposition w) a.1 a.2 hgtNat
  simpa [toComposition_swapAt, Question3.ratio] using hSwap

theorem stationary_on_bounded_words_of_compositionExchange
    {m n : ℕ}
    (weight : Conventions.Composition n → ℝ)
    (x : Fin n → ℝ) (t : ℝ) (Pstar : ℝ)
    (hEx : CompositionExchangeReal weight x t)
    (hden : Question3.DenomNonzero x t) :
    ∀ y : BoundedWord m n,
      (∑ w, (weight (toComposition w) / Pstar) * Question3.transitionRate x t w y) =
      (weight (toComposition y) / Pstar) * (∑ z, Question3.transitionRate x t y z) := by
  have hWE :
      Question3.WeightExchange
        (Species := Fin m)
        (fun w : BoundedWord m n => weight (toComposition w)) x t :=
    weightExchange_bounded_of_compositionExchange
      (weight := weight) (x := x) (t := t) hEx
  have hGB :
      ∀ y : BoundedWord m n,
        (∑ w, weight (toComposition w) * Question3.transitionRate x t w y) =
        weight (toComposition y) * (∑ z, Question3.transitionRate x t y z) :=
    Question3.stationary_global_balance_explicit
      (Species := Fin m)
      (weight := fun w : BoundedWord m n => weight (toComposition w))
      (x := x) (t := t) hWE hden
  intro y
  simpa using
    Question3.global_balance_normalized
      (weight := fun w : BoundedWord m n => weight (toComposition w))
      (rate := Question3.transitionRate x t)
      (Pstar := Pstar) hGB y

theorem exists_inversion_boundedWord
    {m n : ℕ}
    (hm : 2 ≤ m) (hn : 2 ≤ n) :
    ∃ w : BoundedWord m n, ∃ a : Question3.AdjIndex n,
      w (Question3.leftIndex a) > w (Question3.rightIndex a) := by
  have hm0 : 0 < m := lt_of_lt_of_le (by decide : 0 < 2) hm
  have hm1 : 1 < m := lt_of_lt_of_le (by decide : 1 < 2) hm
  have hn0 : 0 < n := lt_of_lt_of_le (by decide : 0 < 2) hn
  have hn1 : 1 < n := lt_of_lt_of_le (by decide : 1 < 2) hn
  let zeroN : Fin n := ⟨0, hn0⟩
  let zeroM : Fin m := ⟨0, hm0⟩
  let oneM : Fin m := ⟨1, hm1⟩
  let a : Question3.AdjIndex n := ⟨zeroN, by simpa [zeroN] using hn1⟩
  let w : BoundedWord m n := fun i => if i = zeroN then oneM else zeroM
  refine ⟨w, a, ?_⟩
  have hne : Question3.rightIndex a ≠ zeroN := by
    intro h
    exact Question3.left_ne_right a (by simpa [Question3.leftIndex, a] using h.symm)
  have hleft : w (Question3.leftIndex a) = oneM := by
    simp [w, a, zeroN, Question3.leftIndex]
  have hright : w (Question3.rightIndex a) = zeroM := by
    simp [w, a, zeroN, hne]
  rw [hleft, hright]
  change (1 : ℕ) > 0
  decide

theorem question3_full_on_bounded_words_of_compositionExchange
    {m n : ℕ}
    (weight : Conventions.Composition n → ℝ)
    (x : Fin n → ℝ) (t : ℝ) (Pstar : ℝ)
    (hEx : CompositionExchangeReal weight x t)
    (hden : Question3.DenomNonzero x t)
    (hpos : ∀ a : Question3.AdjIndex n, 0 < Question3.ratePlus x t a)
    (hInv : ∃ w : BoundedWord m n, ∃ a : Question3.AdjIndex n,
      w (Question3.leftIndex a) > w (Question3.rightIndex a)) :
    (∀ y : BoundedWord m n,
      (∑ w, Question3.PiFromFstarPstar
        (Question3.FstarAtQ1ByDefinition
          (fun u : BoundedWord m n => weight (toComposition u))) Pstar w
          * Question3.transitionRate x t w y)
        =
      Question3.PiFromFstarPstar
        (Question3.FstarAtQ1ByDefinition
          (fun u : BoundedWord m n => weight (toComposition u))) Pstar y
        * (∑ z, Question3.transitionRate x t y z))
    ∧
    (∃ w : BoundedWord m n, ∃ a : Question3.AdjIndex n,
      w ≠ Question3.swapAt w a ∧ 0 < Question3.localRate x t w a) := by
  have hWE :
      Question3.WeightExchange
        (Species := Fin m)
        (fun w : BoundedWord m n => weight (toComposition w)) x t :=
    weightExchange_bounded_of_compositionExchange
      (weight := weight) (x := x) (t := t) hEx
  exact Question3.question3_full_definitional
    (Species := Fin m)
    (asepWeight := fun w : BoundedWord m n => weight (toComposition w))
    (x := x) (t := t) (Pstar := Pstar)
    hWE hden hpos hInv

theorem question3_full_on_bounded_words_of_compositionExchange_auto
    {m n : ℕ}
    (weight : Conventions.Composition n → ℝ)
    (x : Fin n → ℝ) (t : ℝ) (Pstar : ℝ)
    (hm : 2 ≤ m) (hn : 2 ≤ n)
    (hEx : CompositionExchangeReal weight x t)
    (hden : Question3.DenomNonzero x t)
    (hpos : ∀ a : Question3.AdjIndex n, 0 < Question3.ratePlus x t a) :
    (∀ y : BoundedWord m n,
      (∑ w, Question3.PiFromFstarPstar
        (Question3.FstarAtQ1ByDefinition
          (fun u : BoundedWord m n => weight (toComposition u))) Pstar w
          * Question3.transitionRate x t w y)
        =
      Question3.PiFromFstarPstar
        (Question3.FstarAtQ1ByDefinition
          (fun u : BoundedWord m n => weight (toComposition u))) Pstar y
        * (∑ z, Question3.transitionRate x t y z))
    ∧
    (∃ w : BoundedWord m n, ∃ a : Question3.AdjIndex n,
      w ≠ Question3.swapAt w a ∧ 0 < Question3.localRate x t w a) := by
  exact question3_full_on_bounded_words_of_compositionExchange
    (weight := weight) (x := x) (t := t) (Pstar := Pstar)
    hEx hden hpos (exists_inversion_boundedWord (m := m) (n := n) hm hn)

theorem question3_full_on_bounded_words_t_one_const_weight_auto
    {m n : ℕ}
    (x : Fin n → ℝ) (Pstar : ℝ)
    (hm : 2 ≤ m) (hn : 2 ≤ n)
    (hden : Question3.DenomNonzero x 1)
    (hpos : ∀ a : Question3.AdjIndex n, 0 < Question3.ratePlus x 1 a) :
    (∀ y : BoundedWord m n,
      (∑ w, Question3.PiFromFstarPstar
        (Question3.FstarAtQ1ByDefinition
          (fun _ : BoundedWord m n => (1 : ℝ))) Pstar w
          * Question3.transitionRate x 1 w y)
        =
      Question3.PiFromFstarPstar
        (Question3.FstarAtQ1ByDefinition
          (fun _ : BoundedWord m n => (1 : ℝ))) Pstar y
        * (∑ z, Question3.transitionRate x 1 y z))
    ∧
    (∃ w : BoundedWord m n, ∃ a : Question3.AdjIndex n,
      w ≠ Question3.swapAt w a ∧ 0 < Question3.localRate x 1 w a) := by
  exact Question3.question3_full_t_one_const_weight
    (Species := Fin m) (x := x) (Pstar := Pstar)
    hden hpos (exists_inversion_boundedWord (m := m) (n := n) hm hn)

theorem question3_full_on_bounded_words_twoSite_explicit_auto
    {m : ℕ}
    (x : Fin 2 → ℝ) (t : ℝ) (Pstar : ℝ)
    (hm : 2 ≤ m)
    (hden : Question3.DenomNonzero x t)
    (hpos : ∀ a : Question3.AdjIndex 2, 0 < Question3.ratePlus x t a) :
    (∀ y : BoundedWord m 2,
      (∑ w, Question3.PiFromFstarPstar
        (Question3.FstarAtQ1ByDefinition
          (Question3.twoSiteWeight (Species := Fin m) x t))
        Pstar w * Question3.transitionRate x t w y)
        =
      Question3.PiFromFstarPstar
        (Question3.FstarAtQ1ByDefinition
          (Question3.twoSiteWeight (Species := Fin m) x t))
        Pstar y * (∑ z, Question3.transitionRate x t y z))
    ∧
    (∃ w : BoundedWord m 2, ∃ a : Question3.AdjIndex 2,
      w ≠ Question3.swapAt w a ∧ 0 < Question3.localRate x t w a) := by
  exact Question3.question3_full_twoSite_explicit
    (Species := Fin m) (x := x) (t := t) (Pstar := Pstar)
    hden hpos
    (exists_inversion_boundedWord (m := m) (n := 2) hm (by decide))

def xTwoSite31 : Fin 2 → ℝ := fun i =>
  if i.1 = 0 then 3 else 1

lemma denomNonzero_xTwoSite31_half :
    Question3.DenomNonzero xTwoSite31 (1 / 2 : ℝ) := by
  intro a
  have ha : a = Question3.adjIndexZeroTwo := Question3.adjIndex_eq_zero_two a
  subst ha
  norm_num [xTwoSite31, Question3.rateMinus, Question3.leftIndex, Question3.rightIndex,
    Question3.adjIndexZeroTwo]

lemma ratePlus_pos_xTwoSite31_half :
    ∀ a : Question3.AdjIndex 2, 0 < Question3.ratePlus xTwoSite31 (1 / 2 : ℝ) a := by
  intro a
  have ha : a = Question3.adjIndexZeroTwo := Question3.adjIndex_eq_zero_two a
  subst ha
  norm_num [xTwoSite31, Question3.ratePlus, Question3.leftIndex, Question3.rightIndex,
    Question3.adjIndexZeroTwo]

theorem question3_full_on_bounded_words_twoSite_x31_half_auto
    {m : ℕ}
    (Pstar : ℝ)
    (hm : 2 ≤ m) :
    (∀ y : BoundedWord m 2,
      (∑ w, Question3.PiFromFstarPstar
        (Question3.FstarAtQ1ByDefinition
          (Question3.twoSiteWeight (Species := Fin m) xTwoSite31 (1 / 2 : ℝ)))
        Pstar w * Question3.transitionRate xTwoSite31 (1 / 2 : ℝ) w y)
        =
      Question3.PiFromFstarPstar
        (Question3.FstarAtQ1ByDefinition
          (Question3.twoSiteWeight (Species := Fin m) xTwoSite31 (1 / 2 : ℝ)))
        Pstar y * (∑ z, Question3.transitionRate xTwoSite31 (1 / 2 : ℝ) y z))
    ∧
    (∃ w : BoundedWord m 2, ∃ a : Question3.AdjIndex 2,
      w ≠ Question3.swapAt w a ∧ 0 < Question3.localRate xTwoSite31 (1 / 2 : ℝ) w a) := by
  exact question3_full_on_bounded_words_twoSite_explicit_auto
    (m := m) (x := xTwoSite31) (t := (1 / 2 : ℝ)) (Pstar := Pstar) hm
    denomNonzero_xTwoSite31_half
    ratePlus_pos_xTwoSite31_half

def piTwoSite31Half
    {m : ℕ} (Pstar : ℝ) : BoundedWord m 2 → ℝ := fun w =>
  Question3.PiFromFstarPstar
    (Question3.FstarAtQ1ByDefinition
      (Question3.twoSiteWeight (Species := Fin m) xTwoSite31 (1 / 2 : ℝ)))
    Pstar w

theorem question3_full_on_bounded_words_twoSite_x31_half_pstar_one_auto
    {m : ℕ}
    (hm : 2 ≤ m) :
    (∀ y : BoundedWord m 2,
      (∑ w, piTwoSite31Half (m := m) 1 w *
        Question3.transitionRate xTwoSite31 (1 / 2 : ℝ) w y)
        =
      piTwoSite31Half (m := m) 1 y *
        (∑ z, Question3.transitionRate xTwoSite31 (1 / 2 : ℝ) y z))
    ∧
    (∃ w : BoundedWord m 2, ∃ a : Question3.AdjIndex 2,
      w ≠ Question3.swapAt w a ∧ 0 < Question3.localRate xTwoSite31 (1 / 2 : ℝ) w a) := by
  simpa [piTwoSite31Half] using
    question3_full_on_bounded_words_twoSite_x31_half_auto
      (m := m) (Pstar := 1) hm

theorem exists_explicit_nontrivial_twoSite_chain
    {m : ℕ}
    (hm : 2 ≤ m) :
    ∃ (x : Fin 2 → ℝ) (t : ℝ) (pi : BoundedWord m 2 → ℝ),
      (∀ y : BoundedWord m 2,
        (∑ w, pi w * Question3.transitionRate x t w y)
          =
        pi y * (∑ z, Question3.transitionRate x t y z))
      ∧
      (∃ w : BoundedWord m 2, ∃ a : Question3.AdjIndex 2,
        w ≠ Question3.swapAt w a ∧ 0 < Question3.localRate x t w a) := by
  refine ⟨xTwoSite31, (1 / 2 : ℝ), piTwoSite31Half (m := m) 1, ?_⟩
  exact question3_full_on_bounded_words_twoSite_x31_half_pstar_one_auto (m := m) hm

def xNegIndex (n : ℕ) : Fin n → ℝ := fun i => - (i.1 : ℝ)

lemma denomNonzero_xNegIndex_one
    (n : ℕ) :
    Question3.DenomNonzero (xNegIndex n) 1 := by
  intro a
  norm_num [Question3.rateMinus, Question3.leftIndex, Question3.rightIndex, xNegIndex]

lemma ratePlus_pos_xNegIndex_one
    (n : ℕ) :
    ∀ a : Question3.AdjIndex n, 0 < Question3.ratePlus (xNegIndex n) 1 a := by
  intro a
  norm_num [Question3.ratePlus, Question3.leftIndex, Question3.rightIndex, xNegIndex]

lemma rateMinus_pos_xNegIndex_one
    (n : ℕ) :
    ∀ a : Question3.AdjIndex n, 0 < Question3.rateMinus (xNegIndex n) 1 a := by
  intro a
  have hPlus : 0 < Question3.ratePlus (xNegIndex n) 1 a :=
    ratePlus_pos_xNegIndex_one n a
  simpa [Question3.ratePlus_eq_rateMinus_one (x := xNegIndex n) (a := a)] using hPlus

lemma localRate_nonneg_xNegIndex_one
    {m n : ℕ}
    (w : BoundedWord m n) (a : Question3.AdjIndex n) :
    0 ≤ Question3.localRate (xNegIndex n) 1 w a := by
  rcases lt_trichotomy (w (Question3.leftIndex a)) (w (Question3.rightIndex a)) with hlt | heq | hgt
  · have hminus : 0 ≤ Question3.rateMinus (xNegIndex n) 1 a :=
      (rateMinus_pos_xNegIndex_one n a).le
    simpa [Question3.localRate_of_lt (x := xNegIndex n) (t := 1) (w := w) (a := a) hlt] using hminus
  · simp [Question3.localRate_of_eq (x := xNegIndex n) (t := 1) (w := w) (a := a) heq]
  · have hplus : 0 ≤ Question3.ratePlus (xNegIndex n) 1 a :=
      (ratePlus_pos_xNegIndex_one n a).le
    simpa [Question3.localRate_of_gt (x := xNegIndex n) (t := 1) (w := w) (a := a) hgt] using hplus

lemma edgeKernel_nonneg_xNegIndex_one
    {m n : ℕ}
    (w w' : BoundedWord m n) (a : Question3.AdjIndex n) :
    0 ≤ Question3.edgeKernel (xNegIndex n) 1 w w' a := by
  by_cases hSwap : Question3.swapAt w a = w'
  · simp [Question3.edgeKernel, hSwap, localRate_nonneg_xNegIndex_one (w := w) (a := a)]
  · simp [Question3.edgeKernel, hSwap]

lemma transitionRate_nonneg_xNegIndex_one
    {m n : ℕ}
    (w w' : BoundedWord m n) :
    0 ≤ Question3.transitionRate (xNegIndex n) 1 w w' := by
  unfold Question3.transitionRate
  refine Finset.sum_nonneg ?_
  intro a ha
  exact edgeKernel_nonneg_xNegIndex_one (w := w) (w' := w') a

def piConstWeight
    {m n : ℕ} (Pstar : ℝ) : BoundedWord m n → ℝ := fun w =>
  Question3.PiFromFstarPstar
    (Question3.FstarAtQ1ByDefinition (fun _ : BoundedWord m n => (1 : ℝ)))
    Pstar w

theorem question3_full_on_bounded_words_t_one_xNegIndex_auto
    {m n : ℕ}
    (Pstar : ℝ)
    (hm : 2 ≤ m) (hn : 2 ≤ n) :
    (∀ y : BoundedWord m n,
      (∑ w, piConstWeight (m := m) (n := n) Pstar w *
        Question3.transitionRate (xNegIndex n) 1 w y)
        =
      piConstWeight (m := m) (n := n) Pstar y *
        (∑ z, Question3.transitionRate (xNegIndex n) 1 y z))
    ∧
    (∃ w : BoundedWord m n, ∃ a : Question3.AdjIndex n,
      w ≠ Question3.swapAt w a ∧ 0 < Question3.localRate (xNegIndex n) 1 w a) := by
  simpa [piConstWeight] using
    question3_full_on_bounded_words_t_one_const_weight_auto
      (m := m) (n := n) (x := xNegIndex n) (Pstar := Pstar)
      hm hn (denomNonzero_xNegIndex_one n) (ratePlus_pos_xNegIndex_one n)

theorem exists_explicit_nontrivial_chain_t_one_const_weight
    {m n : ℕ}
    (hm : 2 ≤ m) (hn : 2 ≤ n) :
    ∃ (x : Fin n → ℝ) (t : ℝ) (pi : BoundedWord m n → ℝ),
      (∀ y : BoundedWord m n,
        (∑ w, pi w * Question3.transitionRate x t w y)
          =
        pi y * (∑ z, Question3.transitionRate x t y z))
      ∧
      (∃ w : BoundedWord m n, ∃ a : Question3.AdjIndex n,
        w ≠ Question3.swapAt w a ∧ 0 < Question3.localRate x t w a) := by
  refine ⟨xNegIndex n, 1, piConstWeight (m := m) (n := n) 1, ?_⟩
  exact question3_full_on_bounded_words_t_one_xNegIndex_auto
    (m := m) (n := n) (Pstar := 1) hm hn

end

end Bridge
end Macdonald
