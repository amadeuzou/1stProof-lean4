import Macdonald.Bridge.Question3Finite

namespace Macdonald
namespace Bridge

open Question3
open scoped BigOperators

noncomputable section

section SnLambda

variable {m n : ℕ}

def permuteWord (σ : Equiv.Perm (Fin n)) (w : BoundedWord m n) : BoundedWord m n := fun i =>
  w (σ i)

@[simp] lemma permuteWord_apply
    (σ : Equiv.Perm (Fin n)) (w : BoundedWord m n) (i : Fin n) :
    permuteWord σ w i = w (σ i) := rfl

def SnLambdaSet (lam : BoundedWord m n) : Set (BoundedWord m n) := fun w =>
  ∃ σ : Equiv.Perm (Fin n), w = permuteWord σ lam

def SnLambdaState (lam : BoundedWord m n) : Type := { w : BoundedWord m n // SnLambdaSet lam w }

instance snLambdaStateFinite (lam : BoundedWord m n) : Finite (SnLambdaState lam) := by
  classical
  exact Finite.of_injective (f := (Subtype.val : SnLambdaState lam → BoundedWord m n))
    Subtype.val_injective

noncomputable instance snLambdaStateFintype (lam : BoundedWord m n) : Fintype (SnLambdaState lam) :=
  Fintype.ofFinite (SnLambdaState lam)

lemma snLambda_mem_self (lam : BoundedWord m n) : SnLambdaSet lam lam := by
  refine ⟨Equiv.refl (Fin n), ?_⟩
  funext i
  simp [permuteWord]

lemma swapAt_permuteWord
    (σ : Equiv.Perm (Fin n)) (w : BoundedWord m n) (a : AdjIndex n) :
    swapAt (permuteWord σ w) a =
      permuteWord (σ * Equiv.swap (leftIndex a) (rightIndex a)) w := by
  funext i
  by_cases hi : i = leftIndex a
  · subst hi
    simp [swapAt, permuteWord, Equiv.Perm.mul_apply]
  · by_cases hj : i = rightIndex a
    · subst hj
      simp [swapAt, permuteWord, Equiv.Perm.mul_apply, hi]
    · have hs : Equiv.swap (leftIndex a) (rightIndex a) i = i :=
        Equiv.swap_apply_of_ne_of_ne hi hj
      simp [swapAt, permuteWord, Equiv.Perm.mul_apply, hi, hj, hs]

lemma snLambda_closed_swap
    {lam w : BoundedWord m n} (hw : SnLambdaSet lam w) (a : AdjIndex n) :
    SnLambdaSet lam (swapAt w a) := by
  rcases hw with ⟨σ, rfl⟩
  refine ⟨σ * Equiv.swap (leftIndex a) (rightIndex a), ?_⟩
  simpa using swapAt_permuteWord (m := m) (σ := σ) (w := lam) (a := a)

def transitionRateSn
    (x : Fin n → ℝ) (t : ℝ)
    (lam : BoundedWord m n) :
    SnLambdaState lam → SnLambdaState lam → ℝ := fun u v =>
  transitionRate x t u.1 v.1

def piSn
    (asepWeight : BoundedWord m n → ℝ)
    (Pstar : ℝ)
    (lam : BoundedWord m n) :
    SnLambdaState lam → ℝ := fun u =>
  PiFromFstarPstar (FstarAtQ1ByDefinition asepWeight) Pstar u.1

theorem stationary_on_SnLambda
    (asepWeight : BoundedWord m n → ℝ)
    (lam : BoundedWord m n)
    (x : Fin n → ℝ) (t : ℝ) (Pstar : ℝ)
    (hEx : WeightExchange (Species := Fin m) asepWeight x t)
    (hden : DenomNonzero x t) :
    ∀ y : SnLambdaState lam,
      (∑ w, piSn asepWeight Pstar lam w * transitionRateSn x t lam w y)
        =
      piSn asepWeight Pstar lam y * (∑ z, transitionRateSn x t lam y z) := by
  let weightOn : SnLambdaState lam → ℝ := fun u => asepWeight u.1
  have hdbOn :
      ∀ u v : SnLambdaState lam,
        weightOn u * transitionRateSn x t lam u v =
          weightOn v * transitionRateSn x t lam v u := by
    intro u v
    exact detailed_balance_explicit
      (Species := Fin m) (weight := asepWeight)
      (x := x) (t := t) hEx hden u.1 v.1
  have hGBOn :
      ∀ y : SnLambdaState lam,
        (∑ w, weightOn w * transitionRateSn x t lam w y)
          =
        weightOn y * (∑ z, transitionRateSn x t lam y z) :=
    globalBalance_of_detailedBalance
      (State := SnLambdaState lam)
      (weight := weightOn)
      (rate := transitionRateSn x t lam)
      hdbOn
  intro y
  simpa [piSn, weightOn, transitionRateSn, PiFromFstarPstar, FstarAtQ1ByDefinition] using
    global_balance_normalized
      (State := SnLambdaState lam)
      (weight := weightOn)
      (rate := transitionRateSn x t lam)
      (Pstar := Pstar) hGBOn y

theorem nontrivial_on_SnLambda
    (lam : BoundedWord m n)
    (x : Fin n → ℝ) (t : ℝ)
    (hpos : ∀ a : AdjIndex n, 0 < ratePlus x t a)
    (hInv : ∃ a : AdjIndex n, lam (leftIndex a) > lam (rightIndex a)) :
    ∃ w : SnLambdaState lam, ∃ a : AdjIndex n,
      w.1 ≠ swapAt w.1 a ∧ 0 < localRate x t w.1 a := by
  rcases hInv with ⟨a, hgt⟩
  let w0 : SnLambdaState lam := ⟨lam, snLambda_mem_self lam⟩
  refine ⟨w0, a, ?_, ?_⟩
  · have hneq : swapAt lam a ≠ lam :=
      swapAt_ne_of_diff (w := lam) (a := a) (ne_of_gt hgt)
    intro hEq
    exact hneq hEq.symm
  · have hlocal : localRate x t lam a = ratePlus x t a :=
      localRate_of_gt (x := x) (t := t) (w := lam) (a := a) hgt
    calc
      0 < ratePlus x t a := hpos a
      _ = localRate x t lam a := hlocal.symm

theorem question3_full_on_SnLambda
    (asepWeight : BoundedWord m n → ℝ)
    (lam : BoundedWord m n)
    (x : Fin n → ℝ) (t : ℝ) (Pstar : ℝ)
    (hEx : WeightExchange (Species := Fin m) asepWeight x t)
    (hden : DenomNonzero x t)
    (hpos : ∀ a : AdjIndex n, 0 < ratePlus x t a)
    (hInv : ∃ a : AdjIndex n, lam (leftIndex a) > lam (rightIndex a)) :
    (∀ y : SnLambdaState lam,
      (∑ w, piSn asepWeight Pstar lam w * transitionRateSn x t lam w y)
        =
      piSn asepWeight Pstar lam y * (∑ z, transitionRateSn x t lam y z))
    ∧
    (∃ w : SnLambdaState lam, ∃ a : AdjIndex n,
      w.1 ≠ swapAt w.1 a ∧ 0 < localRate x t w.1 a) := by
  constructor
  · exact stationary_on_SnLambda
      (asepWeight := asepWeight) (lam := lam)
      (x := x) (t := t) (Pstar := Pstar) hEx hden
  · exact nontrivial_on_SnLambda
      (lam := lam) (x := x) (t := t) hpos hInv

theorem exists_explicit_chain_on_SnLambda_t_one_const_weight
    (lam : BoundedWord m n)
    (hInv : ∃ a : AdjIndex n, lam (leftIndex a) > lam (rightIndex a)) :
    ∃ (x : Fin n → ℝ) (t : ℝ) (pi : SnLambdaState lam → ℝ),
      (∀ y : SnLambdaState lam,
        (∑ w, pi w * transitionRateSn x t lam w y)
          =
        pi y * (∑ z, transitionRateSn x t lam y z))
      ∧
      (∃ w : SnLambdaState lam, ∃ a : AdjIndex n,
        w.1 ≠ swapAt w.1 a ∧ 0 < localRate x t w.1 a) := by
  refine ⟨xNegIndex n, 1, piSn (fun _ : BoundedWord m n => (1 : ℝ)) 1 lam, ?_⟩
  exact question3_full_on_SnLambda
    (asepWeight := fun _ : BoundedWord m n => (1 : ℝ))
    (lam := lam)
    (x := xNegIndex n) (t := 1) (Pstar := 1)
    (weightExchange_const_one_t_one (Species := Fin m)
      (x := xNegIndex n) (denomNonzero_xNegIndex_one n))
    (denomNonzero_xNegIndex_one n)
    (ratePlus_pos_xNegIndex_one n)
    hInv

theorem exists_local_inversion_of_strictAdjacent
    (lam : BoundedWord m n)
    (hn : 2 ≤ n)
    (hDesc : ∀ a : AdjIndex n, lam (leftIndex a) > lam (rightIndex a)) :
    ∃ a : AdjIndex n, lam (leftIndex a) > lam (rightIndex a) := by
  have hn0 : 0 < n := lt_of_lt_of_le (by decide : 0 < 2) hn
  have hn1 : 1 < n := lt_of_lt_of_le (by decide : 1 < 2) hn
  let i0 : Fin n := ⟨0, hn0⟩
  let a0 : AdjIndex n := ⟨i0, by simpa [i0] using hn1⟩
  exact ⟨a0, hDesc a0⟩

theorem exists_explicit_chain_on_SnLambda_of_strictAdjacent
    (lam : BoundedWord m n)
    (hn : 2 ≤ n)
    (hDesc : ∀ a : AdjIndex n, lam (leftIndex a) > lam (rightIndex a)) :
    ∃ (x : Fin n → ℝ) (t : ℝ) (pi : SnLambdaState lam → ℝ),
      (∀ y : SnLambdaState lam,
        (∑ w, pi w * transitionRateSn x t lam w y)
          =
        pi y * (∑ z, transitionRateSn x t lam y z))
      ∧
      (∃ w : SnLambdaState lam, ∃ a : AdjIndex n,
        w.1 ≠ swapAt w.1 a ∧ 0 < localRate x t w.1 a) := by
  exact exists_explicit_chain_on_SnLambda_t_one_const_weight
    (lam := lam)
    (exists_local_inversion_of_strictAdjacent
      (lam := lam) (hn := hn) hDesc)

def IsStrictAdjacentDescending (lam : BoundedWord m n) : Prop :=
  ∀ a : AdjIndex n, lam (leftIndex a) > lam (rightIndex a)

def HasUniqueZeroPart (lam : BoundedWord m n) : Prop :=
  ∃ i : Fin n, (lam i).1 = 0 ∧ ∀ j : Fin n, (lam j).1 = 0 → j = i

def HasNoOnePart (lam : BoundedWord m n) : Prop :=
  ∀ i : Fin n, (lam i).1 ≠ 1

def IsRestrictedWord (lam : BoundedWord m n) : Prop :=
  IsStrictAdjacentDescending lam ∧ HasUniqueZeroPart lam ∧ HasNoOnePart lam

theorem exists_explicit_chain_on_SnLambda_of_restricted
    (lam : BoundedWord m n)
    (hn : 2 ≤ n)
    (hRes : IsRestrictedWord lam) :
    ∃ (x : Fin n → ℝ) (t : ℝ) (pi : SnLambdaState lam → ℝ),
      (∀ y : SnLambdaState lam,
        (∑ w, pi w * transitionRateSn x t lam w y)
          =
        pi y * (∑ z, transitionRateSn x t lam y z))
      ∧
      (∃ w : SnLambdaState lam, ∃ a : AdjIndex n,
        w.1 ≠ swapAt w.1 a ∧ 0 < localRate x t w.1 a) := by
  exact exists_explicit_chain_on_SnLambda_of_strictAdjacent
    (lam := lam) (hn := hn) hRes.1

def canonicalFstarWeight : BoundedWord m n → ℝ := fun _ => 1

def canonicalPstar (lam : BoundedWord m n) : ℝ :=
  (Fintype.card (SnLambdaState lam) : ℝ)

def canonicalPi (lam : BoundedWord m n) : SnLambdaState lam → ℝ :=
  piSn (asepWeight := canonicalFstarWeight (m := m) (n := n))
    (Pstar := canonicalPstar lam) lam

@[simp] lemma canonicalPi_apply
    (lam : BoundedWord m n) (u : SnLambdaState lam) :
    canonicalPi (m := m) (n := n) lam u = (1 : ℝ) / canonicalPstar lam := by
  simp [canonicalPi, canonicalFstarWeight, canonicalPstar, piSn,
    PiFromFstarPstar, FstarAtQ1ByDefinition]

lemma canonicalPstar_pos (lam : BoundedWord m n) :
    0 < canonicalPstar (m := m) (n := n) lam := by
  have hNonempty : Nonempty (SnLambdaState lam) := ⟨⟨lam, snLambda_mem_self lam⟩⟩
  unfold canonicalPstar
  exact_mod_cast (Fintype.card_pos_iff.mpr hNonempty)

lemma canonicalPstar_ne_zero (lam : BoundedWord m n) :
    canonicalPstar (m := m) (n := n) lam ≠ 0 :=
  ne_of_gt (canonicalPstar_pos (m := m) (n := n) lam)

lemma canonicalPi_nonneg
    (lam : BoundedWord m n) (u : SnLambdaState lam) :
    0 ≤ canonicalPi (m := m) (n := n) lam u := by
  have hP : 0 < canonicalPstar (m := m) (n := n) lam :=
    canonicalPstar_pos (m := m) (n := n) lam
  simpa [canonicalPi_apply] using (div_nonneg (show (0 : ℝ) ≤ 1 by norm_num) hP.le)

lemma canonicalPi_sum_eq_one (lam : BoundedWord m n) :
    (∑ u : SnLambdaState lam, canonicalPi (m := m) (n := n) lam u) = 1 := by
  have hP0 : canonicalPstar (m := m) (n := n) lam ≠ 0 :=
    canonicalPstar_ne_zero (m := m) (n := n) lam
  calc
    (∑ u : SnLambdaState lam, canonicalPi (m := m) (n := n) lam u)
      = (Fintype.card (SnLambdaState lam) : ℝ) *
          ((1 : ℝ) / canonicalPstar (m := m) (n := n) lam) := by
          simp [canonicalPi_apply]
    _ = canonicalPstar (m := m) (n := n) lam *
          ((1 : ℝ) / canonicalPstar (m := m) (n := n) lam) := by
          simp [canonicalPstar]
    _ = 1 := by
          field_simp [hP0]

theorem canonicalPi_stationary
    (lam : BoundedWord m n) :
    ∀ y : SnLambdaState lam,
      (∑ w, canonicalPi (m := m) (n := n) lam w *
        transitionRateSn (xNegIndex n) 1 lam w y)
        =
      canonicalPi (m := m) (n := n) lam y *
        (∑ z, transitionRateSn (xNegIndex n) 1 lam y z) := by
  exact stationary_on_SnLambda
    (asepWeight := canonicalFstarWeight (m := m) (n := n))
    (lam := lam)
    (x := xNegIndex n) (t := 1)
    (Pstar := canonicalPstar (m := m) (n := n) lam)
    (weightExchange_const_one_t_one (Species := Fin m)
      (x := xNegIndex n) (denomNonzero_xNegIndex_one n))
    (denomNonzero_xNegIndex_one n)

theorem canonical_transitionRateSn_nonneg
    (lam : BoundedWord m n) :
    ∀ u v : SnLambdaState lam,
      0 ≤ transitionRateSn (xNegIndex n) 1 lam u v := by
  intro u v
  simpa [transitionRateSn] using
    Macdonald.Bridge.transitionRate_nonneg_xNegIndex_one
      (m := m) (n := n) u.1 v.1

theorem canonical_nontrivial_of_restricted
    (lam : BoundedWord m n)
    (hn : 2 ≤ n)
    (hRes : IsRestrictedWord lam) :
    ∃ w : SnLambdaState lam, ∃ a : AdjIndex n,
      w.1 ≠ swapAt w.1 a ∧ 0 < localRate (xNegIndex n) 1 w.1 a := by
  exact nontrivial_on_SnLambda
    (lam := lam) (x := xNegIndex n) (t := 1)
    (ratePlus_pos_xNegIndex_one n)
    (exists_local_inversion_of_strictAdjacent (lam := lam) (hn := hn) hRes.1)

theorem complete_chain_on_SnLambda_of_restricted
    (lam : BoundedWord m n)
    (hn : 2 ≤ n)
    (hRes : IsRestrictedWord lam) :
    (∀ y : SnLambdaState lam,
      (∑ w, canonicalPi (m := m) (n := n) lam w *
        transitionRateSn (xNegIndex n) 1 lam w y)
        =
      canonicalPi (m := m) (n := n) lam y *
        (∑ z, transitionRateSn (xNegIndex n) 1 lam y z))
    ∧
    (∀ u v : SnLambdaState lam,
      0 ≤ transitionRateSn (xNegIndex n) 1 lam u v)
    ∧
    (∀ u : SnLambdaState lam, 0 ≤ canonicalPi (m := m) (n := n) lam u)
    ∧
    ((∑ u : SnLambdaState lam, canonicalPi (m := m) (n := n) lam u) = 1)
    ∧
    (∃ w : SnLambdaState lam, ∃ a : AdjIndex n,
      w.1 ≠ swapAt w.1 a ∧ 0 < localRate (xNegIndex n) 1 w.1 a) := by
  refine ⟨canonicalPi_stationary (m := m) (n := n) lam, ?_, ?_, ?_, ?_⟩
  · exact canonical_transitionRateSn_nonneg (m := m) (n := n) lam
  · intro u
    exact canonicalPi_nonneg (m := m) (n := n) lam u
  · exact canonicalPi_sum_eq_one (m := m) (n := n) lam
  · exact canonical_nontrivial_of_restricted (m := m) (n := n) lam hn hRes

end SnLambda

end

end Bridge
end Macdonald
