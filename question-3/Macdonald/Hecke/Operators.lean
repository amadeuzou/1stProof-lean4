import Mathlib.Algebra.MvPolynomial.Basic
import Mathlib.Algebra.MvPolynomial.Rename
import Mathlib.GroupTheory.Perm.Fin

namespace Macdonald
namespace Hecke

/-!
Phase 1.1: multivariate polynomial ambient space and `S_n` action.
-/

noncomputable section

abbrev Poly (n : ℕ) (R : Type*) [CommSemiring R] := MvPolynomial (Fin n) R

section PermutationAction

variable {n : ℕ} {R : Type*} [CommSemiring R]

def permuteVars (σ : Equiv.Perm (Fin n)) : Poly n R →ₐ[R] Poly n R :=
  MvPolynomial.rename σ

@[simp] theorem permuteVars_apply (σ : Equiv.Perm (Fin n)) (p : Poly n R) :
    permuteVars (R := R) σ p = MvPolynomial.rename σ p := rfl

@[simp] theorem permuteVars_X (σ : Equiv.Perm (Fin n)) (i : Fin n) :
    permuteVars (R := R) σ (MvPolynomial.X i) = MvPolynomial.X (σ i) := by
  simp [permuteVars]

@[simp] theorem permuteVars_C (σ : Equiv.Perm (Fin n)) (r : R) :
    permuteVars (R := R) σ (MvPolynomial.C r) = MvPolynomial.C r := by
  simp [permuteVars]

@[simp] theorem permuteVars_id (p : Poly n R) :
    permuteVars (R := R) (Equiv.refl (Fin n)) p = p := by
  simp [permuteVars]

@[simp] theorem permuteVars_comp
    (σ τ : Equiv.Perm (Fin n)) (p : Poly n R) :
    permuteVars (R := R) σ (permuteVars (R := R) τ p) =
      permuteVars (R := R) (τ.trans σ) p := by
  unfold permuteVars
  exact MvPolynomial.rename_rename (f := τ) (g := σ) (p := p)

end PermutationAction

section AdjacentSwap

variable {n : ℕ}

def adjacentSwap (i : Fin n) (h : i.1 + 1 < n) : Equiv.Perm (Fin n) :=
  Equiv.swap i ⟨i.1 + 1, h⟩

@[simp] theorem adjacentSwap_left (i : Fin n) (h : i.1 + 1 < n) :
    adjacentSwap i h i = ⟨i.1 + 1, h⟩ := by
  simp [adjacentSwap]

@[simp] theorem adjacentSwap_right (i : Fin n) (h : i.1 + 1 < n) :
    adjacentSwap i h ⟨i.1 + 1, h⟩ = i := by
  simp [adjacentSwap]

theorem adjacentSwap_involutive (i : Fin n) (h : i.1 + 1 < n) :
    Function.Involutive (adjacentSwap i h) := by
  intro j
  simp [adjacentSwap]

theorem adjacentSwap_comm_of_lt
    (i j : Fin n) (hi : i.1 + 1 < n) (hj : j.1 + 1 < n)
    (hlt : i.1 + 1 < j.1) :
    adjacentSwap i hi * adjacentSwap j hj =
      adjacentSwap j hj * adjacentSwap i hi := by
  let i1 : Fin n := ⟨i.1 + 1, hi⟩
  let j1 : Fin n := ⟨j.1 + 1, hj⟩
  have hac : i ≠ j := by
    intro h
    exact (ne_of_lt (lt_trans (Nat.lt_succ_self i.1) hlt)) (congrArg Fin.val h)
  have had : i ≠ j1 := by
    intro h
    have hlt' : i.1 < j.1 + 1 :=
      lt_trans (lt_trans (Nat.lt_succ_self i.1) hlt) (Nat.lt_succ_self j.1)
    exact (ne_of_lt hlt') (congrArg Fin.val h)
  have hbc : i1 ≠ j := by
    intro h
    exact (ne_of_lt hlt) (congrArg Fin.val h)
  have hbd : i1 ≠ j1 := by
    intro h
    have hlt' : i.1 + 1 < j.1 + 1 := lt_trans hlt (Nat.lt_succ_self j.1)
    exact (ne_of_lt hlt') (congrArg Fin.val h)
  have h1 : (Equiv.swap i i1) j = j :=
    Equiv.swap_apply_of_ne_of_ne hac.symm hbc.symm
  have h2 : (Equiv.swap i i1) j1 = j1 :=
    Equiv.swap_apply_of_ne_of_ne had.symm hbd.symm
  have hswap : Equiv.swap i i1 * Equiv.swap j j1 = Equiv.swap j j1 * Equiv.swap i i1 := by
    calc
      Equiv.swap i i1 * Equiv.swap j j1
        = Equiv.swap ((Equiv.swap i i1) j) ((Equiv.swap i i1) j1) * Equiv.swap i i1 := by
            simpa using (Equiv.mul_swap_eq_swap_mul (f := Equiv.swap i i1) (x := j) (y := j1))
      _ = Equiv.swap j j1 * Equiv.swap i i1 := by
            rw [h1, h2]
  simpa [adjacentSwap, i1, j1] using hswap

theorem adjacentSwap_comm_of_far
    (i j : Fin n) (hi : i.1 + 1 < n) (hj : j.1 + 1 < n)
    (hfar : i.1 + 1 < j.1 ∨ j.1 + 1 < i.1) :
    adjacentSwap i hi * adjacentSwap j hj =
      adjacentSwap j hj * adjacentSwap i hi := by
  rcases hfar with hlt | hgt
  · exact adjacentSwap_comm_of_lt (i := i) (j := j) (hi := hi) (hj := hj) hlt
  · exact (adjacentSwap_comm_of_lt (i := j) (j := i) (hi := hj) (hj := hi) hgt).symm

theorem adjacentSwap_braid
    (i : Fin n) (h1 : i.1 + 1 < n) (h2 : i.1 + 2 < n) :
    adjacentSwap i h1 * adjacentSwap ⟨i.1 + 1, h1⟩ (by simpa using h2) * adjacentSwap i h1 =
      adjacentSwap ⟨i.1 + 1, h1⟩ (by simpa using h2) * adjacentSwap i h1 *
        adjacentSwap ⟨i.1 + 1, h1⟩ (by simpa using h2) := by
  let j : Fin n := ⟨i.1 + 1, h1⟩
  let k : Fin n := ⟨i.1 + 2, h2⟩
  have hj : j.1 + 1 < n := by
    simpa [j] using h2
  have hij : i ≠ j := by
    intro h
    exact (ne_of_lt (Nat.lt_succ_self i.1)) (congrArg Fin.val h)
  have hik : i ≠ k := by
    intro h
    exact (ne_of_lt (Nat.lt_add_of_pos_right (by decide : 0 < 2))) (congrArg Fin.val h)
  have hjk : j ≠ k := by
    intro h
    have hlt : i.1 + 1 < i.1 + 2 := by
      exact Nat.lt_succ_self (i.1 + 1)
    exact (ne_of_lt hlt) (congrArg Fin.val h)
  have hLeft : Equiv.swap j k * Equiv.swap i j * Equiv.swap j k = Equiv.swap k i := by
    exact Equiv.swap_mul_swap_mul_swap (x := i) (y := j) (z := k) hij hik
  have hRight : Equiv.swap i j * Equiv.swap j k * Equiv.swap i j = Equiv.swap i k := by
    simpa [Equiv.swap_comm] using
      (Equiv.swap_mul_swap_mul_swap (x := k) (y := j) (z := i) hjk.symm hik.symm)
  have hi : adjacentSwap i h1 = Equiv.swap i j := by
    simp [adjacentSwap, j]
  have hjadj : adjacentSwap j hj = Equiv.swap j k := by
    simp [adjacentSwap, j, k]
  calc
    adjacentSwap i h1 * adjacentSwap ⟨i.1 + 1, h1⟩ (by simpa using h2) * adjacentSwap i h1
      = adjacentSwap i h1 * adjacentSwap j hj * adjacentSwap i h1 := by rfl
    _ = Equiv.swap i j * Equiv.swap j k * Equiv.swap i j := by
          simp [hi, hjadj]
    _ = Equiv.swap i k := hRight
    _ = Equiv.swap k i := by simp [Equiv.swap_comm]
    _ = Equiv.swap j k * Equiv.swap i j * Equiv.swap j k := hLeft.symm
    _ = adjacentSwap j hj * adjacentSwap i h1 * adjacentSwap j hj := by
          simp [hi, hjadj]
    _ = adjacentSwap ⟨i.1 + 1, h1⟩ (by simpa using h2) * adjacentSwap i h1 *
          adjacentSwap ⟨i.1 + 1, h1⟩ (by simpa using h2) := by rfl

end AdjacentSwap

end

end Hecke
end Macdonald
