import Question7.Defs
import Mathlib.GroupTheory.Perm.Cycle.Type

set_option autoImplicit false

universe u

namespace Question7

variable {E : Type u} [TopologicalSpace E]

/--
Abstract fixed-point consequence of Smith/Lefschetz-type input for involutive
homeomorphisms.
-/
theorem fixed_point_of_involutive_homeomorph
    (hFixed : HasInvolutiveHomeomorphFixedPointProperty E)
    (g : E ≃ₜ E) (hInv : Function.Involutive g) :
    ∃ x : E, g x = x :=
  hFixed g hInv

theorem fixed_point_of_involutive_homeomorph_of_input
    [InvolutionFixedPointInput E]
    (g : E ≃ₜ E) (hInv : Function.Involutive g) :
    ∃ x : E, g x = x :=
  fixed_point_of_involutive_homeomorph
    (InvolutionFixedPointInput.hasFixedPoint (E := E)) g hInv

theorem fixed_point_of_involutive_homeomorph_of_fintype_odd
    [Fintype E] [DecidableEq E]
    (g : E ≃ₜ E) (hInv : Function.Involutive g)
    (hodd : Odd (Fintype.card E)) :
    ∃ x : E, g x = x := by
  have hNotDvd : ¬ 2 ∣ Fintype.card E := by
    rw [Nat.two_dvd_ne_zero]
    exact Nat.odd_iff.mp hodd
  have hPrime : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hpow : (g.toEquiv : Equiv.Perm E) ^ 2 ^ 1 = 1 := by
    ext x
    simp [pow_two, hInv x]
  obtain ⟨x, hx⟩ :=
    Equiv.Perm.exists_fixed_point_of_prime (α := E) (p := 2) (n := 1) hNotDvd hpow
  exact ⟨x, hx⟩

theorem hasInvolutiveHomeomorphFixedPointProperty_of_fintype_odd
    [Fintype E] [DecidableEq E] (hodd : Odd (Fintype.card E)) :
    HasInvolutiveHomeomorphFixedPointProperty E := by
  intro g hInv
  exact fixed_point_of_involutive_homeomorph_of_fintype_odd g hInv hodd

theorem hasInvolutiveHomeomorphFixedPointProperty_of_subsingleton
    [Subsingleton E] [Inhabited E] :
    HasInvolutiveHomeomorphFixedPointProperty E := by
  intro g _hInv
  refine ⟨default, ?_⟩
  exact Subsingleton.elim _ _

instance involutionFixedPointInput_of_subsingleton
    [Subsingleton E] [Inhabited E] :
    InvolutionFixedPointInput E where
  hasFixedPoint := hasInvolutiveHomeomorphFixedPointProperty_of_subsingleton

instance involutionFixedPointInput_of_fintype_odd
    [Fintype E] [DecidableEq E] [Fact (Odd (Fintype.card E))] :
    InvolutionFixedPointInput E where
  hasFixedPoint := hasInvolutiveHomeomorphFixedPointProperty_of_fintype_odd (Fact.out)

end Question7
