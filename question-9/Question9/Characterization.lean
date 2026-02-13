import Question9.PolynomialMap

namespace Question9

open Anchors

namespace Characterization

variable {n : Nat} (S : Anchors n) (lam : Lambda n)

theorem separable_implies_fzero (hsep : separable lam) :
    FZero S lam := by
  rcases hsep with ⟨u, v, w, x, hu, hv, hw, hx, hform⟩
  intro a b c d hvalid
  have habcd : lam a b c d = u a * v b * w c * x d := hform a b c d hvalid
  have hA : lam a S.b0 S.c0 S.d0 = u a * v S.b0 * w S.c0 * x S.d0 := by
    exact hform a S.b0 S.c0 S.d0 (S.valid_a_slice a)
  have hB : lam S.a0 b S.c0 S.d0 = u S.a0 * v b * w S.c0 * x S.d0 := by
    exact hform S.a0 b S.c0 S.d0 (S.valid_b_slice b)
  have hC : lam S.a0 S.b0 c S.d0 = u S.a0 * v S.b0 * w c * x S.d0 := by
    exact hform S.a0 S.b0 c S.d0 (S.valid_c_slice c)
  have hD : lam S.a0 S.b0 S.c0 d = u S.a0 * v S.b0 * w S.c0 * x d := by
    exact hform S.a0 S.b0 S.c0 d (S.valid_d_slice d)
  have h0 : lam S.a0 S.b0 S.c0 S.d0 = u S.a0 * v S.b0 * w S.c0 * x S.d0 := by
    exact hform S.a0 S.b0 S.c0 S.d0 S.valid_anchor
  simp [FMap, coord, habcd, hA, hB, hC, hD, h0]
  ring

theorem fzero_implies_separable
    (hF : FZero S lam)
    (hNZ : nonzeroOnValid lam) :
    separable lam := by
  let lam0 : ℝ := lam S.a0 S.b0 S.c0 S.d0
  have hlam0 : lam0 ≠ 0 := by
    exact hNZ S.a0 S.b0 S.c0 S.d0 S.valid_anchor
  let u : Idx n → ℝ := fun a => lam a S.b0 S.c0 S.d0
  let v : Idx n → ℝ := fun b => lam S.a0 b S.c0 S.d0
  let w : Idx n → ℝ := fun c => lam S.a0 S.b0 c S.d0
  let x : Idx n → ℝ := fun d => lam S.a0 S.b0 S.c0 d / (lam0 ^ 3)
  refine ⟨u, v, w, x, ?_, ?_, ?_, ?_, ?_⟩
  · intro a
    exact hNZ a S.b0 S.c0 S.d0 (S.valid_a_slice a)
  · intro b
    exact hNZ S.a0 b S.c0 S.d0 (S.valid_b_slice b)
  · intro c
    exact hNZ S.a0 S.b0 c S.d0 (S.valid_c_slice c)
  · intro d
    have hslice : lam S.a0 S.b0 S.c0 d ≠ 0 := hNZ S.a0 S.b0 S.c0 d (S.valid_d_slice d)
    exact div_ne_zero hslice (pow_ne_zero 3 hlam0)
  · intro a b c d hvalid
    have hcoord0 : coord S lam a b c d = 0 := hF a b c d hvalid
    have hcoord :
        lam a b c d * lam0 ^ 3 =
          lam a S.b0 S.c0 S.d0
            * lam S.a0 b S.c0 S.d0
            * lam S.a0 S.b0 c S.d0
            * lam S.a0 S.b0 S.c0 d := by
      have htmp : lam a b c d * lam0 ^ 3
          - (lam a S.b0 S.c0 S.d0
            * lam S.a0 b S.c0 S.d0
            * lam S.a0 S.b0 c S.d0
            * lam S.a0 S.b0 S.c0 d) = 0 := by
        simpa [coord, lam0] using hcoord0
      exact sub_eq_zero.mp htmp
    have hpow3 : lam0 ^ 3 ≠ 0 := pow_ne_zero 3 hlam0
    have hdiv :
        lam a b c d =
          (lam a S.b0 S.c0 S.d0
            * lam S.a0 b S.c0 S.d0
            * lam S.a0 S.b0 c S.d0
            * lam S.a0 S.b0 S.c0 d) / (lam0 ^ 3) := by
      exact (eq_div_iff hpow3).2 hcoord
    rw [hdiv]
    have hmul :
        (lam a S.b0 S.c0 S.d0
          * lam S.a0 b S.c0 S.d0
          * lam S.a0 S.b0 c S.d0
          * lam S.a0 S.b0 S.c0 d) / (lam0 ^ 3)
          =
        (lam a S.b0 S.c0 S.d0
          * lam S.a0 b S.c0 S.d0
          * lam S.a0 S.b0 c S.d0)
          * (lam S.a0 S.b0 S.c0 d / (lam0 ^ 3)) := by
      simpa [mul_assoc] using
        (mul_div_assoc
          (lam a S.b0 S.c0 S.d0
            * lam S.a0 b S.c0 S.d0
            * lam S.a0 S.b0 c S.d0)
          (lam S.a0 S.b0 S.c0 d)
          (lam0 ^ 3))
    simpa [u, v, w, x, mul_assoc] using hmul

theorem fzero_iff_separable
    (hNZ : nonzeroOnValid lam) :
    FZero S lam ↔ separable lam := by
  constructor
  · intro hF
    exact fzero_implies_separable S lam hF hNZ
  · intro hsep
    exact separable_implies_fzero S lam hsep

end Characterization
end Question9
