import Question9.Characterization

namespace Question9

open Anchors
open Characterization

def H1Condition
    {n : Nat}
    (S : Anchors n)
    (lam : Lambda n) : Prop :=
  ∀ a b c d, valid a b c d →
    lam a b c d * lam S.a0 S.b0 S.c0 S.d0 =
      lam a b S.c0 S.d0 * lam S.a0 S.b0 c d

def H2Condition
    {n : Nat}
    (S : Anchors n)
    (lam : Lambda n) : Prop :=
  ∀ a b,
    lam a b S.c0 S.d0 * lam S.a0 S.b0 S.c0 S.d0 =
      lam a S.b0 S.c0 S.d0 * lam S.a0 b S.c0 S.d0

def H3Condition
    {n : Nat}
    (S : Anchors n)
    (lam : Lambda n) : Prop :=
  ∀ c d,
    lam S.a0 S.b0 c d * lam S.a0 S.b0 S.c0 S.d0 =
      lam S.a0 S.b0 c S.d0 * lam S.a0 S.b0 S.c0 d

def Bridge1Condition
    {n : Nat}
    (S : Anchors n)
    (lam : Lambda n) : Prop :=
  ∀ a b c d, valid a b c d →
    lam c b a d * lam S.c0 S.b0 S.a0 S.d0 =
      lam S.c0 b a S.d0 * lam c S.b0 S.a0 d

def Bridge2Condition
    {n : Nat}
    (S : Anchors n)
    (lam : Lambda n) : Prop :=
  ∀ a b,
    lam b a S.c0 S.d0 * lam S.b0 S.a0 S.c0 S.d0 =
      lam S.b0 a S.c0 S.d0 * lam b S.a0 S.c0 S.d0

def Bridge3Condition
    {n : Nat}
    (S : Anchors n)
    (lam : Lambda n) : Prop :=
  ∀ c d,
    lam S.a0 S.b0 d c * lam S.a0 S.b0 S.d0 S.c0 =
      lam S.a0 S.b0 S.d0 c * lam S.a0 S.b0 d S.c0

theorem bridge1Condition_iff_h1_swap13
    {n : Nat}
    (S : Anchors n)
    (lam : Lambda n) :
    Bridge1Condition S lam ↔ H1Condition S (swap13Lambda lam) := by
  constructor <;> intro h
  · intro a b c d hvalid
    simpa [Bridge1Condition, H1Condition, swap13Lambda] using h a b c d hvalid
  · intro a b c d hvalid
    simpa [Bridge1Condition, H1Condition, swap13Lambda] using h a b c d hvalid

theorem bridge2Condition_iff_h2_swap12
    {n : Nat}
    (S : Anchors n)
    (lam : Lambda n) :
    Bridge2Condition S lam ↔ H2Condition S (swap12Lambda lam) := by
  constructor <;> intro h
  · intro a b
    simpa [Bridge2Condition, H2Condition, swap12Lambda] using h a b
  · intro a b
    simpa [Bridge2Condition, H2Condition, swap12Lambda] using h a b

theorem bridge3Condition_iff_h3_swap34
    {n : Nat}
    (S : Anchors n)
    (lam : Lambda n) :
    Bridge3Condition S lam ↔ H3Condition S (swap34Lambda lam) := by
  constructor <;> intro h
  · intro c d
    simpa [Bridge3Condition, H3Condition, swap34Lambda] using h c d
  · intro c d
    simpa [Bridge3Condition, H3Condition, swap34Lambda] using h c d

theorem h1Condition_of_separable
    {n : Nat}
    (S : Anchors n)
    (lam : Lambda n)
    (hSep : separable lam) :
    H1Condition S lam := by
  rcases hSep with ⟨u, v, w, x, hu, hv, hw, hx, hform⟩
  intro a b c d hvalid
  have h1 : lam a b c d = u a * v b * w c * x d := hform a b c d hvalid
  have h0 : lam S.a0 S.b0 S.c0 S.d0 = u S.a0 * v S.b0 * w S.c0 * x S.d0 := by
    exact hform S.a0 S.b0 S.c0 S.d0 S.valid_anchor
  have h2 : lam a b S.c0 S.d0 = u a * v b * w S.c0 * x S.d0 := by
    exact hform a b S.c0 S.d0 (by
      intro hall
      exact S.hcd hall.2.2)
  have h3 : lam S.a0 S.b0 c d = u S.a0 * v S.b0 * w c * x d := by
    exact hform S.a0 S.b0 c d (by
      intro hall
      exact S.hab hall.1)
  simp [H1Condition, h1, h0, h2, h3, mul_assoc, mul_left_comm, mul_comm]

theorem h2Condition_of_separable
    {n : Nat}
    (S : Anchors n)
    (lam : Lambda n)
    (hSep : separable lam) :
    H2Condition S lam := by
  rcases hSep with ⟨u, v, w, x, hu, hv, hw, hx, hform⟩
  intro a b
  have h1 : lam a b S.c0 S.d0 = u a * v b * w S.c0 * x S.d0 := by
    exact hform a b S.c0 S.d0 (by
      intro hall
      exact S.hcd hall.2.2)
  have h0 : lam S.a0 S.b0 S.c0 S.d0 = u S.a0 * v S.b0 * w S.c0 * x S.d0 := by
    exact hform S.a0 S.b0 S.c0 S.d0 S.valid_anchor
  have h2 : lam a S.b0 S.c0 S.d0 = u a * v S.b0 * w S.c0 * x S.d0 := by
    exact hform a S.b0 S.c0 S.d0 (S.valid_a_slice a)
  have h3 : lam S.a0 b S.c0 S.d0 = u S.a0 * v b * w S.c0 * x S.d0 := by
    exact hform S.a0 b S.c0 S.d0 (S.valid_b_slice b)
  simp [H2Condition, h1, h0, h2, h3, mul_assoc, mul_left_comm, mul_comm]

theorem h3Condition_of_separable
    {n : Nat}
    (S : Anchors n)
    (lam : Lambda n)
    (hSep : separable lam) :
    H3Condition S lam := by
  rcases hSep with ⟨u, v, w, x, hu, hv, hw, hx, hform⟩
  intro c d
  have h1 : lam S.a0 S.b0 c d = u S.a0 * v S.b0 * w c * x d := by
    exact hform S.a0 S.b0 c d (by
      intro hall
      exact S.hab hall.1)
  have h0 : lam S.a0 S.b0 S.c0 S.d0 = u S.a0 * v S.b0 * w S.c0 * x S.d0 := by
    exact hform S.a0 S.b0 S.c0 S.d0 S.valid_anchor
  have h2 : lam S.a0 S.b0 c S.d0 = u S.a0 * v S.b0 * w c * x S.d0 := by
    exact hform S.a0 S.b0 c S.d0 (S.valid_c_slice c)
  have h3 : lam S.a0 S.b0 S.c0 d = u S.a0 * v S.b0 * w S.c0 * x d := by
    exact hform S.a0 S.b0 S.c0 d (S.valid_d_slice d)
  simp [H3Condition, h1, h0, h2, h3, mul_assoc, mul_left_comm, mul_comm]

theorem fzero_of_three_bilinear_identities
    {n : Nat}
    (S : Anchors n)
    (lam : Lambda n)
    (h1 :
      ∀ a b c d, valid a b c d →
        lam a b c d * lam S.a0 S.b0 S.c0 S.d0 =
          lam a b S.c0 S.d0 * lam S.a0 S.b0 c d)
    (h2 :
      ∀ a b,
        lam a b S.c0 S.d0 * lam S.a0 S.b0 S.c0 S.d0 =
          lam a S.b0 S.c0 S.d0 * lam S.a0 b S.c0 S.d0)
    (h3 :
      ∀ c d,
        lam S.a0 S.b0 c d * lam S.a0 S.b0 S.c0 S.d0 =
          lam S.a0 S.b0 c S.d0 * lam S.a0 S.b0 S.c0 d) :
    FZero S lam := by
  intro a b c d hvalid
  let lam0 : ℝ := lam S.a0 S.b0 S.c0 S.d0
  have h1' :
      lam a b c d * lam0 =
        lam a b S.c0 S.d0 * lam S.a0 S.b0 c d := by
    simpa [lam0] using h1 a b c d hvalid
  have h2' :
      lam a b S.c0 S.d0 * lam0 =
        lam a S.b0 S.c0 S.d0 * lam S.a0 b S.c0 S.d0 := by
    simpa [lam0] using h2 a b
  have h3' :
      lam S.a0 S.b0 c d * lam0 =
        lam S.a0 S.b0 c S.d0 * lam S.a0 S.b0 S.c0 d := by
    simpa [lam0] using h3 c d
  have hcoordEq :
      lam a b c d * lam0 ^ 3 =
        lam a S.b0 S.c0 S.d0
          * lam S.a0 b S.c0 S.d0
          * lam S.a0 S.b0 c S.d0
          * lam S.a0 S.b0 S.c0 d := by
    calc
      lam a b c d * lam0 ^ 3
          = (lam a b c d * lam0) * lam0 ^ 2 := by ring
      _ = (lam a b S.c0 S.d0 * lam S.a0 S.b0 c d) * lam0 ^ 2 := by rw [h1']
      _ = (lam a b S.c0 S.d0 * lam0) * (lam S.a0 S.b0 c d * lam0) := by ring
      _ =
          (lam a S.b0 S.c0 S.d0 * lam S.a0 b S.c0 S.d0)
            * (lam S.a0 S.b0 c S.d0 * lam S.a0 S.b0 S.c0 d) := by rw [h2', h3']
      _ =
          lam a S.b0 S.c0 S.d0
            * lam S.a0 b S.c0 S.d0
            * lam S.a0 S.b0 c S.d0
            * lam S.a0 S.b0 S.c0 d := by ring
  have hcoordZero :
      lam a b c d * lam0 ^ 3
        - (lam a S.b0 S.c0 S.d0
          * lam S.a0 b S.c0 S.d0
          * lam S.a0 S.b0 c S.d0
          * lam S.a0 S.b0 S.c0 d) = 0 := by
    linarith [hcoordEq]
  simpa [FMap, coord, lam0] using hcoordZero

theorem separable_of_three_bilinear_identities
    {n : Nat}
    (S : Anchors n)
    (lam : Lambda n)
    (hNZ : nonzeroOnValid lam)
    (h1 :
      ∀ a b c d, valid a b c d →
        lam a b c d * lam S.a0 S.b0 S.c0 S.d0 =
          lam a b S.c0 S.d0 * lam S.a0 S.b0 c d)
    (h2 :
      ∀ a b,
        lam a b S.c0 S.d0 * lam S.a0 S.b0 S.c0 S.d0 =
          lam a S.b0 S.c0 S.d0 * lam S.a0 b S.c0 S.d0)
    (h3 :
      ∀ c d,
        lam S.a0 S.b0 c d * lam S.a0 S.b0 S.c0 S.d0 =
          lam S.a0 S.b0 c S.d0 * lam S.a0 S.b0 S.c0 d) :
    separable lam := by
  have hF : FZero S lam := fzero_of_three_bilinear_identities S lam h1 h2 h3
  exact (Characterization.fzero_iff_separable S lam hNZ).1 hF

theorem h2_of_swap12_balance_triangle
    {n : Nat}
    (S : Anchors n)
    (lam : Lambda n)
    (hBal1 :
      ∀ a b,
        lam a b S.c0 S.d0 * lam S.a0 S.b0 S.c0 S.d0 =
          lam b a S.c0 S.d0 * lam S.b0 S.a0 S.c0 S.d0)
    (hBal2 :
      ∀ a b,
        lam a S.b0 S.c0 S.d0 * lam S.a0 b S.c0 S.d0 =
          lam S.b0 a S.c0 S.d0 * lam b S.a0 S.c0 S.d0)
    (hBridge :
      ∀ a b,
        lam b a S.c0 S.d0 * lam S.b0 S.a0 S.c0 S.d0 =
          lam S.b0 a S.c0 S.d0 * lam b S.a0 S.c0 S.d0) :
    ∀ a b,
      lam a b S.c0 S.d0 * lam S.a0 S.b0 S.c0 S.d0 =
        lam a S.b0 S.c0 S.d0 * lam S.a0 b S.c0 S.d0 := by
  intro a b
  calc
    lam a b S.c0 S.d0 * lam S.a0 S.b0 S.c0 S.d0
        = lam b a S.c0 S.d0 * lam S.b0 S.a0 S.c0 S.d0 := hBal1 a b
    _ = lam S.b0 a S.c0 S.d0 * lam b S.a0 S.c0 S.d0 := hBridge a b
    _ = lam a S.b0 S.c0 S.d0 * lam S.a0 b S.c0 S.d0 := by
      have h := hBal2 a b
      simpa [mul_comm] using h.symm

theorem h1_of_swap13_balance_triangle
    {n : Nat}
    (S : Anchors n)
    (lam : Lambda n)
    (hBal1 :
      ∀ a b c d, valid a b c d →
        lam a b c d * lam S.a0 S.b0 S.c0 S.d0 =
          lam c b a d * lam S.c0 S.b0 S.a0 S.d0)
    (hBal2 :
      ∀ a b c d, valid a b c d →
        lam a b S.c0 S.d0 * lam S.a0 S.b0 c d =
          lam S.c0 b a S.d0 * lam c S.b0 S.a0 d)
    (hBridge :
      ∀ a b c d, valid a b c d →
        lam c b a d * lam S.c0 S.b0 S.a0 S.d0 =
          lam S.c0 b a S.d0 * lam c S.b0 S.a0 d) :
    ∀ a b c d, valid a b c d →
      lam a b c d * lam S.a0 S.b0 S.c0 S.d0 =
        lam a b S.c0 S.d0 * lam S.a0 S.b0 c d := by
  intro a b c d hvalid
  calc
    lam a b c d * lam S.a0 S.b0 S.c0 S.d0
        = lam c b a d * lam S.c0 S.b0 S.a0 S.d0 := hBal1 a b c d hvalid
    _ = lam S.c0 b a S.d0 * lam c S.b0 S.a0 d := hBridge a b c d hvalid
    _ = lam a b S.c0 S.d0 * lam S.a0 S.b0 c d := by
      exact (hBal2 a b c d hvalid).symm

theorem h3_of_swap34_balance_triangle
    {n : Nat}
    (S : Anchors n)
    (lam : Lambda n)
    (hBal1 :
      ∀ c d,
        lam S.a0 S.b0 c d * lam S.a0 S.b0 S.c0 S.d0 =
          lam S.a0 S.b0 d c * lam S.a0 S.b0 S.d0 S.c0)
    (hBal2 :
      ∀ c d,
        lam S.a0 S.b0 c S.d0 * lam S.a0 S.b0 S.c0 d =
          lam S.a0 S.b0 S.d0 c * lam S.a0 S.b0 d S.c0)
    (hBridge :
      ∀ c d,
        lam S.a0 S.b0 d c * lam S.a0 S.b0 S.d0 S.c0 =
          lam S.a0 S.b0 S.d0 c * lam S.a0 S.b0 d S.c0) :
    ∀ c d,
      lam S.a0 S.b0 c d * lam S.a0 S.b0 S.c0 S.d0 =
        lam S.a0 S.b0 c S.d0 * lam S.a0 S.b0 S.c0 d := by
  intro c d
  calc
    lam S.a0 S.b0 c d * lam S.a0 S.b0 S.c0 S.d0
        = lam S.a0 S.b0 d c * lam S.a0 S.b0 S.d0 S.c0 := hBal1 c d
    _ = lam S.a0 S.b0 S.d0 c * lam S.a0 S.b0 d S.c0 := hBridge c d
    _ = lam S.a0 S.b0 c S.d0 * lam S.a0 S.b0 S.c0 d := by
      have h := hBal2 c d
      simpa [mul_comm] using h.symm

theorem bridge1_of_h1_and_swap13_balances
    {n : Nat}
    (S : Anchors n)
    (lam : Lambda n)
    (h1 :
      ∀ a b c d, valid a b c d →
        lam a b c d * lam S.a0 S.b0 S.c0 S.d0 =
          lam a b S.c0 S.d0 * lam S.a0 S.b0 c d)
    (hBal1 :
      ∀ a b c d, valid a b c d →
        lam a b c d * lam S.a0 S.b0 S.c0 S.d0 =
          lam c b a d * lam S.c0 S.b0 S.a0 S.d0)
    (hBal2 :
      ∀ a b c d, valid a b c d →
        lam a b S.c0 S.d0 * lam S.a0 S.b0 c d =
          lam S.c0 b a S.d0 * lam c S.b0 S.a0 d) :
    ∀ a b c d, valid a b c d →
      lam c b a d * lam S.c0 S.b0 S.a0 S.d0 =
        lam S.c0 b a S.d0 * lam c S.b0 S.a0 d := by
  intro a b c d hvalid
  calc
    lam c b a d * lam S.c0 S.b0 S.a0 S.d0
        = lam a b c d * lam S.a0 S.b0 S.c0 S.d0 := by
          exact (hBal1 a b c d hvalid).symm
    _ = lam a b S.c0 S.d0 * lam S.a0 S.b0 c d := h1 a b c d hvalid
    _ = lam S.c0 b a S.d0 * lam c S.b0 S.a0 d := hBal2 a b c d hvalid

theorem bridge2_of_h2_and_swap12_balances
    {n : Nat}
    (S : Anchors n)
    (lam : Lambda n)
    (h2 :
      ∀ a b,
        lam a b S.c0 S.d0 * lam S.a0 S.b0 S.c0 S.d0 =
          lam a S.b0 S.c0 S.d0 * lam S.a0 b S.c0 S.d0)
    (hBal1 :
      ∀ a b,
        lam a b S.c0 S.d0 * lam S.a0 S.b0 S.c0 S.d0 =
          lam b a S.c0 S.d0 * lam S.b0 S.a0 S.c0 S.d0)
    (hBal2 :
      ∀ a b,
        lam a S.b0 S.c0 S.d0 * lam S.a0 b S.c0 S.d0 =
          lam S.b0 a S.c0 S.d0 * lam b S.a0 S.c0 S.d0) :
    ∀ a b,
      lam b a S.c0 S.d0 * lam S.b0 S.a0 S.c0 S.d0 =
        lam S.b0 a S.c0 S.d0 * lam b S.a0 S.c0 S.d0 := by
  intro a b
  calc
    lam b a S.c0 S.d0 * lam S.b0 S.a0 S.c0 S.d0
        = lam a b S.c0 S.d0 * lam S.a0 S.b0 S.c0 S.d0 := by
          have h := hBal1 a b
          simpa [mul_comm] using h.symm
    _ = lam a S.b0 S.c0 S.d0 * lam S.a0 b S.c0 S.d0 := h2 a b
    _ = lam S.b0 a S.c0 S.d0 * lam b S.a0 S.c0 S.d0 := hBal2 a b

theorem bridge3_of_h3_and_swap34_balances
    {n : Nat}
    (S : Anchors n)
    (lam : Lambda n)
    (h3 :
      ∀ c d,
        lam S.a0 S.b0 c d * lam S.a0 S.b0 S.c0 S.d0 =
          lam S.a0 S.b0 c S.d0 * lam S.a0 S.b0 S.c0 d)
    (hBal1 :
      ∀ c d,
        lam S.a0 S.b0 c d * lam S.a0 S.b0 S.c0 S.d0 =
          lam S.a0 S.b0 d c * lam S.a0 S.b0 S.d0 S.c0)
    (hBal2 :
      ∀ c d,
        lam S.a0 S.b0 c S.d0 * lam S.a0 S.b0 S.c0 d =
          lam S.a0 S.b0 S.d0 c * lam S.a0 S.b0 d S.c0) :
    ∀ c d,
      lam S.a0 S.b0 d c * lam S.a0 S.b0 S.d0 S.c0 =
        lam S.a0 S.b0 S.d0 c * lam S.a0 S.b0 d S.c0 := by
  intro c d
  calc
    lam S.a0 S.b0 d c * lam S.a0 S.b0 S.d0 S.c0
        = lam S.a0 S.b0 c d * lam S.a0 S.b0 S.c0 S.d0 := by
          have h := hBal1 c d
          simpa [mul_comm] using h.symm
    _ = lam S.a0 S.b0 c S.d0 * lam S.a0 S.b0 S.c0 d := h3 c d
    _ = lam S.a0 S.b0 S.d0 c * lam S.a0 S.b0 d S.c0 := hBal2 c d

theorem bridge1_of_separable
    {n : Nat}
    (S : Anchors n)
    (lam : Lambda n)
    (hSep : separable lam) :
    ∀ a b c d, valid a b c d →
      lam c b a d * lam S.c0 S.b0 S.a0 S.d0 =
        lam S.c0 b a S.d0 * lam c S.b0 S.a0 d := by
  rcases hSep with ⟨u, v, w, x, hu, hv, hw, hx, hform⟩
  intro a b c d hvalid
  have hvalid_cbad : valid c b a d := by
    intro hall
    apply hvalid
    refine ⟨hall.2.1.symm, hall.1.symm, ?_⟩
    exact (hall.1.trans hall.2.1).trans hall.2.2
  have hvalid_c0b0a0d0 : valid S.c0 S.b0 S.a0 S.d0 := by
    intro hall
    exact S.hab hall.2.1.symm
  have hvalid_c0bad0 : valid S.c0 b a S.d0 := by
    intro hall
    exact S.hcd ((hall.1.trans hall.2.1).trans hall.2.2)
  have hvalid_cb0a0d : valid c S.b0 S.a0 d := by
    intro hall
    exact S.hab hall.2.1.symm
  have h1 : lam c b a d = u c * v b * w a * x d := by
    exact hform c b a d hvalid_cbad
  have h2 : lam S.c0 S.b0 S.a0 S.d0 = u S.c0 * v S.b0 * w S.a0 * x S.d0 := by
    exact hform S.c0 S.b0 S.a0 S.d0 hvalid_c0b0a0d0
  have h3 : lam S.c0 b a S.d0 = u S.c0 * v b * w a * x S.d0 := by
    exact hform S.c0 b a S.d0 hvalid_c0bad0
  have h4 : lam c S.b0 S.a0 d = u c * v S.b0 * w S.a0 * x d := by
    exact hform c S.b0 S.a0 d hvalid_cb0a0d
  simp [h1, h2, h3, h4, mul_assoc, mul_left_comm, mul_comm]

theorem bridge2_of_separable
    {n : Nat}
    (S : Anchors n)
    (lam : Lambda n)
    (hSep : separable lam) :
    ∀ a b,
      lam b a S.c0 S.d0 * lam S.b0 S.a0 S.c0 S.d0 =
        lam S.b0 a S.c0 S.d0 * lam b S.a0 S.c0 S.d0 := by
  rcases hSep with ⟨u, v, w, x, hu, hv, hw, hx, hform⟩
  intro a b
  have hvalid_bac0d0 : valid b a S.c0 S.d0 := by
    intro hall
    exact S.hcd hall.2.2
  have hvalid_b0a0c0d0 : valid S.b0 S.a0 S.c0 S.d0 := by
    intro hall
    exact S.hab hall.1.symm
  have hvalid_b0ac0d0 : valid S.b0 a S.c0 S.d0 := by
    intro hall
    exact S.hcd hall.2.2
  have hvalid_ba0c0d0 : valid b S.a0 S.c0 S.d0 := by
    intro hall
    exact S.hcd hall.2.2
  have h1 : lam b a S.c0 S.d0 = u b * v a * w S.c0 * x S.d0 := by
    exact hform b a S.c0 S.d0 hvalid_bac0d0
  have h2 : lam S.b0 S.a0 S.c0 S.d0 = u S.b0 * v S.a0 * w S.c0 * x S.d0 := by
    exact hform S.b0 S.a0 S.c0 S.d0 hvalid_b0a0c0d0
  have h3 : lam S.b0 a S.c0 S.d0 = u S.b0 * v a * w S.c0 * x S.d0 := by
    exact hform S.b0 a S.c0 S.d0 hvalid_b0ac0d0
  have h4 : lam b S.a0 S.c0 S.d0 = u b * v S.a0 * w S.c0 * x S.d0 := by
    exact hform b S.a0 S.c0 S.d0 hvalid_ba0c0d0
  simp [h1, h2, h3, h4, mul_assoc, mul_left_comm, mul_comm]

theorem bridge3_of_separable
    {n : Nat}
    (S : Anchors n)
    (lam : Lambda n)
    (hSep : separable lam) :
    ∀ c d,
      lam S.a0 S.b0 d c * lam S.a0 S.b0 S.d0 S.c0 =
        lam S.a0 S.b0 S.d0 c * lam S.a0 S.b0 d S.c0 := by
  rcases hSep with ⟨u, v, w, x, hu, hv, hw, hx, hform⟩
  intro c d
  have hvalid_a0b0dc : valid S.a0 S.b0 d c := by
    intro hall
    exact S.hab hall.1
  have hvalid_a0b0d0c0 : valid S.a0 S.b0 S.d0 S.c0 := by
    intro hall
    exact S.hab hall.1
  have hvalid_a0b0d0c : valid S.a0 S.b0 S.d0 c := by
    intro hall
    exact S.hab hall.1
  have hvalid_a0b0dc0 : valid S.a0 S.b0 d S.c0 := by
    intro hall
    exact S.hab hall.1
  have h1 : lam S.a0 S.b0 d c = u S.a0 * v S.b0 * w d * x c := by
    exact hform S.a0 S.b0 d c hvalid_a0b0dc
  have h2 : lam S.a0 S.b0 S.d0 S.c0 = u S.a0 * v S.b0 * w S.d0 * x S.c0 := by
    exact hform S.a0 S.b0 S.d0 S.c0 hvalid_a0b0d0c0
  have h3 : lam S.a0 S.b0 S.d0 c = u S.a0 * v S.b0 * w S.d0 * x c := by
    exact hform S.a0 S.b0 S.d0 c hvalid_a0b0d0c
  have h4 : lam S.a0 S.b0 d S.c0 = u S.a0 * v S.b0 * w d * x S.c0 := by
    exact hform S.a0 S.b0 d S.c0 hvalid_a0b0dc0
  simp [h1, h2, h3, h4, mul_assoc, mul_left_comm, mul_comm]

theorem separable_swap12
    {n : Nat}
    (lam : Lambda n)
    (hSep : separable lam) :
    separable (swap12Lambda lam) := by
  rcases hSep with ⟨u, v, w, x, hu, hv, hw, hx, hform⟩
  refine ⟨v, u, w, x, hv, hu, hw, hx, ?_⟩
  intro a b c d hvalid
  have hperm : valid b a c d := (valid_swap12_iff a b c d).2 hvalid
  simpa [swap12Lambda, mul_assoc, mul_left_comm, mul_comm] using hform b a c d hperm

theorem separable_swap13
    {n : Nat}
    (lam : Lambda n)
    (hSep : separable lam) :
    separable (swap13Lambda lam) := by
  rcases hSep with ⟨u, v, w, x, hu, hv, hw, hx, hform⟩
  refine ⟨w, v, u, x, hw, hv, hu, hx, ?_⟩
  intro a b c d hvalid
  have hperm : valid c b a d := (valid_swap13_iff a b c d).2 hvalid
  simpa [swap13Lambda, mul_assoc, mul_left_comm, mul_comm] using hform c b a d hperm

theorem separable_swap34
    {n : Nat}
    (lam : Lambda n)
    (hSep : separable lam) :
    separable (swap34Lambda lam) := by
  rcases hSep with ⟨u, v, w, x, hu, hv, hw, hx, hform⟩
  refine ⟨u, v, x, w, hu, hv, hx, hw, ?_⟩
  intro a b c d hvalid
  have hperm : valid a b d c := (valid_swap34_iff a b c d).2 hvalid
  simpa [swap34Lambda, mul_assoc, mul_left_comm, mul_comm] using hform a b d c hperm

theorem separable_swap12_iff
    {n : Nat}
    (lam : Lambda n) :
    separable (swap12Lambda lam) ↔ separable lam := by
  constructor
  · intro h
    simpa [swap12Lambda_swap12] using separable_swap12 (swap12Lambda lam) h
  · intro h
    exact separable_swap12 lam h

theorem separable_swap13_iff
    {n : Nat}
    (lam : Lambda n) :
    separable (swap13Lambda lam) ↔ separable lam := by
  constructor
  · intro h
    simpa [swap13Lambda_swap13] using separable_swap13 (swap13Lambda lam) h
  · intro h
    exact separable_swap13 lam h

theorem separable_swap34_iff
    {n : Nat}
    (lam : Lambda n) :
    separable (swap34Lambda lam) ↔ separable lam := by
  constructor
  · intro h
    simpa [swap34Lambda_swap34] using separable_swap34 (swap34Lambda lam) h
  · intro h
    exact separable_swap34 lam h

end Question9
