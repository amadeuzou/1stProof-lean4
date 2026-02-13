import Question9.Characterization

namespace Question9

open Anchors
open Characterization

abbrev Entry4 := Fin 3 → Fin 3 → Fin 3 → Fin 3 → ℝ
abbrev TensorField (n : Nat) := Idx n → Idx n → Idx n → Idx n → Entry4

def i0 : Fin 3 := ⟨0, by decide⟩

noncomputable def extractLambda {n : Nat} (Q X : TensorField n) : Lambda n :=
  fun a b c d => X a b c d i0 i0 i0 i0 / Q a b c d i0 i0 i0 i0

theorem extractLambda_eq
    {n : Nat}
    (Q X : TensorField n)
    (lam : Lambda n)
    (hScale :
      ∀ a b c d, valid a b c d →
        X a b c d i0 i0 i0 i0 = lam a b c d * Q a b c d i0 i0 i0 i0)
    (hQNZ :
      ∀ a b c d, valid a b c d → Q a b c d i0 i0 i0 i0 ≠ 0)
    :
    ∀ a b c d, valid a b c d → extractLambda Q X a b c d = lam a b c d := by
  intro a b c d hvalid
  unfold extractLambda
  have hq : Q a b c d i0 i0 i0 i0 ≠ 0 := hQNZ a b c d hvalid
  have hsc := hScale a b c d hvalid
  rw [hsc]
  simpa [mul_comm] using (mul_div_cancel_left₀ (lam a b c d) hq)

theorem extract_nonzeroOnValid
    {n : Nat}
    (Q X : TensorField n)
    (lam : Lambda n)
    (hScale :
      ∀ a b c d, valid a b c d →
        X a b c d i0 i0 i0 i0 = lam a b c d * Q a b c d i0 i0 i0 i0)
    (hQNZ :
      ∀ a b c d, valid a b c d → Q a b c d i0 i0 i0 i0 ≠ 0)
    (hlamNZ : nonzeroOnValid lam) :
    nonzeroOnValid (extractLambda Q X) := by
  intro a b c d hvalid
  have heq := extractLambda_eq Q X lam hScale hQNZ a b c d hvalid
  rw [heq]
  exact hlamNZ a b c d hvalid

theorem scaledQ_characterization
    {n : Nat}
    (S : Anchors n)
    (Q X : TensorField n)
    (lam : Lambda n)
    (hScale :
      ∀ a b c d, valid a b c d →
        X a b c d i0 i0 i0 i0 = lam a b c d * Q a b c d i0 i0 i0 i0)
    (hQNZ :
      ∀ a b c d, valid a b c d → Q a b c d i0 i0 i0 i0 ≠ 0)
    (hlamNZ : nonzeroOnValid lam) :
    FZero S (extractLambda Q X) ↔ separable (extractLambda Q X) := by
  exact Characterization.fzero_iff_separable S (extractLambda Q X)
    (extract_nonzeroOnValid Q X lam hScale hQNZ hlamNZ)

end Question9
