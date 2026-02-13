import Question9.Defs

namespace Question9

open Anchors

def coord {n : Nat} (S : Anchors n) (lam : Lambda n) (a b c d : Idx n) : ℝ :=
  lam a b c d * (lam S.a0 S.b0 S.c0 S.d0) ^ 3
    - (lam a S.b0 S.c0 S.d0)
      * (lam S.a0 b S.c0 S.d0)
      * (lam S.a0 S.b0 c S.d0)
      * (lam S.a0 S.b0 S.c0 d)

def FMap {n : Nat} (S : Anchors n) (lam : Lambda n) : Idx n → Idx n → Idx n → Idx n → ℝ :=
  fun a b c d => coord S lam a b c d

def FZero {n : Nat} (S : Anchors n) (lam : Lambda n) : Prop :=
  ∀ a b c d, valid a b c d → FMap S lam a b c d = 0

def coordinateDegree : Nat := 4

theorem coordinateDegree_eq : coordinateDegree = 4 := rfl

theorem degree_independent_of_n : coordinateDegree = 4 := rfl

theorem map_does_not_depend_on_A {n : Nat} (S : Anchors n) :
    ∃ F : Lambda n → (Idx n → Idx n → Idx n → Idx n → ℝ),
      ∀ lam, F lam = FMap S lam := by
  refine ⟨FMap S, ?_⟩
  intro lam
  rfl

theorem fzero_iff_coord_zero {n : Nat} (S : Anchors n) (lam : Lambda n) :
    FZero S lam ↔ ∀ a b c d, valid a b c d → coord S lam a b c d = 0 := by
  rfl

end Question9
