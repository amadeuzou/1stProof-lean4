import Question9.Bridge
import Question9.Geometry

namespace Question9

structure BilinearFamilyWitness (n m : Nat) where
  map : InputVector n → (Fin m → ℝ)
  h1_from_zero :
    ∀ S : Anchors n, ∀ A : CameraMatrices n, ∀ lam : Lambda n,
      (∀ t, map (scaleInput lam (QInput A)) t = 0) →
        ∀ a b c d, valid a b c d →
          lam a b c d * lam S.a0 S.b0 S.c0 S.d0 =
            lam a b S.c0 S.d0 * lam S.a0 S.b0 c d
  h2_from_zero :
    ∀ S : Anchors n, ∀ A : CameraMatrices n, ∀ lam : Lambda n,
      (∀ t, map (scaleInput lam (QInput A)) t = 0) →
        ∀ a b,
          lam a b S.c0 S.d0 * lam S.a0 S.b0 S.c0 S.d0 =
            lam a S.b0 S.c0 S.d0 * lam S.a0 b S.c0 S.d0
  h3_from_zero :
    ∀ S : Anchors n, ∀ A : CameraMatrices n, ∀ lam : Lambda n,
      (∀ t, map (scaleInput lam (QInput A)) t = 0) →
        ∀ c d,
          lam S.a0 S.b0 c d * lam S.a0 S.b0 S.c0 S.d0 =
            lam S.a0 S.b0 c S.d0 * lam S.a0 S.b0 S.c0 d
  zero_of_separable :
    ∀ _S : Anchors n, ∀ A : CameraMatrices n, ∀ lam : Lambda n,
      separable lam → ∀ t, map (scaleInput lam (QInput A)) t = 0

theorem separable_of_family_zero_of_bilinearWitness
    {n m : Nat}
    (W : BilinearFamilyWitness n m)
    (S : Anchors n)
    (A : CameraMatrices n)
    (lam : Lambda n)
    (hNZ : nonzeroOnValid lam)
    (hZero : ∀ t, W.map (scaleInput lam (QInput A)) t = 0) :
    separable lam := by
  exact separable_of_three_bilinear_identities S lam hNZ
    (W.h1_from_zero S A lam hZero)
    (W.h2_from_zero S A lam hZero)
    (W.h3_from_zero S A lam hZero)

theorem family_zero_iff_separable_of_bilinearWitness
    {n m : Nat}
    (W : BilinearFamilyWitness n m)
    (S : Anchors n)
    (A : CameraMatrices n)
    (lam : Lambda n)
    (hNZ : nonzeroOnValid lam) :
    (∀ t, W.map (scaleInput lam (QInput A)) t = 0) ↔ separable lam := by
  constructor
  · intro hZero
    exact separable_of_family_zero_of_bilinearWitness W S A lam hNZ hZero
  · intro hSep
    exact W.zero_of_separable S A lam hSep

end Question9
