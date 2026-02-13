import Question9.ScaledQ
import Question9.Plucker
import Question9.Bridge
import Question9.BilinearWitness

namespace Question9

structure PluckerFamilyWitness (n m : Nat) where
  patterns : Fin m → PluckerPattern n
  patternValid : ∀ t, PatternValid (patterns t)
  patternAligned : ∀ t, ModeAligned (patterns t)
  base_zero : ∀ A : CameraMatrices n, ∀ t, pluckerRel (QInput A) (patterns t) = 0
  h1_from_zero :
    ∀ S : Anchors n, ∀ A : CameraMatrices n, ∀ lam : Lambda n,
      (∀ t, pluckerMap patterns (scaleInput lam (QInput A)) t = 0) →
        ∀ a b c d, valid a b c d →
          lam a b c d * lam S.a0 S.b0 S.c0 S.d0 =
            lam a b S.c0 S.d0 * lam S.a0 S.b0 c d
  h2_from_zero :
    ∀ S : Anchors n, ∀ A : CameraMatrices n, ∀ lam : Lambda n,
      (∀ t, pluckerMap patterns (scaleInput lam (QInput A)) t = 0) →
        ∀ a b,
          lam a b S.c0 S.d0 * lam S.a0 S.b0 S.c0 S.d0 =
            lam a S.b0 S.c0 S.d0 * lam S.a0 b S.c0 S.d0
  h3_from_zero :
    ∀ S : Anchors n, ∀ A : CameraMatrices n, ∀ lam : Lambda n,
      (∀ t, pluckerMap patterns (scaleInput lam (QInput A)) t = 0) →
        ∀ c d,
          lam S.a0 S.b0 c d * lam S.a0 S.b0 S.c0 S.d0 =
            lam S.a0 S.b0 c S.d0 * lam S.a0 S.b0 S.c0 d

def familyMap {n m : Nat} (W : PluckerFamilyWitness n m) (Y : InputVector n) : Fin m → ℝ :=
  pluckerMap W.patterns Y

theorem familyMap_degree_uniform {n m : Nat} (_W : PluckerFamilyWitness n m) :
    pluckerCoordinateDegree = 2 := by
  exact pluckerCoordinateDegree_eq

def PluckerFamilyWitness.toBilinearWitness
    {n m : Nat}
    (W : PluckerFamilyWitness n m) : BilinearFamilyWitness n m where
  map := familyMap W
  h1_from_zero := by
    intro S A lam hZero a b c d hvalid
    exact W.h1_from_zero S A lam (by simpa [familyMap] using hZero) a b c d hvalid
  h2_from_zero := by
    intro S A lam hZero a b
    exact W.h2_from_zero S A lam (by simpa [familyMap] using hZero) a b
  h3_from_zero := by
    intro S A lam hZero c d
    exact W.h3_from_zero S A lam (by simpa [familyMap] using hZero) c d
  zero_of_separable := by
    intro S A lam hSep t
    have hRel : ∀ t, pluckerRel (scaleInput lam (QInput A)) (W.patterns t) = 0 := by
      exact plucker_forward_of_separable_for_family W.patterns lam (QInput A)
        hSep W.patternValid W.patternAligned (W.base_zero A)
    simpa [familyMap, pluckerMap] using hRel t

theorem scaled_q_iff_separable_of_witness
    {n m : Nat}
    (W : PluckerFamilyWitness n m)
    (S : Anchors n)
    (A : CameraMatrices n)
    (lam : Lambda n)
    (hLamNZ : nonzeroOnValid lam) :
    (∀ t, familyMap W (scaleInput lam (QInput A)) t = 0) ↔ separable lam := by
  simpa [PluckerFamilyWitness.toBilinearWitness, familyMap] using
    (family_zero_iff_separable_of_bilinearWitness
      (W := W.toBilinearWitness) S A lam hLamNZ)

end Question9
