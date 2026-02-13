import Macdonald.Hecke.Operators
import Mathlib.RingTheory.Localization.FractionRing
import Mathlib.RingTheory.MvPolynomial.Basic
import Mathlib.Algebra.MvPolynomial.CommRing

namespace Macdonald
namespace Hecke

/-!
Phase 1.2 (initial): Demazure-Lusztig operator on multivariate rational functions.

This module establishes a concrete, compilable interface for `T_i` acting on
`FractionRing (MvPolynomial (Fin n) R)`. Full Hecke relation proofs are deferred
to later phases.
-/

noncomputable section

abbrev PolyCR (n : ℕ) (R : Type*) [CommRing R] := MvPolynomial (Fin n) R

abbrev RatPoly (n : ℕ) (R : Type*) [CommRing R] [IsDomain R] :=
  FractionRing (PolyCR n R)

section BasicDefs

variable {n : ℕ} {R : Type*} [CommRing R] [IsDomain R]

instance polyCRIsDomain : IsDomain (PolyCR n R) := by infer_instance

noncomputable instance ratPolyField : Field (RatPoly n R) :=
  IsFractionRing.toField (PolyCR n R)

abbrev toRat : PolyCR n R →+* RatPoly n R :=
  algebraMap (PolyCR n R) (RatPoly n R)

abbrev coeffToRat : R →+* RatPoly n R :=
  toRat.comp MvPolynomial.C

def ratVar (i : Fin n) : RatPoly n R :=
  toRat (MvPolynomial.X i)

def nextFin (i : Fin n) (h : i.1 + 1 < n) : Fin n :=
  ⟨i.1 + 1, h⟩

def permuteRat (σ : Equiv.Perm (Fin n)) : RatPoly n R ≃+* RatPoly n R :=
  IsFractionRing.ringEquivOfRingEquiv
    (A := PolyCR n R) (K := RatPoly n R) (B := PolyCR n R) (L := RatPoly n R)
    (MvPolynomial.renameEquiv R σ).toRingEquiv

@[simp] theorem permuteRat_toRat (σ : Equiv.Perm (Fin n)) (p : PolyCR n R) :
    permuteRat σ (toRat p) = toRat (MvPolynomial.rename σ p) := by
  simpa [permuteRat, toRat] using
    (IsFractionRing.ringEquivOfRingEquiv_algebraMap
      (A := PolyCR n R) (K := RatPoly n R)
      (B := PolyCR n R) (L := RatPoly n R)
      (h := (MvPolynomial.renameEquiv R σ).toRingEquiv) p)

def adjacentPermuteRat (i : Fin n) (h : i.1 + 1 < n) :
    RatPoly n R ≃+* RatPoly n R :=
  permuteRat (adjacentSwap i h)

def demazureDenom (i : Fin n) (h : i.1 + 1 < n) : RatPoly n R :=
  1 - ratVar i / ratVar (nextFin i h)

def demazureLusztig (t : R) (i : Fin n) (h : i.1 + 1 < n) :
    RatPoly n R → RatPoly n R := fun f =>
  let s := adjacentPermuteRat i h
  let sf := s f
  let tR : RatPoly n R := coeffToRat t
  let tm1R : RatPoly n R := coeffToRat (t - 1)
  tR * sf + tm1R * ((f - sf) / demazureDenom i h)

@[simp] theorem nextFin_val (i : Fin n) (h : i.1 + 1 < n) :
    (nextFin i h).1 = i.1 + 1 := rfl

@[simp] theorem adjacentPermuteRat_apply
    (i : Fin n) (h : i.1 + 1 < n) (f : RatPoly n R) :
    adjacentPermuteRat i h f = permuteRat (adjacentSwap i h) f := rfl

@[simp] theorem permuteRat_ratVar
    (σ : Equiv.Perm (Fin n)) (i : Fin n) :
    permuteRat (n := n) (R := R) σ (ratVar (n := n) (R := R) i) =
      ratVar (n := n) (R := R) (σ i) := by
  simp [ratVar]

@[simp] theorem adjacentPermuteRat_ratVar_left
    (i : Fin n) (h : i.1 + 1 < n) :
    adjacentPermuteRat (n := n) (R := R) i h (ratVar (n := n) (R := R) i) =
      ratVar (n := n) (R := R) (nextFin i h) := by
  simpa [nextFin] using
    (permuteRat_ratVar (n := n) (R := R) (σ := adjacentSwap i h) (i := i))

@[simp] theorem adjacentPermuteRat_ratVar_right
    (i : Fin n) (h : i.1 + 1 < n) :
    adjacentPermuteRat (n := n) (R := R) i h (ratVar (n := n) (R := R) (nextFin i h)) =
      ratVar (n := n) (R := R) i := by
  simpa [nextFin] using
    (permuteRat_ratVar (n := n) (R := R) (σ := adjacentSwap i h) (i := nextFin i h))

@[simp] theorem demazureLusztig_apply
    (t : R) (i : Fin n) (h : i.1 + 1 < n) (f : RatPoly n R) :
    demazureLusztig t i h f =
      let s := adjacentPermuteRat i h
      let sf := s f
      let tR : RatPoly n R := coeffToRat t
      let tm1R : RatPoly n R := coeffToRat (t - 1)
      tR * sf + tm1R * ((f - sf) / demazureDenom i h) := rfl

@[simp] theorem demazureLusztig_zero
    (t : R) (i : Fin n) (h : i.1 + 1 < n) :
    demazureLusztig t i h 0 = 0 := by
  simp [demazureLusztig]

@[simp] theorem adjacentPermuteRat_involutive
    (i : Fin n) (h : i.1 + 1 < n) (f : RatPoly n R) :
    adjacentPermuteRat i h (adjacentPermuteRat i h f) = f := by
  exact (adjacentPermuteRat i h).left_inv f

@[simp] theorem adjacentPermuteRat_denom
    (i : Fin n) (h : i.1 + 1 < n) :
    adjacentPermuteRat (n := n) (R := R) i h (demazureDenom i h) =
      1 - ratVar (n := n) (R := R) (nextFin i h) / ratVar (n := n) (R := R) i := by
  unfold demazureDenom
  simp [nextFin]

@[simp] theorem demazureLusztig_one
    (i : Fin n) (h : i.1 + 1 < n) (f : RatPoly n R) :
    demazureLusztig (R := R) 1 i h f = adjacentPermuteRat i h f := by
  simp [demazureLusztig]

theorem demazureLusztig_of_invariant
    (t : R) (i : Fin n) (h : i.1 + 1 < n) (f : RatPoly n R)
    (hs : adjacentPermuteRat i h f = f) :
    demazureLusztig t i h f = coeffToRat (n := n) (R := R) t * f := by
  simp [demazureLusztig, hs]

theorem coeffToRat_t_sub_one_add_one
    (t : R) :
    coeffToRat (n := n) (R := R) (t - 1) + (1 : RatPoly n R) =
      coeffToRat (n := n) (R := R) t := by
  calc
    coeffToRat (n := n) (R := R) (t - 1) + (1 : RatPoly n R)
      = coeffToRat (n := n) (R := R) (t - 1) + coeffToRat (n := n) (R := R) (1 : R) := by
          simp [coeffToRat]
    _ = coeffToRat (n := n) (R := R) ((t - 1) + 1) := by
          rw [← RingHom.map_add]
    _ = coeffToRat (n := n) (R := R) t := by
          simp [sub_eq_add_neg, add_assoc]

theorem demazureLusztig_quadratic_on_invariant
    (t : R) (i : Fin n) (h : i.1 + 1 < n) (f : RatPoly n R)
    (hs : adjacentPermuteRat i h f = f) :
    demazureLusztig t i h (demazureLusztig t i h f) =
      (coeffToRat (n := n) (R := R) (t - 1)) * demazureLusztig t i h f +
      (coeffToRat (n := n) (R := R) t) * f := by
  have hT : demazureLusztig t i h f = coeffToRat (n := n) (R := R) t * f :=
    demazureLusztig_of_invariant (t := t) (i := i) (h := h) (f := f) hs
  have hsT : adjacentPermuteRat i h (demazureLusztig t i h f) = demazureLusztig t i h f := by
    calc
      adjacentPermuteRat i h (demazureLusztig t i h f)
        = adjacentPermuteRat i h (coeffToRat (n := n) (R := R) t * f) := by
            exact congrArg (adjacentPermuteRat i h) hT
      _ = adjacentPermuteRat i h (coeffToRat (n := n) (R := R) t) * adjacentPermuteRat i h f := by
            simp
      _ = coeffToRat (n := n) (R := R) t * f := by
            simpa [hs]
      _ = demazureLusztig t i h f := hT.symm
  have hTT :
      demazureLusztig t i h (demazureLusztig t i h f) =
        coeffToRat (n := n) (R := R) t * demazureLusztig t i h f :=
    demazureLusztig_of_invariant
      (t := t) (i := i) (h := h) (f := demazureLusztig t i h f) hsT
  calc
    demazureLusztig t i h (demazureLusztig t i h f)
      = coeffToRat (n := n) (R := R) t * demazureLusztig t i h f := hTT
    _ = ((coeffToRat (n := n) (R := R) (t - 1)) + 1) * demazureLusztig t i h f := by
          rw [coeffToRat_t_sub_one_add_one (n := n) (R := R) t]
    _ = (coeffToRat (n := n) (R := R) (t - 1)) * demazureLusztig t i h f +
        demazureLusztig t i h f := by
          rw [add_mul, one_mul]
    _ = (coeffToRat (n := n) (R := R) (t - 1)) * demazureLusztig t i h f +
        (coeffToRat (n := n) (R := R) t) * f := by
          exact congrArg
            (fun u => (coeffToRat (n := n) (R := R) (t - 1)) * demazureLusztig t i h f + u) hT

/-- `f` is invariant under the adjacent swap `s_i`. -/
def AdjacentInvariant (i : Fin n) (h : i.1 + 1 < n) (f : RatPoly n R) : Prop :=
  adjacentPermuteRat i h f = f

/--
Quadratic relation for `T_i` restricted to the adjacent-invariant subspace.
-/
def HeckeQuadraticOnInvariant (t : R) (i : Fin n) (h : i.1 + 1 < n) : Prop :=
  ∀ f, AdjacentInvariant (n := n) (R := R) i h f →
    demazureLusztig t i h (demazureLusztig t i h f) =
      (coeffToRat (n := n) (R := R) (t - 1)) * demazureLusztig t i h f +
      (coeffToRat (n := n) (R := R) t) * f

theorem demazureLusztig_satisfies_quadratic_on_invariant
    (t : R) (i : Fin n) (h : i.1 + 1 < n) :
    HeckeQuadraticOnInvariant (n := n) (R := R) t i h := by
  intro f hs
  exact demazureLusztig_quadratic_on_invariant (t := t) (i := i) (h := h) (f := f) hs

/-- Expanded quadratic relation `(T_i - t)(T_i + 1)=0` in operator form. -/
def HeckeQuadraticRelation (t : R) (T : RatPoly n R → RatPoly n R) : Prop :=
  ∀ f,
    T (T f) =
      (coeffToRat (n := n) (R := R) (t - 1)) * T f +
      (coeffToRat (n := n) (R := R) t) * f

def DemazureLusztigSatisfiesQuadratic
    (t : R) (i : Fin n) (h : i.1 + 1 < n) : Prop :=
  HeckeQuadraticRelation (R := R) t (demazureLusztig t i h)

theorem demazureLusztig_satisfies_quadratic_of_all_invariant
    (t : R) (i : Fin n) (h : i.1 + 1 < n)
    (hInv : ∀ f : RatPoly n R, AdjacentInvariant (n := n) (R := R) i h f) :
    DemazureLusztigSatisfiesQuadratic (n := n) (R := R) t i h := by
  intro f
  exact demazureLusztig_quadratic_on_invariant
    (t := t) (i := i) (h := h) (f := f) (hInv f)

end BasicDefs

end

end Hecke
end Macdonald
