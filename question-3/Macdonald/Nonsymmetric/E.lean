import Macdonald.Conventions
import Macdonald.Hecke.DemazureLusztig

namespace Macdonald
namespace Nonsymmetric

open Conventions
open Hecke

noncomputable section

abbrev Composition (n : ℕ) := Conventions.Composition n

abbrev RatPoly (n : ℕ) (R : Type*) [CommRing R] [IsDomain R] :=
  Hecke.RatPoly n R

section CherednikInterfaces

variable {n : ℕ} {R : Type*} [CommRing R] [IsDomain R]

/-- Abstract interface for a commuting family of Cherednik-type operators. -/
structure CherednikSystem where
  Y : Fin n → RatPoly n R → RatPoly n R
  commute : ∀ i j f, Y i (Y j f) = Y j (Y i f)

def IsEigenvector
    (Y : RatPoly n R → RatPoly n R)
    (eigenvalue : RatPoly n R) (f : RatPoly n R) : Prop :=
  Y f = eigenvalue * f

/--
Interface for a family `E_μ` of nonsymmetric Macdonald polynomials:
each `E_μ` is a simultaneous eigenvector of all `Y_i`.
-/
structure NonsymmetricMacdonaldFamily (sys : CherednikSystem (n := n) (R := R)) where
  E : Composition n → RatPoly n R
  eigenvalue : Composition n → Fin n → RatPoly n R
  eigen_eq : ∀ μ i, IsEigenvector (sys.Y i) (eigenvalue μ i) (E μ)

theorem eigen_eq_apply
    (sys : CherednikSystem (n := n) (R := R))
    (fam : NonsymmetricMacdonaldFamily (n := n) (R := R) sys)
    (μ : Composition n) (i : Fin n) :
    sys.Y i (fam.E μ) = fam.eigenvalue μ i * fam.E μ :=
  fam.eigen_eq μ i

end CherednikInterfaces

section QOneExchange

variable {n : ℕ} {R : Type*} [CommRing R] [IsDomain R]

def nextIndex (i : Fin n) (h : i.1 + 1 < n) : Fin n := ⟨i.1 + 1, h⟩

def swapComposition (μ : Composition n) (i : Fin n) (h : i.1 + 1 < n) : Composition n := fun j =>
  if j = i then
    μ (nextIndex i h)
  else if j = nextIndex i h then
    μ i
  else
    μ j

def exchangeRatio (t : R) (i : Fin n) (h : i.1 + 1 < n) : RatPoly n R :=
  ((coeffToRat (n := n) (R := R) t) * ratVar (n := n) (R := R) i -
      ratVar (n := n) (R := R) (nextIndex i h)) /
    (ratVar (n := n) (R := R) i -
      (coeffToRat (n := n) (R := R) t) * ratVar (n := n) (R := R) (nextIndex i h))

/--
`q = 1` local exchange interface used by the ASEP bridge:
weights transform by an explicit local ratio under an adjacent swap.
-/
def ExchangeRelationQOne
    (weight : Composition n → RatPoly n R) (t : R) : Prop :=
  ∀ μ (i : Fin n) (h : i.1 + 1 < n), μ i > μ (nextIndex i h) →
    weight (swapComposition μ i h) = exchangeRatio (n := n) (R := R) t i h * weight μ

theorem exchange_relation_apply
    (weight : Composition n → RatPoly n R) (t : R)
    (hEx : ExchangeRelationQOne (n := n) (R := R) weight t)
    (μ : Composition n) (i : Fin n) (h : i.1 + 1 < n)
    (hgt : μ i > μ (nextIndex i h)) :
    weight (swapComposition μ i h) = exchangeRatio (n := n) (R := R) t i h * weight μ :=
  hEx μ i h hgt

def zeroFinTwo : Fin 2 := ⟨0, by decide⟩

def oneFinTwo : Fin 2 := ⟨1, by decide⟩

lemma fin2_eq_zero_of_succ_lt_two (i : Fin 2) (h : i.1 + 1 < 2) :
    i = zeroFinTwo := by
  apply Fin.ext
  have hs : Nat.succ i.1 ≤ 1 := by
    simpa [Nat.succ_eq_add_one] using (Nat.lt_succ_iff.mp h)
  exact Nat.lt_one_iff.mp (Nat.succ_le_iff.mp hs)

/--
Canonical explicit two-site `q = 1` weight model:
the descending state has weight `1`, the ascending state has weight `exchangeRatio`.
-/
def twoSiteCanonicalWeight (t : R) : Composition 2 → RatPoly 2 R := fun μ =>
  if μ zeroFinTwo > μ oneFinTwo then
    1
  else
    exchangeRatio (n := 2) (R := R) t zeroFinTwo (by decide)

theorem exchangeRelationQOne_twoSiteCanonical
    (t : R) :
    ExchangeRelationQOne (n := 2) (R := R) (twoSiteCanonicalWeight (R := R) t) t := by
  intro μ i h hgt
  have hi : i = zeroFinTwo := fin2_eq_zero_of_succ_lt_two i h
  subst hi
  have hnext : nextIndex zeroFinTwo h = oneFinTwo := by
    apply Fin.ext
    simp [nextIndex, zeroFinTwo, oneFinTwo]
  have hgt01 : μ (0 : Fin 2) > μ (1 : Fin 2) := by
    simpa [hnext] using hgt
  have hlt10 : μ (1 : Fin 2) < μ (0 : Fin 2) := hgt01
  have hnot01 : ¬ μ (0 : Fin 2) < μ (1 : Fin 2) := not_lt_of_ge (le_of_lt hgt01)
  simp [twoSiteCanonicalWeight, swapComposition, nextIndex, zeroFinTwo, oneFinTwo,
    hlt10, hnot01]

end QOneExchange

theorem q_specialization_locked :
    Conventions.chosenQSpecialization = .qOne :=
  Conventions.chosen_q_is_qOne

end
end Nonsymmetric
end Macdonald
