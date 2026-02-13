import Equivariant.Spectra.Orthogonal

namespace Equivariant

universe u w

variable {G : Type u} [Group G]

/-- Abstract family of subgroups used in isotropy separation. -/
structure SubgroupFamily (G : Type u) [Group G] where
  contains : Subgroup G → Prop
  closed_under_subgroup :
    ∀ {H K : Subgroup G}, contains K → H ≤ K → contains H

/--
Data for geometric fixed points and isotropy separation on orthogonal `G`-spectra.
This is the interface target for future concrete homotopy-theoretic implementation.
-/
structure IsotropySeparationData (G : Type u) [Group G] where
  spectrum : Type w
  smash : spectrum → spectrum → spectrum
  phi : Subgroup G → spectrum → spectrum
  eFamily : SubgroupFamily G → spectrum
  eTildeFamily : SubgroupFamily G → spectrum
  cofiber : spectrum → spectrum → spectrum
  isotropy_cofiber :
    ∀ (F : SubgroupFamily G) (X : spectrum),
      cofiber (smash (eFamily F) X) X = smash (eTildeFamily F) X
  phi_preserves_smash :
    ∀ (H : Subgroup G) (X Y : spectrum),
      phi H (smash X Y) = smash (phi H X) (phi H Y)
  phi_preserves_cofiber :
    ∀ (H : Subgroup G) (A B : spectrum),
      phi H (cofiber A B) = cofiber (phi H A) (phi H B)

/-- The isotropy cofiber equation after applying geometric fixed points. -/
theorem phi_isotropy_cofiber (D : IsotropySeparationData G)
    (H : Subgroup G) (F : SubgroupFamily G) (X : D.spectrum) :
    D.cofiber (D.smash (D.phi H (D.eFamily F)) (D.phi H X)) (D.phi H X) =
      D.smash (D.phi H (D.eTildeFamily F)) (D.phi H X) := by
  calc
    D.cofiber (D.smash (D.phi H (D.eFamily F)) (D.phi H X)) (D.phi H X)
        = D.cofiber (D.phi H (D.smash (D.eFamily F) X)) (D.phi H X) := by
            rw [D.phi_preserves_smash H (D.eFamily F) X]
    _ = D.phi H (D.cofiber (D.smash (D.eFamily F) X) X) := by
          rw [D.phi_preserves_cofiber H (D.smash (D.eFamily F) X) X]
    _ = D.phi H (D.smash (D.eTildeFamily F) X) := by
          rw [D.isotropy_cofiber F X]
    _ = D.smash (D.phi H (D.eTildeFamily F)) (D.phi H X) := by
          rw [D.phi_preserves_smash H (D.eTildeFamily F) X]

/-- Geometric fixed points preserve the isotropy-separation cofiber equation pointwise. -/
theorem phi_isotropy_cofiber_forall (D : IsotropySeparationData G)
    (F : SubgroupFamily G) (X : D.spectrum) :
    ∀ H : Subgroup G,
      D.cofiber (D.smash (D.phi H (D.eFamily F)) (D.phi H X)) (D.phi H X) =
        D.smash (D.phi H (D.eTildeFamily F)) (D.phi H X) := by
  intro H
  exact phi_isotropy_cofiber D H F X

/-- Auxiliary notion: `X` is isotropy-separated with respect to a family `F`. -/
def IsIsotropySeparated (D : IsotropySeparationData G)
    (F : SubgroupFamily G) (X : D.spectrum) : Prop :=
  D.cofiber (D.smash (D.eFamily F) X) X = D.smash (D.eTildeFamily F) X

theorem isIsotropySeparated_iff (D : IsotropySeparationData G)
    (F : SubgroupFamily G) (X : D.spectrum) :
    IsIsotropySeparated D F X := by
  unfold IsIsotropySeparated
  exact D.isotropy_cofiber F X

/--
Orthogonality-style interface: after applying `Φ^H`, smashing with the
family part acts as identity on `Φ^H X`.
-/
def IsPhiFamilyOrthogonal (D : IsotropySeparationData G)
    (H : Subgroup G) (F : SubgroupFamily G) (X : D.spectrum) : Prop :=
  D.smash (D.phi H (D.eFamily F)) (D.phi H X) = D.phi H X

theorem phi_of_isIsotropySeparated (D : IsotropySeparationData G)
    (H : Subgroup G) (F : SubgroupFamily G) (X : D.spectrum)
    (hSep : IsIsotropySeparated D F X) :
    D.phi H (D.cofiber (D.smash (D.eFamily F) X) X) =
      D.phi H (D.smash (D.eTildeFamily F) X) := by
  exact congrArg (D.phi H) hSep

theorem phi_preserves_isIsotropySeparated (D : IsotropySeparationData G)
    (H : Subgroup G) (F : SubgroupFamily G) (X : D.spectrum)
    (hSep : IsIsotropySeparated D F X) :
    D.cofiber (D.smash (D.phi H (D.eFamily F)) (D.phi H X)) (D.phi H X) =
      D.smash (D.phi H (D.eTildeFamily F)) (D.phi H X) := by
  calc
    D.cofiber (D.smash (D.phi H (D.eFamily F)) (D.phi H X)) (D.phi H X)
        = D.phi H (D.cofiber (D.smash (D.eFamily F) X) X) := by
            symm
            rw [D.phi_preserves_cofiber H (D.smash (D.eFamily F) X) X]
            rw [D.phi_preserves_smash H (D.eFamily F) X]
    _ = D.phi H (D.smash (D.eTildeFamily F) X) :=
          phi_of_isIsotropySeparated D H F X hSep
    _ = D.smash (D.phi H (D.eTildeFamily F)) (D.phi H X) := by
          rw [D.phi_preserves_smash H (D.eTildeFamily F) X]

theorem phi_preserves_isIsotropySeparated_forall (D : IsotropySeparationData G)
    (F : SubgroupFamily G) (X : D.spectrum)
    (hSep : IsIsotropySeparated D F X) :
    ∀ H : Subgroup G,
      D.cofiber (D.smash (D.phi H (D.eFamily F)) (D.phi H X)) (D.phi H X) =
        D.smash (D.phi H (D.eTildeFamily F)) (D.phi H X) := by
  intro H
  exact phi_preserves_isIsotropySeparated D H F X hSep

theorem cofiber_diagonal_of_phiFamilyOrthogonal (D : IsotropySeparationData G)
    (H : Subgroup G) (F : SubgroupFamily G) (X : D.spectrum)
    (hOrth : IsPhiFamilyOrthogonal D H F X) :
    D.cofiber (D.phi H X) (D.phi H X) =
      D.smash (D.phi H (D.eTildeFamily F)) (D.phi H X) := by
  calc
    D.cofiber (D.phi H X) (D.phi H X)
        = D.cofiber (D.smash (D.phi H (D.eFamily F)) (D.phi H X)) (D.phi H X) := by
            exact congrArg (fun A => D.cofiber A (D.phi H X)) hOrth.symm
    _ = D.smash (D.phi H (D.eTildeFamily F)) (D.phi H X) := by
          exact phi_isotropy_cofiber D H F X

end Equivariant
