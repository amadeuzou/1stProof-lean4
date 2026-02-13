import Equivariant.Spectra.Definition
import Mathlib.Algebra.Group.Subgroup.Defs
import Mathlib.Data.Sigma.Basic

namespace Equivariant

universe u

variable {G : Type u} [Group G]

/--
Levelwise geometric fixed points for the lightweight orthogonal-spectrum model.
The resulting object keeps the same ambient group with a trivial action.
-/
def GeometricFixedPoints (H : Subgroup G) (X : OrthogonalSpectrum G) :
    OrthogonalSpectrum G where
  level := fun n => {x : X.level n // ∀ h : H, X.gAction n h x = x}
  gAction := fun _ _ x => x
  structMap := fun n x =>
    ⟨X.structMap n x.1, by
      intro h
      have hx : X.gAction n h x.1 = x.1 := x.2 h
      calc
        X.gAction (n + 1) h (X.structMap n x.1)
            = X.structMap n (X.gAction n h x.1) := by
                simpa using (X.structMap_equivariant n h x.1).symm
        _ = X.structMap n x.1 := by simp [hx]⟩
  gAction_one := by
    intro n x
    rfl
  gAction_mul := by
    intro n g h x
    rfl
  structMap_equivariant := by
    intro n g x
    rfl

theorem geometricFixedPoints_susp (H : Subgroup G) (X : OrthogonalSpectrum G) :
    GeometricFixedPoints (G := G) H (SuspSpectrum X) =
      SuspSpectrum (G := G) (GeometricFixedPoints (G := G) H X) := by
  rfl

/--
Levelwise fixed-point equivalence for the zero spectrum:
fixed points of the zero object are levelwise equivalent to the zero object.
-/
def geometricFixedPoints_zero_levelEquiv
    (H : Subgroup G) (n : ℕ) :
    (GeometricFixedPoints (G := G) H (ZeroSpectrum G)).level n ≃
      (ZeroSpectrum G).level n where
  toFun := fun _ => PUnit.unit
  invFun := fun _ => ⟨PUnit.unit, by intro h; rfl⟩
  left_inv := by
    intro z
    apply Subtype.ext
    rfl
  right_inv := by
    intro z
    cases z
    rfl

def geometricFixedPoints_zero_levelwiseEquiv
    (H : Subgroup G) :
    LevelwiseEquiv
      (GeometricFixedPoints (G := G) H (ZeroSpectrum G))
      (ZeroSpectrum G) := by
  intro n
  exact geometricFixedPoints_zero_levelEquiv (G := G) H n

/--
Levelwise fixed-point decomposition for cofibers:
fixed points of a disjoint sum are a disjoint sum of fixed points.
-/
def geometricFixedPoints_cofiber_levelEquiv
    (H : Subgroup G) (X Y : OrthogonalSpectrum G) (n : ℕ) :
    (GeometricFixedPoints (G := G) H (CofiberSpectrum X Y)).level n ≃
      ((GeometricFixedPoints (G := G) H X).level n ⊕
        (GeometricFixedPoints (G := G) H Y).level n) where
  toFun z := by
    rcases z with ⟨z, hz⟩
    cases z with
    | inl x =>
        exact Sum.inl ⟨x, by
          intro h
          have hz' := hz h
          simpa [CofiberSpectrum, OrthogonalSpectrum.cofiber] using hz'⟩
    | inr y =>
        exact Sum.inr ⟨y, by
          intro h
          have hz' := hz h
          simpa [CofiberSpectrum, OrthogonalSpectrum.cofiber] using hz'⟩
  invFun s := by
    cases s with
    | inl x =>
        refine ⟨Sum.inl x.1, ?_⟩
        intro h
        simpa [CofiberSpectrum, OrthogonalSpectrum.cofiber]
          using congrArg (fun t => (Sum.inl t : X.level n ⊕ Y.level n)) (x.2 h)
    | inr y =>
        refine ⟨Sum.inr y.1, ?_⟩
        intro h
        simpa [CofiberSpectrum, OrthogonalSpectrum.cofiber]
          using congrArg (fun t => (Sum.inr t : X.level n ⊕ Y.level n)) (y.2 h)
  left_inv z := by
    rcases z with ⟨z, hz⟩
    cases z with
    | inl x =>
        apply Subtype.ext
        rfl
    | inr y =>
        apply Subtype.ext
        rfl
  right_inv s := by
    cases s with
    | inl x =>
        apply congrArg Sum.inl
        apply Subtype.ext
        rfl
    | inr y =>
        apply congrArg Sum.inr
        apply Subtype.ext
        rfl

def geometricFixedPoints_cofiber_levelwiseEquiv
    (H : Subgroup G) (X Y : OrthogonalSpectrum G) :
    LevelwiseEquiv
      (GeometricFixedPoints (G := G) H (CofiberSpectrum X Y))
      (CofiberSpectrum
        (GeometricFixedPoints (G := G) H X)
        (GeometricFixedPoints (G := G) H Y)) := by
  intro n
  exact geometricFixedPoints_cofiber_levelEquiv (G := G) H X Y n

/--
Levelwise fixed-point decomposition for colimits:
fixed points of a sigma-colimit are sigma of fixed points.
-/
def geometricFixedPoints_colim_levelEquiv {ι : Type u}
    (H : Subgroup G) (F : ι → OrthogonalSpectrum G) (n : ℕ) :
    (GeometricFixedPoints (G := G) H (ColimSpectrum F)).level n ≃
      Σ i : ι, (GeometricFixedPoints (G := G) H (F i)).level n where
  toFun z := by
    rcases z with ⟨⟨i, x⟩, hz⟩
    refine ⟨i, x, ?_⟩
    intro h
    have hz' :
        (Sigma.mk i ((F i).gAction n (↑h) x) :
          Sigma fun j : ι => (F j).level n) = Sigma.mk i x := by
      simpa [ColimSpectrum, OrthogonalSpectrum.colim] using hz h
    simpa [heq_eq_eq] using (Sigma.mk.inj_iff.mp hz').2
  invFun z := by
    refine ⟨⟨z.1, z.2.1⟩, ?_⟩
    intro h
    simp [OrthogonalSpectrum.colim, z.2.2 h]
  left_inv z := by
    apply Subtype.ext
    rfl
  right_inv z := by
    rcases z with ⟨i, x⟩
    rfl

def geometricFixedPoints_colim_levelwiseEquiv {ι : Type u}
    (H : Subgroup G) (F : ι → OrthogonalSpectrum G) :
    LevelwiseEquiv
      (GeometricFixedPoints (G := G) H (ColimSpectrum F))
      (ColimSpectrum (fun i => GeometricFixedPoints (G := G) H (F i))) := by
  intro n
  exact geometricFixedPoints_colim_levelEquiv (G := G) H F n

end Equivariant
