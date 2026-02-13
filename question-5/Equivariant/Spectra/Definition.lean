import Mathlib.Algebra.Group.Subgroup.Defs

namespace Equivariant

universe u

/-- Canonical group structure on `PUnit`, used as the trivial target group. -/
instance instGroupPUnit : Group PUnit where
  mul _ _ := PUnit.unit
  mul_assoc := by intro a b c; cases a; cases b; cases c; rfl
  one := PUnit.unit
  one_mul := by intro a; cases a; rfl
  mul_one := by intro a; cases a; rfl
  inv _ := PUnit.unit
  inv_mul_cancel := by intro a; cases a; rfl

/--
Lightweight orthogonal-spectrum skeleton indexed by `ℕ`.
This captures the levelwise objects, `G`-action, and structure maps.
-/
structure OrthogonalSpectrum (G : Type u) [Group G] where
  level : ℕ → Type u
  gAction : ∀ n, G → level n → level n
  structMap : ∀ n, level n → level (n + 1)
  gAction_one : ∀ n x, gAction n 1 x = x
  gAction_mul : ∀ n g h x, gAction n (g * h) x = gAction n g (gAction n h x)
  structMap_equivariant :
    ∀ n g x, structMap n (gAction n g x) = gAction (n + 1) g (structMap n x)

namespace OrthogonalSpectrum

variable {G : Type u} [Group G]

/-- Zero spectrum placeholder. -/
def zero : OrthogonalSpectrum G where
  level := fun _ => PUnit
  gAction := fun _ _ _ => PUnit.unit
  structMap := fun _ _ => PUnit.unit
  gAction_one := by intro n x; cases x; rfl
  gAction_mul := by intro n g h x; cases x; rfl
  structMap_equivariant := by intro n g x; cases x; rfl

/-- Suspension placeholder: shifts levels by one. -/
def susp (X : OrthogonalSpectrum G) : OrthogonalSpectrum G where
  level := fun n => X.level (n + 1)
  gAction := fun n g => X.gAction (n + 1) g
  structMap := fun n => X.structMap (n + 1)
  gAction_one := by
    intro n x
    simpa using X.gAction_one (n + 1) x
  gAction_mul := by
    intro n g h x
    simpa using X.gAction_mul (n + 1) g h x
  structMap_equivariant := by
    intro n g x
    simpa [Nat.add_assoc] using X.structMap_equivariant (n + 1) g x

/-- Cofiber placeholder as levelwise disjoint sum. -/
def cofiber (X Y : OrthogonalSpectrum G) : OrthogonalSpectrum G where
  level := fun n => X.level n ⊕ Y.level n
  gAction := fun n g z =>
    match z with
    | Sum.inl x => Sum.inl (X.gAction n g x)
    | Sum.inr y => Sum.inr (Y.gAction n g y)
  structMap := fun n z =>
    match z with
    | Sum.inl x => Sum.inl (X.structMap n x)
    | Sum.inr y => Sum.inr (Y.structMap n y)
  gAction_one := by
    intro n z
    cases z with
    | inl x =>
        simp [X.gAction_one]
    | inr y =>
        simp [Y.gAction_one]
  gAction_mul := by
    intro n g h z
    cases z with
    | inl x =>
        simp [X.gAction_mul]
    | inr y =>
        simp [Y.gAction_mul]
  structMap_equivariant := by
    intro n g z
    cases z with
    | inl x =>
        simp [X.structMap_equivariant]
    | inr y =>
        simp [Y.structMap_equivariant]

/-- Small colimit placeholder as levelwise sigma type. -/
def colim {ι : Type u} (F : ι → OrthogonalSpectrum G) : OrthogonalSpectrum G where
  level := fun n => Σ i : ι, (F i).level n
  gAction := fun n g z => ⟨z.1, (F z.1).gAction n g z.2⟩
  structMap := fun n z => ⟨z.1, (F z.1).structMap n z.2⟩
  gAction_one := by
    intro n z
    cases z with
    | mk i x =>
        simp [(F i).gAction_one]
  gAction_mul := by
    intro n g h z
    cases z with
    | mk i x =>
        simp [(F i).gAction_mul]
  structMap_equivariant := by
    intro n g z
    cases z with
    | mk i x =>
        simp [(F i).structMap_equivariant]

end OrthogonalSpectrum

abbrev ZeroSpectrum (G : Type u) [Group G] : OrthogonalSpectrum G :=
  OrthogonalSpectrum.zero

abbrev SuspSpectrum {G : Type u} [Group G] (X : OrthogonalSpectrum G) :
    OrthogonalSpectrum G :=
  OrthogonalSpectrum.susp X

abbrev CofiberSpectrum {G : Type u} [Group G]
    (X Y : OrthogonalSpectrum G) : OrthogonalSpectrum G :=
  OrthogonalSpectrum.cofiber X Y

abbrev ColimSpectrum {G : Type u} [Group G] {ι : Type u}
    (F : ι → OrthogonalSpectrum G) : OrthogonalSpectrum G :=
  OrthogonalSpectrum.colim F

/-- Levelwise equivalence of orthogonal spectra. -/
abbrev LevelwiseEquiv {G : Type u} [Group G]
    (X Y : OrthogonalSpectrum G) : Type u :=
  ∀ n, X.level n ≃ Y.level n

namespace LevelwiseEquiv

variable {G : Type u} [Group G]

def refl (X : OrthogonalSpectrum G) : LevelwiseEquiv X X := by
  intro n
  exact Equiv.refl _

def symm {X Y : OrthogonalSpectrum G} (h : LevelwiseEquiv X Y) :
    LevelwiseEquiv Y X := by
  intro n
  exact (h n).symm

def trans {X Y Z : OrthogonalSpectrum G}
    (hXY : LevelwiseEquiv X Y) (hYZ : LevelwiseEquiv Y Z) :
    LevelwiseEquiv X Z := by
  intro n
  exact (hXY n).trans (hYZ n)

end LevelwiseEquiv

/-- Morphisms in the levelwise orthogonal-spectrum interface. -/
structure OrthogonalSpectrumHom {G : Type u} [Group G]
    (X Y : OrthogonalSpectrum G) where
  app : ∀ n, X.level n → Y.level n
  equivariant :
    ∀ n g x, app n (X.gAction n g x) = Y.gAction n g (app n x)
  structMap_naturality :
    ∀ n x, app (n + 1) (X.structMap n x) = Y.structMap n (app n x)

namespace OrthogonalSpectrumHom

variable {G : Type u} [Group G]

def id (X : OrthogonalSpectrum G) : OrthogonalSpectrumHom X X where
  app := fun _ x => x
  equivariant := by intro n g x; rfl
  structMap_naturality := by intro n x; rfl

def comp {X Y Z : OrthogonalSpectrum G}
    (f : OrthogonalSpectrumHom X Y) (g : OrthogonalSpectrumHom Y Z) :
    OrthogonalSpectrumHom X Z where
  app := fun n x => g.app n (f.app n x)
  equivariant := by
    intro n h x
    rw [f.equivariant, g.equivariant]
  structMap_naturality := by
    intro n x
    rw [f.structMap_naturality, g.structMap_naturality]

end OrthogonalSpectrumHom

end Equivariant
