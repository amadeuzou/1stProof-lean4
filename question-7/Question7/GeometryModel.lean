import Question7.Main
import Mathlib.AlgebraicTopology.FundamentalGroupoid.SimplyConnected
import Mathlib.Geometry.Manifold.InteriorBoundary

set_option autoImplicit false

universe u v w u1 u2 u3

namespace Question7

/--
Abstract existence of a manifold-without-boundary structure on `M`.
This packages the standard manifold data needed to state `BoundarylessManifold`
without fixing a concrete model in the global API.
-/
def HasBoundarylessManifoldStructure (M : Type w) [TopologicalSpace M] : Prop :=
  ∃ (𝕜 : Type u1) (_ : NontriviallyNormedField 𝕜)
    (E : Type u2) (_ : NormedAddCommGroup E) (_ : NormedSpace 𝕜 E)
    (H : Type u3) (_ : TopologicalSpace H) (_ : ChartedSpace H M)
    (I : ModelWithCorners 𝕜 E H), BoundarylessManifold I M

/--
Lightweight model of a compact manifold without boundary.
Fields are deliberately minimal and can be strengthened incrementally.
-/
structure CompactBoundarylessManifold (M : Type w) [TopologicalSpace M] : Prop where
  compactSpace : CompactSpace M
  noBoundary : HasBoundarylessManifoldStructure M

/--
Geometric packaging of the setup in the question:
`Γ` is realized via deck transformations of a universal cover of a compact
boundaryless manifold.
-/
structure UniversalCoverRealization (Γ : Type u) (E : Type v) (M : Type w)
    [Group Γ] [TopologicalSpace E] [TopologicalSpace M] where
  realization : RealizationData Γ E M
  baseManifold : CompactBoundarylessManifold M
  simplyConnectedCover : SimplyConnectedSpace E

def UniversalCoverRealization.toRealizationData
    {Γ : Type u} {E : Type v} {M : Type w}
    [Group Γ] [TopologicalSpace E] [TopologicalSpace M]
    (hGeom : UniversalCoverRealization Γ E M) : RealizationData Γ E M :=
  hGeom.realization

@[simp] theorem UniversalCoverRealization.toRealizationData_eq
    {Γ : Type u} {E : Type v} {M : Type w}
    [Group Γ] [TopologicalSpace E] [TopologicalSpace M]
    (hGeom : UniversalCoverRealization Γ E M) :
    hGeom.toRealizationData = hGeom.realization := rfl

theorem UniversalCoverRealization.simplyConnected
    {Γ : Type u} {E : Type v} {M : Type w}
    [Group Γ] [TopologicalSpace E] [TopologicalSpace M]
    (hGeom : UniversalCoverRealization Γ E M) :
    SimplyConnectedSpace E :=
  hGeom.simplyConnectedCover

theorem UniversalCoverRealization.preconnected
    {Γ : Type u} {E : Type v} {M : Type w}
    [Group Γ] [TopologicalSpace E] [TopologicalSpace M]
    (hGeom : UniversalCoverRealization Γ E M) :
    PreconnectedSpace E := by
  letI : SimplyConnectedSpace E := hGeom.simplyConnectedCover
  infer_instance

end Question7
