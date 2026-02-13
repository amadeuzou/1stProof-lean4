import Mathlib

set_option autoImplicit false

universe u v

namespace Question7

/--
Lightweight topological marker for the ambient "real semisimple group" context.
These fields capture standard ambient regularity assumptions used in lattice
theory statements.
-/
class IsRealSemisimpleGroup (H : Type u) [Group H] [TopologicalSpace H] : Prop where
  isTopologicalGroup : TopologicalGroup H
  isT2 : T2Space H
  isLocallyCompact : LocallyCompactSpace H

/--
Abstract model of "`Γ` is a uniform lattice in `H`".
`embedding` records the inclusion map; `isDiscreteDomain` captures discreteness.
Cocompactness is modeled by the cocompact-filter condition on the embedding.
-/
class IsUniformLatticeIn (Γ : Type u) (H : Type v)
    [Group Γ] [Group H] [TopologicalSpace Γ] [TopologicalSpace H] where
  embedding : Γ →* H
  embedding_injective : Function.Injective embedding
  isDiscreteDomain : DiscreteTopology Γ
  embedding_cocompact :
    Filter.Tendsto embedding (Filter.cocompact Γ) (Filter.cocompact H)

theorem uniformLattice_embedding_injective
    {Γ : Type u} {H : Type v}
    [Group Γ] [Group H] [TopologicalSpace Γ] [TopologicalSpace H]
    [IsUniformLatticeIn Γ H] :
    Function.Injective (IsUniformLatticeIn.embedding (Γ := Γ) (H := H)) :=
  IsUniformLatticeIn.embedding_injective (Γ := Γ) (H := H)

theorem uniformLattice_discreteDomain
    {Γ : Type u} {H : Type v}
    [Group Γ] [Group H] [TopologicalSpace Γ] [TopologicalSpace H]
    [IsUniformLatticeIn Γ H] :
    DiscreteTopology Γ :=
  IsUniformLatticeIn.isDiscreteDomain (Γ := Γ) (H := H)

theorem uniformLattice_embedding_cocompact
    {Γ : Type u} {H : Type v}
    [Group Γ] [Group H] [TopologicalSpace Γ] [TopologicalSpace H]
    [IsUniformLatticeIn Γ H] :
    Filter.Tendsto (IsUniformLatticeIn.embedding (Γ := Γ) (H := H))
      (Filter.cocompact Γ) (Filter.cocompact H) :=
  IsUniformLatticeIn.embedding_cocompact (Γ := Γ) (H := H)

end Question7
