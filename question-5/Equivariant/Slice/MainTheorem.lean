import Equivariant.FixedPoints.Geo
import Mathlib.Data.Fintype.Defs

namespace Equivariant

universe u v

variable {G : Type u} [Group G]

abbrev IsConnective (C : SpectrumLike G) := C.Obj → Prop

lemma oSliceConnectivity_implies_geometricFixedPoints
    (C : SpectrumLike G) (O : IncompleteTransferSystem G)
    (geo : GeoFixedPointsData C) (d : DimensionFunction G)
    (hAxioms : FixedPointClosureAxioms C O geo d)
    {n : ℤ} {X : C.Obj}
    (hX : OSliceConnectivity C O d n X) :
    GeometricFixedPointCondition C geo O d n X := by
  unfold OSliceConnectivity at hX
  induction hX with
  | of_generator hGen =>
      rcases hGen with ⟨c, hc, rfl⟩
      exact hAxioms.generators hc
  | zero =>
      exact hAxioms.zero
  | susp hMem ih =>
      exact hAxioms.susp ih
  | cofiber hA hB ihA ihB =>
      exact hAxioms.cofiber ihA ihB
  | colim F hFam ih =>
      exact hAxioms.colim F ih

/--
Reverse direction package (hard step): reconstruct from fixed-point criterion
to localizing generation by slice cells.
-/
structure ReconstructionAxiom (C : SpectrumLike G) (geo : GeoFixedPointsData C)
    (O : IncompleteTransferSystem G) (d : DimensionFunction G)
    (Conn : IsConnective C) : Prop where
  of_fixedPoints :
    ∀ {n : ℤ} {X : C.Obj},
      Conn X →
      GeometricFixedPointCondition C geo O d n X →
      OSliceConnectivity C O d n X

/--
Interface-level characterization theorem:
for connective objects, generator-defined slice connectivity is equivalent to
geometric fixed-point connectivity constraints.
-/
theorem oSliceConnectivity_iff_geometricFixedPoints [Fintype G]
    (C : SpectrumLike G) (O : IncompleteTransferSystem G) (geo : GeoFixedPointsData C)
    (d : DimensionFunction G) (Conn : IsConnective C)
    (hAxioms : FixedPointClosureAxioms C O geo d)
    (hReconstruction : ReconstructionAxiom C geo O d Conn)
    (X : C.Obj) (n : ℤ)
    (hConn : Conn X) :
    OSliceConnectivity C O d n X ↔ GeometricFixedPointCondition C geo O d n X := by
  constructor
  · intro hSlice
    exact oSliceConnectivity_implies_geometricFixedPoints C O geo d hAxioms hSlice
  · intro hGeo
    exact hReconstruction.of_fixedPoints hConn hGeo

theorem operad_sliceConnectivity_iff_geometricFixedPoints [Fintype G]
    (C : SpectrumLike G) (Oinf : NInfinityOperad G) (geo : GeoFixedPointsData C)
    (d : DimensionFunction G) (Conn : IsConnective C)
    (hAxioms : FixedPointClosureAxioms C Oinf.transferSystem geo d)
    (hReconstruction : ReconstructionAxiom C geo Oinf.transferSystem d Conn)
    (X : C.Obj) (n : ℤ)
    (hConn : Conn X) :
    OSliceConnectivity C Oinf.transferSystem d n X ↔
      GeometricFixedPointCondition C geo Oinf.transferSystem d n X := by
  exact oSliceConnectivity_iff_geometricFixedPoints
    C Oinf.transferSystem geo d Conn hAxioms hReconstruction X n hConn

theorem indexingSystem_sliceConnectivity_iff_geometricFixedPoints [Fintype G]
    (C : SpectrumLike G) (I : IndexingSystem G) (geo : GeoFixedPointsData C)
    (d : DimensionFunction G) (Conn : IsConnective C)
    (hAxioms : FixedPointClosureAxioms C I.toTransferSystem geo d)
    (hReconstruction : ReconstructionAxiom C geo I.toTransferSystem d Conn)
    (X : C.Obj) (n : ℤ)
    (hConn : Conn X) :
    OSliceConnectivity C I.toTransferSystem d n X ↔
      GeometricFixedPointCondition C geo I.toTransferSystem d n X := by
  exact oSliceConnectivity_iff_geometricFixedPoints
    C I.toTransferSystem geo d Conn hAxioms hReconstruction X n hConn

end Equivariant
