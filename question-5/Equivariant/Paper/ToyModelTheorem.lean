import Equivariant.Instances.ToyModel

namespace Equivariant
namespace Paper

universe u

variable {G : Type u} [Group G] [Fintype G]

/--
Concrete nontrivial characterization theorem on the toy model:
for connective objects, slice connectivity is equivalent to geometric
fixed-point connectivity constraints.
-/
theorem toy_sliceConnectivity_iff_geometricFixedPoints
    (O : IncompleteTransferSystem G) (d : DimensionFunction G)
    (hSpec : DimensionFunctionSpec d)
    (X : Set (Question5.SliceCellData G)) (n : ℤ)
    (hConn : Instances.ToyModel.Conn G X) :
    OSliceConnectivity (Instances.ToyModel.C G) O d n X ↔
      GeometricFixedPointCondition (Instances.ToyModel.C G)
        (Instances.ToyModel.geoData O) O d n X := by
  exact Instances.ToyModel.toy_oSliceConnectivity_iff_geometricFixedPoints
    (G := G) O d hSpec X n hConn

theorem toy_operad_sliceConnectivity_iff_geometricFixedPoints
    (Oinf : NInfinityOperad G) (d : DimensionFunction G)
    (hSpec : DimensionFunctionSpec d)
    (X : Set (Question5.SliceCellData G)) (n : ℤ)
    (hConn : Instances.ToyModel.Conn G X) :
    OSliceConnectivity (Instances.ToyModel.C G) Oinf.transferSystem d n X ↔
      GeometricFixedPointCondition (Instances.ToyModel.C G)
        (Instances.ToyModel.geoData Oinf.transferSystem)
        Oinf.transferSystem d n X := by
  exact toy_sliceConnectivity_iff_geometricFixedPoints
    (G := G) Oinf.transferSystem d hSpec X n hConn

theorem toy_indexingSystem_sliceConnectivity_iff_geometricFixedPoints
    (I : IndexingSystem G) (d : DimensionFunction G)
    (hSpec : DimensionFunctionSpec d)
    (X : Set (Question5.SliceCellData G)) (n : ℤ)
    (hConn : Instances.ToyModel.Conn G X) :
    OSliceConnectivity (Instances.ToyModel.C G) I.toTransferSystem d n X ↔
      GeometricFixedPointCondition (Instances.ToyModel.C G)
        (Instances.ToyModel.geoData I.toTransferSystem)
        I.toTransferSystem d n X := by
  exact toy_sliceConnectivity_iff_geometricFixedPoints
    (G := G) I.toTransferSystem d hSpec X n hConn

end Paper
end Equivariant
