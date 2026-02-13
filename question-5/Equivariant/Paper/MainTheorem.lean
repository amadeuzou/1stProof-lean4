import Equivariant.MainResult

namespace Equivariant
namespace Paper

universe u

variable {G : Type u} [Group G]

/--
Paper-facing input package for the base theorem.
This keeps the theorem interface free of low-level closure/reconstruction fields.
-/
abbrev SliceInput (M : SliceCellModel G) (π : HomotopyGroupData G)
    (O : IncompleteTransferSystem G) (d : DimensionFunction G) :=
  MainRecommendedInput (G := G) M π O d

/--
Paper-facing input package for the base theorem with isotropy bridge data.
-/
abbrev SliceInputWithBridge (M : SliceCellModel G) (π : HomotopyGroupData G)
    (O : IncompleteTransferSystem G) (d : DimensionFunction G) :=
  MainRecommendedInputWithBridge (G := G) M π O d

/-- Paper-facing input package for the operad-level theorem. -/
abbrev OperadInput (M : SliceCellModel G) (π : HomotopyGroupData G)
    (Oinf : NInfinityOperad G) (d : DimensionFunction G) :=
  MainOperadRecommendedInput (G := G) M π Oinf d

/-- Paper-facing input package for the operad-level theorem with bridge data. -/
abbrev OperadInputWithBridge (M : SliceCellModel G) (π : HomotopyGroupData G)
    (Oinf : NInfinityOperad G) (d : DimensionFunction G) :=
  MainOperadRecommendedInputWithBridge (G := G) M π Oinf d

/-- Paper-facing input package for the indexing-system theorem. -/
abbrev IndexingInput (M : SliceCellModel G) (π : HomotopyGroupData G)
    (I : IndexingSystem G) (d : DimensionFunction G) :=
  MainIndexingSystemRecommendedInput (G := G) M π I d

/-- Paper-facing input package for the indexing-system theorem with bridge data. -/
abbrev IndexingInputWithBridge (M : SliceCellModel G) (π : HomotopyGroupData G)
    (I : IndexingSystem G) (d : DimensionFunction G) :=
  MainIndexingSystemRecommendedInputWithBridge (G := G) M π I d

def sliceInput_of_global_and_conditionalCellSurjective
    (M : SliceCellModel G)
    (π : HomotopyGroupData G)
    (O : IncompleteTransferSystem G) (d : DimensionFunction G)
    (hGlobal : MainGlobalGeometricFixedPointCondition (G := G) π O d)
    (hCondSurj : MainConditionalCellSurjective (G := G) M π O d) :
    SliceInput (G := G) M π O d :=
  mainRecommendedInput_of_global_and_conditionalCellSurjective
    (G := G) M π O d hGlobal hCondSurj

def sliceInput_of_generator_and_conditionalCellSurjective
    (M : SliceCellModel G)
    (π : HomotopyGroupData G)
    (O : IncompleteTransferSystem G) (d : DimensionFunction G)
    (hGen : MainGeneratorGeometricCondition (G := G) M π O d)
    (hConn : MainConnectednessAxiomsWithZero (G := G) π)
    (hCondSurj : MainConditionalCellSurjective (G := G) M π O d) :
    SliceInput (G := G) M π O d :=
  mainRecommendedInput_of_generator_and_conditionalCellSurjective
    (G := G) M π O d hGen hConn hCondSurj

def sliceInputWithBridge_of_global_and_conditionalCellSurjective
    (M : SliceCellModel G)
    (π : HomotopyGroupData G)
    (O : IncompleteTransferSystem G) (d : DimensionFunction G)
    (hGlobal : MainGlobalGeometricFixedPointCondition (G := G) π O d)
    (B : MainIsotropyOrthogonalBridge (G := G) M π O d)
    (hCondSurj : MainConditionalCellSurjective (G := G) M π O d) :
    SliceInputWithBridge (G := G) M π O d :=
  mainRecommendedInputWithBridge_of_global_and_conditionalCellSurjective
    (G := G) M π O d hGlobal B hCondSurj

def operadInput_of_global_and_conditionalCellSurjective
    (M : SliceCellModel G)
    (π : HomotopyGroupData G)
    (Oinf : NInfinityOperad G) (d : DimensionFunction G)
    (hGlobal :
      MainGlobalGeometricFixedPointCondition (G := G) π Oinf.transferSystem d)
    (hCondSurj :
      MainConditionalCellSurjective (G := G) M π Oinf.transferSystem d) :
    OperadInput (G := G) M π Oinf d :=
  mainOperadRecommendedInput_of_global_and_conditionalCellSurjective
    (G := G) M π Oinf d hGlobal hCondSurj

def operadInputWithBridge_of_global_and_conditionalCellSurjective
    (M : SliceCellModel G)
    (π : HomotopyGroupData G)
    (Oinf : NInfinityOperad G) (d : DimensionFunction G)
    (hGlobal :
      MainGlobalGeometricFixedPointCondition (G := G) π Oinf.transferSystem d)
    (B : MainIsotropyOrthogonalBridge (G := G) M π Oinf.transferSystem d)
    (hCondSurj :
      MainConditionalCellSurjective (G := G) M π Oinf.transferSystem d) :
    OperadInputWithBridge (G := G) M π Oinf d :=
  mainOperadRecommendedInputWithBridge_of_global_and_conditionalCellSurjective
    (G := G) M π Oinf d hGlobal B hCondSurj

def indexingInput_of_global_and_conditionalCellSurjective
    (M : SliceCellModel G)
    (π : HomotopyGroupData G)
    (I : IndexingSystem G) (d : DimensionFunction G)
    (hGlobal :
      MainGlobalGeometricFixedPointCondition (G := G) π I.toTransferSystem d)
    (hCondSurj :
      MainConditionalCellSurjective (G := G) M π I.toTransferSystem d) :
    IndexingInput (G := G) M π I d :=
  mainIndexingSystemRecommendedInput_of_global_and_conditionalCellSurjective
    (G := G) M π I d hGlobal hCondSurj

def indexingInputWithBridge_of_global_and_conditionalCellSurjective
    (M : SliceCellModel G)
    (π : HomotopyGroupData G)
    (I : IndexingSystem G) (d : DimensionFunction G)
    (hGlobal :
      MainGlobalGeometricFixedPointCondition (G := G) π I.toTransferSystem d)
    (B : MainIsotropyOrthogonalBridge (G := G) M π I.toTransferSystem d)
    (hCondSurj :
      MainConditionalCellSurjective (G := G) M π I.toTransferSystem d) :
    IndexingInputWithBridge (G := G) M π I d :=
  mainIndexingSystemRecommendedInputWithBridge_of_global_and_conditionalCellSurjective
    (G := G) M π I d hGlobal B hCondSurj

/--
Paper-layer base characterization theorem.
`hClosure` and `hReconstruction` are internalized via `SliceInput`.
-/
theorem sliceConnectivity_iff_geometricFixedPoints
    (M : SliceCellModel G)
    (π : HomotopyGroupData G)
    (O : IncompleteTransferSystem G) (d : DimensionFunction G)
    (I : SliceInput (G := G) M π O d)
    (n : ℤ) (X : OrthogonalSpectrum G) :
    IsSliceConnected (G := G) M O d n X ↔
      MainGeometricFixedPointCondition (G := G) π O d n X := by
  exact MainSliceConnectivity_iff_GeometricFixedPoints_recommended
    (G := G) M π O d I n X

/-- Paper-layer base characterization theorem with isotropy bridge input. -/
theorem sliceConnectivity_iff_geometricFixedPoints_withBridge
    (M : SliceCellModel G)
    (π : HomotopyGroupData G)
    (O : IncompleteTransferSystem G) (d : DimensionFunction G)
    (I : SliceInputWithBridge (G := G) M π O d)
    (n : ℤ) (X : OrthogonalSpectrum G) :
    IsSliceConnected (G := G) M O d n X ↔
      MainGeometricFixedPointCondition (G := G) π O d n X := by
  exact MainSliceConnectivity_iff_GeometricFixedPoints_recommendedWithBridge
    (G := G) M π O d I n X

/-- Paper-layer operad characterization theorem. -/
theorem operad_sliceConnectivity_iff_geometricFixedPoints
    (M : SliceCellModel G)
    (π : HomotopyGroupData G)
    (Oinf : NInfinityOperad G) (d : DimensionFunction G)
    (I : OperadInput (G := G) M π Oinf d)
    (n : ℤ) (X : OrthogonalSpectrum G) :
    IsSliceConnected (G := G) M Oinf.transferSystem d n X ↔
      MainGeometricFixedPointCondition (G := G) π Oinf.transferSystem d n X := by
  exact MainOperadSliceConnectivity_iff_GeometricFixedPoints_recommended
    (G := G) M π Oinf d I n X

/-- Paper-layer operad characterization theorem with bridge input. -/
theorem operad_sliceConnectivity_iff_geometricFixedPoints_withBridge
    (M : SliceCellModel G)
    (π : HomotopyGroupData G)
    (Oinf : NInfinityOperad G) (d : DimensionFunction G)
    (I : OperadInputWithBridge (G := G) M π Oinf d)
    (n : ℤ) (X : OrthogonalSpectrum G) :
    IsSliceConnected (G := G) M Oinf.transferSystem d n X ↔
      MainGeometricFixedPointCondition (G := G) π Oinf.transferSystem d n X := by
  exact MainOperadSliceConnectivity_iff_GeometricFixedPoints_recommendedWithBridge
    (G := G) M π Oinf d I n X

/-- Paper-layer indexing-system characterization theorem. -/
theorem indexingSystem_sliceConnectivity_iff_geometricFixedPoints
    (M : SliceCellModel G)
    (π : HomotopyGroupData G)
    (Ixs : IndexingSystem G) (d : DimensionFunction G)
    (I : IndexingInput (G := G) M π Ixs d)
    (n : ℤ) (X : OrthogonalSpectrum G) :
    IsSliceConnected (G := G) M Ixs.toTransferSystem d n X ↔
      MainGeometricFixedPointCondition (G := G) π Ixs.toTransferSystem d n X := by
  exact MainIndexingSystemSliceConnectivity_iff_GeometricFixedPoints_recommended
    (G := G) M π Ixs d I n X

/-- Paper-layer indexing-system characterization theorem with bridge input. -/
theorem indexingSystem_sliceConnectivity_iff_geometricFixedPoints_withBridge
    (M : SliceCellModel G)
    (π : HomotopyGroupData G)
    (Ixs : IndexingSystem G) (d : DimensionFunction G)
    (I : IndexingInputWithBridge (G := G) M π Ixs d)
    (n : ℤ) (X : OrthogonalSpectrum G) :
    IsSliceConnected (G := G) M Ixs.toTransferSystem d n X ↔
      MainGeometricFixedPointCondition (G := G) π Ixs.toTransferSystem d n X := by
  exact MainIndexingSystemSliceConnectivity_iff_GeometricFixedPoints_recommendedWithBridge
    (G := G) M π Ixs d I n X

theorem sliceConnectivity_iff_geometricFixedPoints_of_global_and_conditionalCellSurjective
    (M : SliceCellModel G)
    (π : HomotopyGroupData G)
    (O : IncompleteTransferSystem G) (d : DimensionFunction G)
    (hGlobal : MainGlobalGeometricFixedPointCondition (G := G) π O d)
    (hCondSurj : MainConditionalCellSurjective (G := G) M π O d)
    (n : ℤ) (X : OrthogonalSpectrum G) :
    IsSliceConnected (G := G) M O d n X ↔
      MainGeometricFixedPointCondition (G := G) π O d n X := by
  exact sliceConnectivity_iff_geometricFixedPoints
    (G := G) M π O d
    (sliceInput_of_global_and_conditionalCellSurjective
      (G := G) M π O d hGlobal hCondSurj)
    n X

theorem sliceConnectivity_iff_geometricFixedPoints_of_global_and_realization
    (M : SliceCellModel G)
    (π : HomotopyGroupData G)
    (O : IncompleteTransferSystem G) (d : DimensionFunction G)
    (hGlobal : MainGlobalGeometricFixedPointCondition (G := G) π O d)
    (R : MainCellRealization (G := G) M O d)
    (n : ℤ) (X : OrthogonalSpectrum G) :
    IsSliceConnected (G := G) M O d n X ↔
      MainGeometricFixedPointCondition (G := G) π O d n X := by
  exact sliceConnectivity_iff_geometricFixedPoints_of_global_and_conditionalCellSurjective
    (G := G) M π O d hGlobal
    (mainConditionalCellSurjective_of_realization (G := G) M π O d R)
    n X

theorem operad_sliceConnectivity_iff_geometricFixedPoints_of_global_and_conditionalCellSurjective
    (M : SliceCellModel G)
    (π : HomotopyGroupData G)
    (Oinf : NInfinityOperad G) (d : DimensionFunction G)
    (hGlobal :
      MainGlobalGeometricFixedPointCondition (G := G) π Oinf.transferSystem d)
    (hCondSurj :
      MainConditionalCellSurjective (G := G) M π Oinf.transferSystem d)
    (n : ℤ) (X : OrthogonalSpectrum G) :
    IsSliceConnected (G := G) M Oinf.transferSystem d n X ↔
      MainGeometricFixedPointCondition (G := G) π Oinf.transferSystem d n X := by
  exact operad_sliceConnectivity_iff_geometricFixedPoints
    (G := G) M π Oinf d
    (operadInput_of_global_and_conditionalCellSurjective
      (G := G) M π Oinf d hGlobal hCondSurj)
    n X

theorem operad_sliceConnectivity_iff_geometricFixedPoints_of_global_and_realization
    (M : SliceCellModel G)
    (π : HomotopyGroupData G)
    (Oinf : NInfinityOperad G) (d : DimensionFunction G)
    (hGlobal :
      MainGlobalGeometricFixedPointCondition (G := G) π Oinf.transferSystem d)
    (R : MainCellRealization (G := G) M Oinf.transferSystem d)
    (n : ℤ) (X : OrthogonalSpectrum G) :
    IsSliceConnected (G := G) M Oinf.transferSystem d n X ↔
      MainGeometricFixedPointCondition (G := G) π Oinf.transferSystem d n X := by
  exact operad_sliceConnectivity_iff_geometricFixedPoints_of_global_and_conditionalCellSurjective
    (G := G) M π Oinf d hGlobal
    (mainConditionalCellSurjective_of_realization
      (G := G) M π Oinf.transferSystem d R)
    n X

theorem indexingSystem_sliceConnectivity_iff_geometricFixedPoints_of_global_and_conditionalCellSurjective
    (M : SliceCellModel G)
    (π : HomotopyGroupData G)
    (Ixs : IndexingSystem G) (d : DimensionFunction G)
    (hGlobal :
      MainGlobalGeometricFixedPointCondition (G := G) π Ixs.toTransferSystem d)
    (hCondSurj :
      MainConditionalCellSurjective (G := G) M π Ixs.toTransferSystem d)
    (n : ℤ) (X : OrthogonalSpectrum G) :
    IsSliceConnected (G := G) M Ixs.toTransferSystem d n X ↔
      MainGeometricFixedPointCondition (G := G) π Ixs.toTransferSystem d n X := by
  exact indexingSystem_sliceConnectivity_iff_geometricFixedPoints
    (G := G) M π Ixs d
    (indexingInput_of_global_and_conditionalCellSurjective
      (G := G) M π Ixs d hGlobal hCondSurj)
    n X

theorem indexingSystem_sliceConnectivity_iff_geometricFixedPoints_of_global_and_realization
    (M : SliceCellModel G)
    (π : HomotopyGroupData G)
    (Ixs : IndexingSystem G) (d : DimensionFunction G)
    (hGlobal :
      MainGlobalGeometricFixedPointCondition (G := G) π Ixs.toTransferSystem d)
    (R : MainCellRealization (G := G) M Ixs.toTransferSystem d)
    (n : ℤ) (X : OrthogonalSpectrum G) :
    IsSliceConnected (G := G) M Ixs.toTransferSystem d n X ↔
      MainGeometricFixedPointCondition (G := G) π Ixs.toTransferSystem d n X := by
  exact indexingSystem_sliceConnectivity_iff_geometricFixedPoints_of_global_and_conditionalCellSurjective
    (G := G) M π Ixs d hGlobal
    (mainConditionalCellSurjective_of_realization
      (G := G) M π Ixs.toTransferSystem d R)
    n X

end Paper
end Equivariant
