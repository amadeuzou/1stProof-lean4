import Equivariant.MainResult
import Equivariant.Paper.MainTheorem
import Mathlib.Algebra.Group.Subgroup.Lattice

namespace Equivariant
namespace Instances
namespace MainPayloadModel

universe u

variable {G : Type u} [Group G]

/--
Concrete slice-cell model using the `realization` payload embedded in
`MainSliceCellData`.
-/
def model : SliceCellModel G where
  cellObj := fun c => c.realization

/-- Canonical payload cell at level `n` encoding any target spectrum `X`. -/
def encodeCell (O : IncompleteTransferSystem G) (d : DimensionFunction G)
    (n : ℤ) (X : OrthogonalSpectrum G) : MainSliceCellData G where
  fromSubgroup := ⊥
  toSubgroup := ⊥
  degree := max 0 (d O ⊥ n)
  realization := X

lemma encodeCell_mem (O : IncompleteTransferSystem G) (d : DimensionFunction G)
    (n : ℤ) (X : OrthogonalSpectrum G) :
    encodeCell (G := G) O d n X ∈ MainSliceCells (G := G) O d n := by
  refine ⟨O.transfer_refl ⊥, ?_, ?_⟩
  · exact le_max_right _ _
  · exact le_max_left _ _

lemma encodeCell_eval (O : IncompleteTransferSystem G) (d : DimensionFunction G)
    (n : ℤ) (X : OrthogonalSpectrum G) :
    model (G := G).cellObj (encodeCell (G := G) O d n X) = X := by
  rfl

/--
Explicit constructive realization for the payload model.
This removes separate surjectivity assumptions.
-/
def realization (O : IncompleteTransferSystem G) (d : DimensionFunction G) :
    MainCellRealization (G := G) (model (G := G)) O d where
  encode := encodeCell (G := G) O d
  encode_mem := by
    intro n X
    exact encodeCell_mem (G := G) O d n X
  encode_eval := by
    intro n X
    exact encodeCell_eval (G := G) O d n X

theorem sliceConnectivity_iff_geometricFixedPoints_of_global
    (π : HomotopyGroupData G)
    (O : IncompleteTransferSystem G) (d : DimensionFunction G)
    (hGlobal : MainGlobalGeometricFixedPointCondition (G := G) π O d)
    (n : ℤ) (X : OrthogonalSpectrum G) :
    IsSliceConnected (G := G) (model (G := G)) O d n X ↔
      MainGeometricFixedPointCondition (G := G) π O d n X := by
  exact Paper.sliceConnectivity_iff_geometricFixedPoints_of_global_and_realization
    (G := G) (M := model (G := G)) (π := π) O d hGlobal
    (realization (G := G) O d) n X

theorem sliceConnectivity_iff_geometricFixedPoints_empty
    (O : IncompleteTransferSystem G) (d : DimensionFunction G)
    (n : ℤ) (X : OrthogonalSpectrum G) :
    IsSliceConnected (G := G) (model (G := G)) O d n X ↔
      MainGeometricFixedPointCondition (G := G) (EmptyHomotopyGroupData G) O d n X := by
  exact Paper.sliceConnectivity_iff_geometricFixedPoints_of_global_and_realization
    (G := G) (M := model (G := G)) (π := EmptyHomotopyGroupData G) O d
    (mainGlobalGeometricFixedPointCondition_empty (G := G) O d)
    (realization (G := G) O d) n X

theorem operadSliceConnectivity_iff_geometricFixedPoints_empty
    (Oinf : NInfinityOperad G) (d : DimensionFunction G)
    (n : ℤ) (X : OrthogonalSpectrum G) :
    IsSliceConnected (G := G) (model (G := G)) Oinf.transferSystem d n X ↔
      MainGeometricFixedPointCondition
        (G := G) (EmptyHomotopyGroupData G) Oinf.transferSystem d n X := by
  exact Paper.operad_sliceConnectivity_iff_geometricFixedPoints_of_global_and_realization
    (G := G) (M := model (G := G)) (π := EmptyHomotopyGroupData G) Oinf d
    (mainGlobalGeometricFixedPointCondition_empty (G := G) Oinf.transferSystem d)
    (realization (G := G) Oinf.transferSystem d) n X

theorem indexingSystemSliceConnectivity_iff_geometricFixedPoints_empty
    (I : IndexingSystem G) (d : DimensionFunction G)
    (n : ℤ) (X : OrthogonalSpectrum G) :
    IsSliceConnected (G := G) (model (G := G)) I.toTransferSystem d n X ↔
      MainGeometricFixedPointCondition
        (G := G) (EmptyHomotopyGroupData G) I.toTransferSystem d n X := by
  exact Paper.indexingSystem_sliceConnectivity_iff_geometricFixedPoints_of_global_and_realization
    (G := G) (M := model (G := G)) (π := EmptyHomotopyGroupData G) I d
    (mainGlobalGeometricFixedPointCondition_empty (G := G) I.toTransferSystem d)
    (realization (G := G) I.toTransferSystem d) n X

/--
Final no-extra-assumption entry theorem at transfer-system level for the
payload model. This specializes to the empty homotopy-group data interface.
-/
theorem final_transferSystem_sliceConnectivity_iff_geometricFixedPoints
    (O : IncompleteTransferSystem G) (d : DimensionFunction G)
    (n : ℤ) (X : OrthogonalSpectrum G) :
    IsSliceConnected (G := G) (model (G := G)) O d n X ↔
      MainGeometricFixedPointCondition (G := G) (EmptyHomotopyGroupData G) O d n X := by
  exact sliceConnectivity_iff_geometricFixedPoints_empty (G := G) O d n X

/--
Final no-extra-assumption entry theorem at `N∞`-operad level for the payload
model.
-/
theorem final_operad_sliceConnectivity_iff_geometricFixedPoints
    (Oinf : NInfinityOperad G) (d : DimensionFunction G)
    (n : ℤ) (X : OrthogonalSpectrum G) :
    IsSliceConnected (G := G) (model (G := G)) Oinf.transferSystem d n X ↔
      MainGeometricFixedPointCondition
        (G := G) (EmptyHomotopyGroupData G) Oinf.transferSystem d n X := by
  exact operadSliceConnectivity_iff_geometricFixedPoints_empty (G := G) Oinf d n X

/--
Final no-extra-assumption entry theorem at indexing-system level for the
payload model.
-/
theorem final_indexingSystem_sliceConnectivity_iff_geometricFixedPoints
    (I : IndexingSystem G) (d : DimensionFunction G)
    (n : ℤ) (X : OrthogonalSpectrum G) :
    IsSliceConnected (G := G) (model (G := G)) I.toTransferSystem d n X ↔
      MainGeometricFixedPointCondition
        (G := G) (EmptyHomotopyGroupData G) I.toTransferSystem d n X := by
  exact indexingSystemSliceConnectivity_iff_geometricFixedPoints_empty (G := G) I d n X

/-! ### Minimal recommended-API examples -/

/-- Trivial subgroup family containing all subgroups. -/
def totalSubgroupFamily : SubgroupFamily G where
  contains := fun _ => True
  closed_under_subgroup := by
    intro H K hK hHK
    trivial

/-- Trivial isotropy-separation data used for bridge examples. -/
def trivialIsotropyData : IsotropySeparationData.{u, 0} G where
  spectrum := PUnit
  smash := fun _ _ => PUnit.unit
  phi := fun _ _ => PUnit.unit
  eFamily := fun _ => PUnit.unit
  eTildeFamily := fun _ => PUnit.unit
  cofiber := fun _ _ => PUnit.unit
  isotropy_cofiber := by
    intro F X
    rfl
  phi_preserves_smash := by
    intro H X Y
    rfl
  phi_preserves_cofiber := by
    intro H A B
    rfl

/-- Trivial bridge witness (all equations are definitional in `PUnit`). -/
def trivialBridge (π : HomotopyGroupData G)
    (O : IncompleteTransferSystem G) (d : DimensionFunction G) :
    MainIsotropyOrthogonalBridge.{u, 0} (G := G) (model (G := G)) π O d where
  D := trivialIsotropyData (G := G)
  lift := fun _ => PUnit.unit
  family := fun _ _ => totalSubgroupFamily (G := G)
  orthogonal_of_fixedPoints := by
    intro n X hGeo H
    rfl

example (O : IncompleteTransferSystem G) (d : DimensionFunction G)
    (n : ℤ) (X : OrthogonalSpectrum G) :
    IsSliceConnected (G := G) (model (G := G)) O d n X ↔
      MainGeometricFixedPointCondition (G := G) (EmptyHomotopyGroupData G) O d n X := by
  let RInput :=
    mainRecommendedInput_of_global_and_conditionalCellSurjective
      (G := G) (M := model (G := G)) (π := EmptyHomotopyGroupData G) O d
      (mainGlobalGeometricFixedPointCondition_empty (G := G) O d)
      (mainConditionalCellSurjective_of_realization
        (G := G) (M := model (G := G)) (π := EmptyHomotopyGroupData G) O d
        (realization (G := G) O d))
  exact MainSliceConnectivity_iff_GeometricFixedPoints_recommended
    (G := G) (M := model (G := G)) (π := EmptyHomotopyGroupData G) O d RInput n X

example (Oinf : NInfinityOperad G) (d : DimensionFunction G)
    (n : ℤ) (X : OrthogonalSpectrum G) :
    IsSliceConnected (G := G) (model (G := G)) Oinf.transferSystem d n X ↔
      MainGeometricFixedPointCondition
        (G := G) (EmptyHomotopyGroupData G) Oinf.transferSystem d n X := by
  let RInput :=
    mainOperadRecommendedInput_of_global_and_conditionalCellSurjective
      (G := G) (M := model (G := G)) (π := EmptyHomotopyGroupData G) Oinf d
      (mainGlobalGeometricFixedPointCondition_empty (G := G) Oinf.transferSystem d)
      (mainConditionalCellSurjective_of_realization
        (G := G) (M := model (G := G)) (π := EmptyHomotopyGroupData G)
        Oinf.transferSystem d
        (realization (G := G) Oinf.transferSystem d))
  exact MainOperadSliceConnectivity_iff_GeometricFixedPoints_recommended
    (G := G) (M := model (G := G)) (π := EmptyHomotopyGroupData G) Oinf d RInput n X

example (I : IndexingSystem G) (d : DimensionFunction G)
    (n : ℤ) (X : OrthogonalSpectrum G) :
    IsSliceConnected (G := G) (model (G := G)) I.toTransferSystem d n X ↔
      MainGeometricFixedPointCondition
        (G := G) (EmptyHomotopyGroupData G) I.toTransferSystem d n X := by
  let RInput :=
    mainIndexingSystemRecommendedInput_of_global_and_conditionalCellSurjective
      (G := G) (M := model (G := G)) (π := EmptyHomotopyGroupData G) I d
      (mainGlobalGeometricFixedPointCondition_empty (G := G) I.toTransferSystem d)
      (mainConditionalCellSurjective_of_realization
        (G := G) (M := model (G := G)) (π := EmptyHomotopyGroupData G)
        I.toTransferSystem d
        (realization (G := G) I.toTransferSystem d))
  exact MainIndexingSystemSliceConnectivity_iff_GeometricFixedPoints_recommended
    (G := G) (M := model (G := G)) (π := EmptyHomotopyGroupData G) I d RInput n X

example (O : IncompleteTransferSystem G) (d : DimensionFunction G)
    (n : ℤ) (X : OrthogonalSpectrum G) :
    IsSliceConnected (G := G) (model (G := G)) O d n X ↔
      MainGeometricFixedPointCondition (G := G) (EmptyHomotopyGroupData G) O d n X := by
  exact MainSliceConnectivity_iff_GeometricFixedPoints_recommendedWithBridge
    (G := G) (M := model (G := G)) (π := EmptyHomotopyGroupData G) O d
    (mainRecommendedInputWithBridge_of_global_and_conditionalCellSurjective.{u, 0}
      (G := G) (M := model (G := G)) (π := EmptyHomotopyGroupData G) O d
      (mainGlobalGeometricFixedPointCondition_empty (G := G) O d)
      (trivialBridge (G := G) (π := EmptyHomotopyGroupData G) O d)
      (mainConditionalCellSurjective_of_realization
        (G := G) (M := model (G := G)) (π := EmptyHomotopyGroupData G) O d
        (realization (G := G) O d)))
    n
    X

example (Oinf : NInfinityOperad G) (d : DimensionFunction G)
    (n : ℤ) (X : OrthogonalSpectrum G) :
    IsSliceConnected (G := G) (model (G := G)) Oinf.transferSystem d n X ↔
      MainGeometricFixedPointCondition
        (G := G) (EmptyHomotopyGroupData G) Oinf.transferSystem d n X := by
  exact MainOperadSliceConnectivity_iff_GeometricFixedPoints_recommendedWithBridge
    (G := G) (M := model (G := G)) (π := EmptyHomotopyGroupData G) Oinf d
    (mainOperadRecommendedInputWithBridge_of_global_and_conditionalCellSurjective.{u, 0}
      (G := G) (M := model (G := G)) (π := EmptyHomotopyGroupData G) Oinf d
      (mainGlobalGeometricFixedPointCondition_empty (G := G) Oinf.transferSystem d)
      (trivialBridge (G := G) (π := EmptyHomotopyGroupData G) Oinf.transferSystem d)
      (mainConditionalCellSurjective_of_realization
        (G := G) (M := model (G := G)) (π := EmptyHomotopyGroupData G)
        Oinf.transferSystem d
        (realization (G := G) Oinf.transferSystem d)))
    n
    X

example (I : IndexingSystem G) (d : DimensionFunction G)
    (n : ℤ) (X : OrthogonalSpectrum G) :
    IsSliceConnected (G := G) (model (G := G)) I.toTransferSystem d n X ↔
      MainGeometricFixedPointCondition
        (G := G) (EmptyHomotopyGroupData G) I.toTransferSystem d n X := by
  exact MainIndexingSystemSliceConnectivity_iff_GeometricFixedPoints_recommendedWithBridge
    (G := G) (M := model (G := G)) (π := EmptyHomotopyGroupData G) I d
    (mainIndexingSystemRecommendedInputWithBridge_of_global_and_conditionalCellSurjective.{u, 0}
      (G := G) (M := model (G := G)) (π := EmptyHomotopyGroupData G) I d
      (mainGlobalGeometricFixedPointCondition_empty (G := G) I.toTransferSystem d)
      (trivialBridge (G := G) (π := EmptyHomotopyGroupData G) I.toTransferSystem d)
      (mainConditionalCellSurjective_of_realization
        (G := G) (M := model (G := G)) (π := EmptyHomotopyGroupData G)
        I.toTransferSystem d
        (realization (G := G) I.toTransferSystem d)))
    n
    X

/-! ### Legacy -> recommended migration (minimal base example) -/

example (O : IncompleteTransferSystem G) (d : DimensionFunction G)
    (n : ℤ) (X : OrthogonalSpectrum G) :
    IsSliceConnected (G := G) (model (G := G)) O d n X ↔
      MainGeometricFixedPointCondition (G := G) (EmptyHomotopyGroupData G) O d n X := by
  -- Legacy wrapper style.
  exact MainSliceConnectivity_iff_GeometricFixedPoints_of_global_and_realization
    (G := G) (M := model (G := G)) (π := EmptyHomotopyGroupData G) O d
    (mainGlobalGeometricFixedPointCondition_empty (G := G) O d)
    (realization (G := G) O d)
    n
    X

example (O : IncompleteTransferSystem G) (d : DimensionFunction G)
    (n : ℤ) (X : OrthogonalSpectrum G) :
    IsSliceConnected (G := G) (model (G := G)) O d n X ↔
      MainGeometricFixedPointCondition (G := G) (EmptyHomotopyGroupData G) O d n X := by
  -- Recommended style (target migration path).
  let RInput :=
    mainRecommendedInput_of_global_and_conditionalCellSurjective
      (G := G) (M := model (G := G)) (π := EmptyHomotopyGroupData G) O d
      (mainGlobalGeometricFixedPointCondition_empty (G := G) O d)
      (mainConditionalCellSurjective_of_realization
        (G := G) (M := model (G := G)) (π := EmptyHomotopyGroupData G) O d
        (realization (G := G) O d))
  exact MainSliceConnectivity_iff_GeometricFixedPoints_recommended
    (G := G) (M := model (G := G)) (π := EmptyHomotopyGroupData G) O d RInput n X

example (Oinf : NInfinityOperad G) (d : DimensionFunction G)
    (n : ℤ) (X : OrthogonalSpectrum G) :
    IsSliceConnected (G := G) (model (G := G)) Oinf.transferSystem d n X ↔
      MainGeometricFixedPointCondition
        (G := G) (EmptyHomotopyGroupData G) Oinf.transferSystem d n X := by
  -- Legacy wrapper style.
  exact MainOperadSliceConnectivity_iff_GeometricFixedPoints_of_global_and_realization
    (G := G) (M := model (G := G)) (π := EmptyHomotopyGroupData G) Oinf d
    (mainGlobalGeometricFixedPointCondition_empty (G := G) Oinf.transferSystem d)
    (realization (G := G) Oinf.transferSystem d)
    n
    X

example (Oinf : NInfinityOperad G) (d : DimensionFunction G)
    (n : ℤ) (X : OrthogonalSpectrum G) :
    IsSliceConnected (G := G) (model (G := G)) Oinf.transferSystem d n X ↔
      MainGeometricFixedPointCondition
        (G := G) (EmptyHomotopyGroupData G) Oinf.transferSystem d n X := by
  -- Recommended style (target migration path).
  let RInput :=
    mainOperadRecommendedInput_of_global_and_conditionalCellSurjective
      (G := G) (M := model (G := G)) (π := EmptyHomotopyGroupData G) Oinf d
      (mainGlobalGeometricFixedPointCondition_empty (G := G) Oinf.transferSystem d)
      (mainConditionalCellSurjective_of_realization
        (G := G) (M := model (G := G)) (π := EmptyHomotopyGroupData G)
        Oinf.transferSystem d
        (realization (G := G) Oinf.transferSystem d))
  exact MainOperadSliceConnectivity_iff_GeometricFixedPoints_recommended
    (G := G) (M := model (G := G)) (π := EmptyHomotopyGroupData G) Oinf d RInput n X

example (I : IndexingSystem G) (d : DimensionFunction G)
    (n : ℤ) (X : OrthogonalSpectrum G) :
    IsSliceConnected (G := G) (model (G := G)) I.toTransferSystem d n X ↔
      MainGeometricFixedPointCondition
        (G := G) (EmptyHomotopyGroupData G) I.toTransferSystem d n X := by
  -- Legacy wrapper style.
  exact MainIndexingSystemSliceConnectivity_iff_GeometricFixedPoints_of_global_and_realization
    (G := G) (M := model (G := G)) (π := EmptyHomotopyGroupData G) I d
    (mainGlobalGeometricFixedPointCondition_empty (G := G) I.toTransferSystem d)
    (realization (G := G) I.toTransferSystem d)
    n
    X

example (I : IndexingSystem G) (d : DimensionFunction G)
    (n : ℤ) (X : OrthogonalSpectrum G) :
    IsSliceConnected (G := G) (model (G := G)) I.toTransferSystem d n X ↔
      MainGeometricFixedPointCondition
        (G := G) (EmptyHomotopyGroupData G) I.toTransferSystem d n X := by
  -- Recommended style (target migration path).
  let RInput :=
    mainIndexingSystemRecommendedInput_of_global_and_conditionalCellSurjective
      (G := G) (M := model (G := G)) (π := EmptyHomotopyGroupData G) I d
      (mainGlobalGeometricFixedPointCondition_empty (G := G) I.toTransferSystem d)
      (mainConditionalCellSurjective_of_realization
        (G := G) (M := model (G := G)) (π := EmptyHomotopyGroupData G)
        I.toTransferSystem d
        (realization (G := G) I.toTransferSystem d))
  exact MainIndexingSystemSliceConnectivity_iff_GeometricFixedPoints_recommended
    (G := G) (M := model (G := G)) (π := EmptyHomotopyGroupData G) I d RInput n X

/-! ### Bridge migration (minimal base example) -/

example (O : IncompleteTransferSystem G) (d : DimensionFunction G)
    (n : ℤ) (X : OrthogonalSpectrum G) :
    IsSliceConnected (G := G) (model (G := G)) O d n X ↔
      MainGeometricFixedPointCondition (G := G) (EmptyHomotopyGroupData G) O d n X := by
  -- Legacy bridge wrapper style.
  exact MainSliceConnectivity_iff_GeometricFixedPoints_of_global_and_conditionalCellRealization_and_bridge
    (G := G) (M := model (G := G)) (π := EmptyHomotopyGroupData G) O d
    (mainGlobalGeometricFixedPointCondition_empty (G := G) O d)
    (trivialBridge (G := G) (π := EmptyHomotopyGroupData G) O d)
    (mainConditionalCellRealization_of_realization
      (G := G) (M := model (G := G)) (π := EmptyHomotopyGroupData G) O d
      (realization (G := G) O d))
    n
    X

example (O : IncompleteTransferSystem G) (d : DimensionFunction G)
    (n : ℤ) (X : OrthogonalSpectrum G) :
    IsSliceConnected (G := G) (model (G := G)) O d n X ↔
      MainGeometricFixedPointCondition (G := G) (EmptyHomotopyGroupData G) O d n X := by
  -- Recommended bridge style (target migration path).
  let hCondSurj :
      MainConditionalCellSurjective
        (G := G) (model (G := G)) (EmptyHomotopyGroupData G) O d :=
    mainConditionalCellSurjective_of_realization
      (G := G) (M := model (G := G)) (π := EmptyHomotopyGroupData G) O d
      (realization (G := G) O d)
  let RInput :=
    mainRecommendedInputWithBridge_of_global_and_conditionalCellSurjective.{u, 0}
      (G := G) (M := model (G := G)) (π := EmptyHomotopyGroupData G) O d
      (mainGlobalGeometricFixedPointCondition_empty (G := G) O d)
      (trivialBridge (G := G) (π := EmptyHomotopyGroupData G) O d)
      hCondSurj
  exact MainSliceConnectivity_iff_GeometricFixedPoints_recommendedWithBridge
    (G := G) (M := model (G := G)) (π := EmptyHomotopyGroupData G) O d RInput n X

end MainPayloadModel
end Instances
end Equivariant
