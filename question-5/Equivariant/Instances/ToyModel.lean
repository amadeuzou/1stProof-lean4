import Equivariant.Slice.MainTheorem
import Question5
import Mathlib.Data.Set.Lattice

namespace Equivariant
namespace Instances
namespace ToyModel

universe u

variable {G : Type u} [Group G]

abbrev C (G : Type u) [Group G] : SpectrumLike G where
  Obj := Set (Question5.SliceCellData G)
  zero := (∅ : Set (Question5.SliceCellData G))
  susp := fun X => X
  cofiber := fun X Y => X ∪ Y
  colim := fun {ι} (F : ι → Set (Question5.SliceCellData G)) => ⋃ i : ι, F i
  sliceCellObj := fun H K n =>
    ({ { fromSubgroup := H, toSubgroup := K, degree := n } } : Set (Question5.SliceCellData G))

abbrev Conn (G : Type u) [Group G] : IsConnective (C G) :=
  fun X => ∀ c : Question5.SliceCellData G, c ∈ X → 0 ≤ c.degree

def geoData (O : IncompleteTransferSystem G) : GeoFixedPointsData (C G) where
  PlainObj := Set (Question5.SliceCellData G)
  phi := fun H X => {c : Question5.SliceCellData G | c ∈ X ∧ O.transfer H c.fromSubgroup}
  isConnected := fun _ Y t =>
    ∀ c : Question5.SliceCellData G, c ∈ Y → O.transfer c.fromSubgroup c.toSubgroup ∧ t ≤ c.degree

lemma geoCondition_of_generator (O : IncompleteTransferSystem G) (d : DimensionFunction G)
    (hSpec : DimensionFunctionSpec d) (n : ℤ) {c : SliceCellData G}
    (hc : c ∈ OSliceCells (C G) O d n) :
    GeometricFixedPointCondition (C G) (geoData O) O d n
      ((C G).sliceCellObj c.fromSubgroup c.toSubgroup c.degree) := by
  intro H c' hc'
  rcases hc' with ⟨hcset, htrans⟩
  have hcEq :
      c' = ({ fromSubgroup := c.fromSubgroup, toSubgroup := c.toSubgroup, degree := c.degree } :
        Question5.SliceCellData G) := by
    simpa [C] using hcset
  have hBoundH : d O H n ≤ d O c'.fromSubgroup n := by
    simpa [hcEq] using hSpec.transfer_mono htrans
  have hTransfer : O.transfer c'.fromSubgroup c'.toSubgroup := by
    simpa [hcEq] using hc.1
  have hBoundFrom : d O c'.fromSubgroup n ≤ c'.degree := by
    simpa [hcEq] using hc.2.1
  exact ⟨hTransfer, le_trans hBoundH hBoundFrom⟩

lemma geoCondition_zero (O : IncompleteTransferSystem G) (d : DimensionFunction G) (n : ℤ) :
    GeometricFixedPointCondition (C G) (geoData O) O d n (C G).zero := by
  intro H c hc
  exact False.elim (Set.notMem_empty c hc.1)

lemma geoCondition_susp {O : IncompleteTransferSystem G} {d : DimensionFunction G}
    {n : ℤ} {X : Set (Question5.SliceCellData G)}
    (hX : GeometricFixedPointCondition (C G) (geoData O) O d n X) :
    GeometricFixedPointCondition (C G) (geoData O) O d n ((C G).susp X) := by
  exact hX

lemma geoCondition_cofiber {O : IncompleteTransferSystem G} {d : DimensionFunction G}
    {n : ℤ} {X Y : Set (Question5.SliceCellData G)}
    (hX : GeometricFixedPointCondition (C G) (geoData O) O d n X)
    (hY : GeometricFixedPointCondition (C G) (geoData O) O d n Y) :
    GeometricFixedPointCondition (C G) (geoData O) O d n ((C G).cofiber X Y) := by
  intro H c hc
  rcases hc with ⟨hcXY, htrans⟩
  rcases hcXY with hcX | hcY
  · exact hX H c ⟨hcX, htrans⟩
  · exact hY H c ⟨hcY, htrans⟩

lemma geoCondition_colim {O : IncompleteTransferSystem G} {d : DimensionFunction G}
    {n : ℤ} {ι : Type u} (F : ι → Set (Question5.SliceCellData G))
    (hF : ∀ i, GeometricFixedPointCondition (C G) (geoData O) O d n (F i)) :
    GeometricFixedPointCondition (C G) (geoData O) O d n ((C G).colim F) := by
  intro H c hc
  rcases hc with ⟨hcUnion, htrans⟩
  rcases Set.mem_iUnion.mp hcUnion with ⟨i, hci⟩
  exact hF i H c ⟨hci, htrans⟩

def closureAxioms (O : IncompleteTransferSystem G) (d : DimensionFunction G)
    (hSpec : DimensionFunctionSpec d) :
    FixedPointClosureAxioms (C G) O (geoData O) d where
  generators := by
    intro n c hc
    exact geoCondition_of_generator O d hSpec n hc
  zero := by
    intro n
    exact geoCondition_zero O d n
  susp := by
    intro n X hX
    exact geoCondition_susp hX
  cofiber := by
    intro n X Y hX hY
    exact geoCondition_cofiber hX hY
  colim := by
    intro n ι F hF
    exact geoCondition_colim F hF

lemma cell_is_oSliceCell_of_geometricFixedPoints
    {O : IncompleteTransferSystem G} {d : DimensionFunction G} {n : ℤ}
    {X : Set (Question5.SliceCellData G)} {c : Question5.SliceCellData G}
    (hConn : Conn G X)
    (hGeo : GeometricFixedPointCondition (C G) (geoData O) O d n X)
    (hcX : c ∈ X) :
    ({ fromSubgroup := c.fromSubgroup, toSubgroup := c.toSubgroup, degree := c.degree } :
      SliceCellData G) ∈ OSliceCells (C G) O d n := by
  have hAtFrom := hGeo c.fromSubgroup
  have hmemFrom :=
    (show c ∈ {x : Question5.SliceCellData G | x ∈ X ∧ O.transfer c.fromSubgroup x.fromSubgroup} from
      ⟨hcX, O.transfer_refl c.fromSubgroup⟩)
  have hFromInfo := hAtFrom c hmemFrom
  refine ⟨?_, ?_, ?_⟩
  · simpa using hFromInfo.1
  · simpa using hFromInfo.2
  · exact hConn c hcX

def reconstructionAxiom (O : IncompleteTransferSystem G) (d : DimensionFunction G) :
    ReconstructionAxiom (C G) (geoData O) O d (Conn G) where
  of_fixedPoints := by
    intro n X hConn hGeo
    let ι := {c : Question5.SliceCellData G // c ∈ X}
    let F : ι → Set (Question5.SliceCellData G) := fun i => ({i.1} : Set (Question5.SliceCellData G))
    have hF : ∀ i, InLocalizing (C G) (SliceGenerators (C G) O d n) (F i) := by
      intro i
      have hc :
          ({ fromSubgroup := i.1.fromSubgroup, toSubgroup := i.1.toSubgroup, degree := i.1.degree } :
            SliceCellData G) ∈ OSliceCells (C G) O d n :=
        cell_is_oSliceCell_of_geometricFixedPoints hConn hGeo i.2
      apply InLocalizing.of_generator
      refine ⟨{ fromSubgroup := i.1.fromSubgroup, toSubgroup := i.1.toSubgroup, degree := i.1.degree }, hc, ?_⟩
      simp [C, F]
    have hColim : InLocalizing (C G) (SliceGenerators (C G) O d n) ((C G).colim F) :=
      InLocalizing.colim (C := C G) (S := SliceGenerators (C G) O d n) F hF
    have hEq : ((C G).colim F) = X := by
      ext c
      constructor
      · intro hcUnion
        rcases Set.mem_iUnion.mp hcUnion with ⟨i, hci⟩
        have hEqc : c = i.1 := by simpa [F] using hci
        exact hEqc ▸ i.2
      · intro hcX
        refine Set.mem_iUnion.mpr ?_
        refine ⟨⟨c, hcX⟩, ?_⟩
        simp [F]
    unfold OSliceConnectivity
    exact hEq ▸ hColim

theorem toy_oSliceConnectivity_iff_geometricFixedPoints [Fintype G]
    (O : IncompleteTransferSystem G) (d : DimensionFunction G)
    (hSpec : DimensionFunctionSpec d)
    (X : Set (Question5.SliceCellData G)) (n : ℤ) (hConn : Conn G X) :
    OSliceConnectivity (C G) O d n X ↔
      GeometricFixedPointCondition (C G) (geoData O) O d n X := by
  exact oSliceConnectivity_iff_geometricFixedPoints
    (C G) O (geoData O) d (Conn G)
    (closureAxioms O d hSpec) (reconstructionAxiom O d) X n hConn

end ToyModel
end Instances
end Equivariant
