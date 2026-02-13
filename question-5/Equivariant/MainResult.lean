import Equivariant.Slice.Filtration
import Equivariant.Slice.Syntax
import Equivariant.FixedPoints.Geometric
import Equivariant.FixedPoints.Isotropy
import Equivariant.IndexingSystem

namespace Equivariant

universe u

variable {G : Type u} [Group G]

abbrev HomotopyGroupData (K : Type u) [Group K] :=
  Subgroup K → ℤ → OrthogonalSpectrum K → Type u

/-- 
Connectivity of a spectrum. 
X is n-connected if its homotopy groups vanish for k < n.
Here we encode `π_k^H(X) = 0` as `IsEmpty (π H k X)` for all `k < n`.
-/
def IsConnected {K : Type u} [Group K]
    (π : HomotopyGroupData K) (n : ℤ) (X : OrthogonalSpectrum K) : Prop :=
  ∀ H k, k < n → IsEmpty (π H k X)
abbrev MainIsConnected := @IsConnected

/-- 
Geometric fixed-point connectivity condition at slice level `n`.
-/
def MainGeometricFixedPointCondition (π : HomotopyGroupData G)
    (O : IncompleteTransferSystem G) (d : DimensionFunction G)
    (n : ℤ) (X : OrthogonalSpectrum G) : Prop :=
  ∀ (H : Subgroup G),
    MainIsConnected π (d O H n)
      (GeometricFixedPoints (G := G) H X)

/-- Global version: geometric fixed-point condition holds for all levels/objects. -/
def MainGlobalGeometricFixedPointCondition (π : HomotopyGroupData G)
    (O : IncompleteTransferSystem G) (d : DimensionFunction G) : Prop :=
  ∀ n : ℤ, ∀ X : OrthogonalSpectrum G,
    MainGeometricFixedPointCondition (G := G) π O d n X

theorem mainPhi_preservesIsotropySeparated
    (D : IsotropySeparationData G)
    (H : Subgroup G) (F : SubgroupFamily G) (X : D.spectrum)
    (hSep : IsIsotropySeparated D F X) :
    D.cofiber (D.smash (D.phi H (D.eFamily F)) (D.phi H X)) (D.phi H X) =
      D.smash (D.phi H (D.eTildeFamily F)) (D.phi H X) := by
  exact phi_preserves_isIsotropySeparated D H F X hSep

theorem mainPhi_cofiberDiagonal_of_orthogonality
    (D : IsotropySeparationData G)
    (H : Subgroup G) (F : SubgroupFamily G) (X : D.spectrum)
    (hOrth : IsPhiFamilyOrthogonal D H F X) :
    D.cofiber (D.phi H X) (D.phi H X) =
      D.smash (D.phi H (D.eTildeFamily F)) (D.phi H X) := by
  exact cofiber_diagonal_of_phiFamilyOrthogonal D H F X hOrth

/--
Closure package: geometric fixed-point criterion holds for generators and
is preserved under localizing operations.
-/
structure MainFixedPointClosureAxioms (M : SliceCellModel G) (π : HomotopyGroupData G)
    (O : IncompleteTransferSystem G) (d : DimensionFunction G) : Prop where
  generators :
    ∀ {n : ℤ} {c : MainSliceCellData G},
      c ∈ MainSliceCells (G := G) O d n →
        MainGeometricFixedPointCondition (G := G) π O d n (M.cellObj c)
  zero :
    ∀ n : ℤ, MainGeometricFixedPointCondition (G := G) π O d n (ZeroSpectrum G)
  susp :
    ∀ {n : ℤ} {X : OrthogonalSpectrum G},
      MainGeometricFixedPointCondition (G := G) π O d n X →
        MainGeometricFixedPointCondition (G := G) π O d n (SuspSpectrum X)
  cofiber :
    ∀ {n : ℤ} {X Y : OrthogonalSpectrum G},
      MainGeometricFixedPointCondition (G := G) π O d n X →
      MainGeometricFixedPointCondition (G := G) π O d n Y →
        MainGeometricFixedPointCondition (G := G) π O d n (CofiberSpectrum X Y)
  colim :
    ∀ {n : ℤ} {ι : Type u} (F : ι → OrthogonalSpectrum G),
      (∀ i, MainGeometricFixedPointCondition (G := G) π O d n (F i)) →
        MainGeometricFixedPointCondition (G := G) π O d n (ColimSpectrum F)

theorem mainFixedPointClosureAxioms_of_global
    (M : SliceCellModel G)
    (π : HomotopyGroupData G)
    (O : IncompleteTransferSystem G) (d : DimensionFunction G)
    (hGlobal : MainGlobalGeometricFixedPointCondition (G := G) π O d) :
    MainFixedPointClosureAxioms (G := G) M π O d where
  generators := by
    intro n c hc
    let _ := hc
    exact hGlobal n (M.cellObj c)
  zero := by
    intro n
    exact hGlobal n (ZeroSpectrum G)
  susp := by
    intro n X hX
    let _ := hX
    exact hGlobal n (SuspSpectrum X)
  cofiber := by
    intro n X Y hX hY
    let _ := hX
    let _ := hY
    exact hGlobal n (CofiberSpectrum X Y)
  colim := by
    intro n ι F hF
    let _ := hF
    exact hGlobal n (ColimSpectrum F)

/--
Connectivity stability package on the ambient orthogonal-spectrum model.
These are the non-equivariant closure properties used to build
`MainFixedPointClosureAxioms`.
-/
structure MainConnectednessAxioms (π : HomotopyGroupData G) : Prop where
  of_levelwiseEquiv :
    ∀ {t : ℤ} {X Y : OrthogonalSpectrum G},
      LevelwiseEquiv X Y →
      MainIsConnected π t X →
      MainIsConnected π t Y
  susp :
    ∀ {t : ℤ} {X : OrthogonalSpectrum G},
      MainIsConnected π t X →
      MainIsConnected π t (SuspSpectrum X)
  cofiber :
    ∀ {t : ℤ} {X Y : OrthogonalSpectrum G},
      MainIsConnected π t X →
      MainIsConnected π t Y →
      MainIsConnected π t (CofiberSpectrum X Y)
  colim :
    ∀ {t : ℤ} {ι : Type u} (F : ι → OrthogonalSpectrum G),
      (∀ i, MainIsConnected π t (F i)) →
      MainIsConnected π t (ColimSpectrum F)

/--
Connectedness stability package with explicit zero-spectrum connectivity.
This removes a separate `hZero` assumption when building fixed-point closure.
-/
structure MainConnectednessAxiomsWithZero (π : HomotopyGroupData G) : Prop extends
    MainConnectednessAxioms (G := G) π where
  zero : ∀ t : ℤ, MainIsConnected π t (ZeroSpectrum G)

/--
Generator-level fixed-point condition packaged on generator objects directly.
This avoids exposing cell-level witnesses at call sites.
-/
def MainGeneratorGeometricCondition (M : SliceCellModel G)
    (π : HomotopyGroupData G) (O : IncompleteTransferSystem G)
    (d : DimensionFunction G) : Prop :=
  ∀ {n : ℤ} {X : OrthogonalSpectrum G},
    X ∈ MainSliceGenerators (G := G) M O d n →
      MainGeometricFixedPointCondition (G := G) π O d n X

theorem mainGeneratorGeometricCondition_of_cells
    (M : SliceCellModel G)
    (π : HomotopyGroupData G) (O : IncompleteTransferSystem G)
    (d : DimensionFunction G)
    (hGenerators :
      ∀ {n : ℤ} {c : MainSliceCellData G},
        c ∈ MainSliceCells (G := G) O d n →
          MainGeometricFixedPointCondition (G := G) π O d n (M.cellObj c)) :
    MainGeneratorGeometricCondition (G := G) M π O d := by
  intro n X hX
  rcases hX with ⟨c, hc, rfl⟩
  exact hGenerators hc

theorem mainGeneratorGeometricCondition_of_global
    (M : SliceCellModel G)
    (π : HomotopyGroupData G) (O : IncompleteTransferSystem G)
    (d : DimensionFunction G)
    (hGlobal : MainGlobalGeometricFixedPointCondition (G := G) π O d) :
    MainGeneratorGeometricCondition (G := G) M π O d := by
  intro n X hX
  let _ := hX
  exact hGlobal n X

theorem mainCellGeneratorCondition_of_generatorCondition
    (M : SliceCellModel G)
    (π : HomotopyGroupData G) (O : IncompleteTransferSystem G)
    (d : DimensionFunction G)
    (hGen : MainGeneratorGeometricCondition (G := G) M π O d) :
    ∀ {n : ℤ} {c : MainSliceCellData G},
      c ∈ MainSliceCells (G := G) O d n →
        MainGeometricFixedPointCondition (G := G) π O d n (M.cellObj c) := by
  intro n c hc
  exact hGen ⟨c, hc, rfl⟩

theorem mainFixedPointClosureAxioms_of_connectedness
    (M : SliceCellModel G)
    (π : HomotopyGroupData G)
    (O : IncompleteTransferSystem G) (d : DimensionFunction G)
    (hGenerators :
      ∀ {n : ℤ} {c : MainSliceCellData G},
        c ∈ MainSliceCells (G := G) O d n →
          MainGeometricFixedPointCondition (G := G) π O d n (M.cellObj c))
    (hZero :
      ∀ n : ℤ,
        MainGeometricFixedPointCondition (G := G) π O d n (ZeroSpectrum G))
    (hConn : MainConnectednessAxioms (G := G) π) :
    MainFixedPointClosureAxioms (G := G) M π O d := by
  refine
    { generators := ?_
      zero := ?_
      susp := ?_
      cofiber := ?_
      colim := ?_ }
  · intro n c hc
    exact hGenerators hc
  · intro n
    exact hZero n
  · intro n X hX H
    have hConnected :
        MainIsConnected π (d O H n) (GeometricFixedPoints (G := G) H X) := hX H
    have hSusp :
        MainIsConnected π (d O H n)
          (SuspSpectrum (GeometricFixedPoints (G := G) H X)) :=
      hConn.susp hConnected
    simpa [geometricFixedPoints_susp (G := G) H X] using hSusp
  · intro n X Y hX hY H
    have hConnectedX :
        MainIsConnected π (d O H n) (GeometricFixedPoints (G := G) H X) := hX H
    have hConnectedY :
        MainIsConnected π (d O H n) (GeometricFixedPoints (G := G) H Y) := hY H
    have hConnectedCofiber :
        MainIsConnected π (d O H n)
          (CofiberSpectrum
            (GeometricFixedPoints (G := G) H X)
            (GeometricFixedPoints (G := G) H Y)) :=
      hConn.cofiber hConnectedX hConnectedY
    have hLvl :
        LevelwiseEquiv
          (GeometricFixedPoints (G := G) H (CofiberSpectrum X Y))
          (CofiberSpectrum
            (GeometricFixedPoints (G := G) H X)
            (GeometricFixedPoints (G := G) H Y)) :=
      geometricFixedPoints_cofiber_levelwiseEquiv (G := G) H X Y
    exact hConn.of_levelwiseEquiv (LevelwiseEquiv.symm hLvl) hConnectedCofiber
  · intro n ι F hF H
    have hConnectedFam :
        ∀ i, MainIsConnected π (d O H n) (GeometricFixedPoints (G := G) H (F i)) :=
      fun i => hF i H
    have hConnectedColim :
        MainIsConnected π (d O H n)
          (ColimSpectrum (fun i => GeometricFixedPoints (G := G) H (F i))) :=
      hConn.colim _ hConnectedFam
    have hLvl :
        LevelwiseEquiv
          (GeometricFixedPoints (G := G) H (ColimSpectrum F))
          (ColimSpectrum (fun i => GeometricFixedPoints (G := G) H (F i))) :=
      geometricFixedPoints_colim_levelwiseEquiv (G := G) H F
    exact hConn.of_levelwiseEquiv (LevelwiseEquiv.symm hLvl) hConnectedColim

theorem mainFixedPointClosureAxioms_of_connectednessWithZero
    (M : SliceCellModel G)
    (π : HomotopyGroupData G)
    (O : IncompleteTransferSystem G) (d : DimensionFunction G)
    (hGenerators :
      ∀ {n : ℤ} {c : MainSliceCellData G},
        c ∈ MainSliceCells (G := G) O d n →
          MainGeometricFixedPointCondition (G := G) π O d n (M.cellObj c))
    (hConn : MainConnectednessAxiomsWithZero (G := G) π) :
    MainFixedPointClosureAxioms (G := G) M π O d := by
  refine mainFixedPointClosureAxioms_of_connectedness (G := G) M π O d hGenerators ?hZero
    hConn.toMainConnectednessAxioms
  intro n H
  have hZeroConnected :
      MainIsConnected π (d O H n) (ZeroSpectrum G) :=
    hConn.zero (d O H n)
  have hLvl :
      LevelwiseEquiv
        (GeometricFixedPoints (G := G) H (ZeroSpectrum G))
        (ZeroSpectrum G) :=
    geometricFixedPoints_zero_levelwiseEquiv (G := G) H
  exact hConn.toMainConnectednessAxioms.of_levelwiseEquiv
    (LevelwiseEquiv.symm hLvl) hZeroConnected

theorem mainFixedPointClosureAxioms_of_generatorCondition_and_connectednessWithZero
    (M : SliceCellModel G)
    (π : HomotopyGroupData G)
    (O : IncompleteTransferSystem G) (d : DimensionFunction G)
    (hGen : MainGeneratorGeometricCondition (G := G) M π O d)
    (hConn : MainConnectednessAxiomsWithZero (G := G) π) :
    MainFixedPointClosureAxioms (G := G) M π O d := by
  refine mainFixedPointClosureAxioms_of_connectednessWithZero (G := G) M π O d ?hGenerators hConn
  intro n c hc
  exact hGen ⟨c, hc, rfl⟩

/--
Unified entry for forward-direction closure hypotheses:
either a global geometric fixed-point condition or
generator-level condition plus connectedness closure axioms.
-/
inductive MainForwardClosurePath (M : SliceCellModel G)
    (π : HomotopyGroupData G) (O : IncompleteTransferSystem G)
    (d : DimensionFunction G) : Prop where
  | global :
      MainGlobalGeometricFixedPointCondition (G := G) π O d →
        MainForwardClosurePath M π O d
  | generator :
      MainGeneratorGeometricCondition (G := G) M π O d →
      MainConnectednessAxiomsWithZero (G := G) π →
        MainForwardClosurePath M π O d

theorem mainFixedPointClosureAxioms_of_forwardPath
    (M : SliceCellModel G)
    (π : HomotopyGroupData G)
    (O : IncompleteTransferSystem G) (d : DimensionFunction G)
    (hForward : MainForwardClosurePath M π O d) :
    MainFixedPointClosureAxioms (G := G) M π O d := by
  cases hForward with
  | global hGlobal =>
      exact mainFixedPointClosureAxioms_of_global (G := G) M π O d hGlobal
  | generator hGen hConn =>
      exact mainFixedPointClosureAxioms_of_generatorCondition_and_connectednessWithZero
        (G := G) M π O d hGen hConn

lemma mainSliceConnectivity_implies_geometricFixedPoints
    (M : SliceCellModel G)
    (π : HomotopyGroupData G)
    (O : IncompleteTransferSystem G) (d : DimensionFunction G)
    (hClosure : MainFixedPointClosureAxioms (G := G) M π O d)
    {n : ℤ} {X : OrthogonalSpectrum G}
    (hX : IsSliceConnected (G := G) M O d n X) :
    MainGeometricFixedPointCondition (G := G) π O d n X := by
  unfold IsSliceConnected at hX
  induction hX with
  | of_generator hGen =>
      rcases hGen with ⟨c, hc, rfl⟩
      exact hClosure.generators hc
  | zero =>
      exact hClosure.zero n
  | susp hMem ih =>
      exact hClosure.susp ih
  | cofiber hA hB ihA ihB =>
      exact hClosure.cofiber ihA ihB
  | colim F hFam ih =>
      exact hClosure.colim F ih

theorem MainSliceConnectivity_implies_GeometricFixedPoints_of_forwardPath
    (M : SliceCellModel G)
    (π : HomotopyGroupData G)
    (O : IncompleteTransferSystem G) (d : DimensionFunction G)
    (hForward : MainForwardClosurePath M π O d)
    {n : ℤ} {X : OrthogonalSpectrum G}
    (hX : IsSliceConnected (G := G) M O d n X) :
    MainGeometricFixedPointCondition (G := G) π O d n X := by
  exact mainSliceConnectivity_implies_geometricFixedPoints (G := G) M π O d
    (mainFixedPointClosureAxioms_of_forwardPath (G := G) M π O d hForward) hX

theorem MainSliceConnectivity_implies_GeometricFixedPoints_core
    (M : SliceCellModel G)
    (π : HomotopyGroupData G)
    (O : IncompleteTransferSystem G) (d : DimensionFunction G)
    (hGen : MainGeneratorGeometricCondition (G := G) M π O d)
    (hConn : MainConnectednessAxiomsWithZero (G := G) π)
    {n : ℤ} {X : OrthogonalSpectrum G}
    (hX : IsSliceConnected (G := G) M O d n X) :
    MainGeometricFixedPointCondition (G := G) π O d n X := by
  exact MainSliceConnectivity_implies_GeometricFixedPoints_of_forwardPath (G := G) M π O d
    (.generator hGen hConn) hX

theorem MainSliceConnectivity_implies_GeometricFixedPoints_of_cells_core
    (M : SliceCellModel G)
    (π : HomotopyGroupData G)
    (O : IncompleteTransferSystem G) (d : DimensionFunction G)
    (hGenerators :
      ∀ {n : ℤ} {c : MainSliceCellData G},
        c ∈ MainSliceCells (G := G) O d n →
          MainGeometricFixedPointCondition (G := G) π O d n (M.cellObj c))
    (hConn : MainConnectednessAxiomsWithZero (G := G) π)
    {n : ℤ} {X : OrthogonalSpectrum G}
    (hX : IsSliceConnected (G := G) M O d n X) :
    MainGeometricFixedPointCondition (G := G) π O d n X := by
  exact MainSliceConnectivity_implies_GeometricFixedPoints_core (G := G) M π O d
    (mainGeneratorGeometricCondition_of_cells (G := G) M π O d hGenerators)
    hConn hX

theorem MainSliceConnectivity_implies_GeometricFixedPoints_of_global
    (M : SliceCellModel G)
    (π : HomotopyGroupData G)
    (O : IncompleteTransferSystem G) (d : DimensionFunction G)
    (hGlobal : MainGlobalGeometricFixedPointCondition (G := G) π O d)
    {n : ℤ} {X : OrthogonalSpectrum G}
    (hX : IsSliceConnected (G := G) M O d n X) :
    MainGeometricFixedPointCondition (G := G) π O d n X := by
  exact MainSliceConnectivity_implies_GeometricFixedPoints_of_forwardPath
    (G := G) M π O d (.global hGlobal) hX

theorem MainOperadSliceConnectivity_implies_GeometricFixedPoints_of_cells_core
    (M : SliceCellModel G)
    (π : HomotopyGroupData G)
    (Oinf : NInfinityOperad G) (d : DimensionFunction G)
    (hGenerators :
      ∀ {n : ℤ} {c : MainSliceCellData G},
        c ∈ MainSliceCells (G := G) Oinf.transferSystem d n →
          MainGeometricFixedPointCondition
            (G := G) π Oinf.transferSystem d n (M.cellObj c))
    (hConn : MainConnectednessAxiomsWithZero (G := G) π)
    {n : ℤ} {X : OrthogonalSpectrum G}
    (hX : IsSliceConnected (G := G) M Oinf.transferSystem d n X) :
    MainGeometricFixedPointCondition (G := G) π Oinf.transferSystem d n X := by
  exact MainSliceConnectivity_implies_GeometricFixedPoints_of_cells_core
    (G := G) M π Oinf.transferSystem d hGenerators hConn hX

theorem MainOperadSliceConnectivity_implies_GeometricFixedPoints_core
    (M : SliceCellModel G)
    (π : HomotopyGroupData G)
    (Oinf : NInfinityOperad G) (d : DimensionFunction G)
    (hGen : MainGeneratorGeometricCondition (G := G) M π Oinf.transferSystem d)
    (hConn : MainConnectednessAxiomsWithZero (G := G) π)
    {n : ℤ} {X : OrthogonalSpectrum G}
    (hX : IsSliceConnected (G := G) M Oinf.transferSystem d n X) :
    MainGeometricFixedPointCondition (G := G) π Oinf.transferSystem d n X := by
  exact MainSliceConnectivity_implies_GeometricFixedPoints_core
    (G := G) M π Oinf.transferSystem d hGen hConn hX

theorem MainIndexingSystemSliceConnectivity_implies_GeometricFixedPoints_of_cells_core
    (M : SliceCellModel G)
    (π : HomotopyGroupData G)
    (I : IndexingSystem G) (d : DimensionFunction G)
    (hGenerators :
      ∀ {n : ℤ} {c : MainSliceCellData G},
        c ∈ MainSliceCells (G := G) I.toTransferSystem d n →
          MainGeometricFixedPointCondition
            (G := G) π I.toTransferSystem d n (M.cellObj c))
    (hConn : MainConnectednessAxiomsWithZero (G := G) π)
    {n : ℤ} {X : OrthogonalSpectrum G}
    (hX : IsSliceConnected (G := G) M I.toTransferSystem d n X) :
    MainGeometricFixedPointCondition (G := G) π I.toTransferSystem d n X := by
  exact MainSliceConnectivity_implies_GeometricFixedPoints_of_cells_core
    (G := G) M π I.toTransferSystem d hGenerators hConn hX

theorem MainIndexingSystemSliceConnectivity_implies_GeometricFixedPoints_core
    (M : SliceCellModel G)
    (π : HomotopyGroupData G)
    (I : IndexingSystem G) (d : DimensionFunction G)
    (hGen : MainGeneratorGeometricCondition (G := G) M π I.toTransferSystem d)
    (hConn : MainConnectednessAxiomsWithZero (G := G) π)
    {n : ℤ} {X : OrthogonalSpectrum G}
    (hX : IsSliceConnected (G := G) M I.toTransferSystem d n X) :
    MainGeometricFixedPointCondition (G := G) π I.toTransferSystem d n X := by
  exact MainSliceConnectivity_implies_GeometricFixedPoints_core
    (G := G) M π I.toTransferSystem d hGen hConn hX

/--
Reverse direction package (hard step):
if the geometric fixed-point criterion holds, then the object is slice-connected.
-/
structure MainReconstructionAxiom (M : SliceCellModel G) (π : HomotopyGroupData G)
    (O : IncompleteTransferSystem G) (d : DimensionFunction G) : Prop where
  of_fixedPoints :
    ∀ {n : ℤ} {X : OrthogonalSpectrum G},
      MainGeometricFixedPointCondition (G := G) π O d n X →
        IsSliceConnected (G := G) M O d n X

/--
Constructive reverse-direction package:
from the fixed-point criterion, produce an explicit slice syntax expression.
-/
structure MainSyntaxReconstructionAxiom (M : SliceCellModel G) (π : HomotopyGroupData G)
    (O : IncompleteTransferSystem G) (d : DimensionFunction G) : Prop where
  toExpr :
    ∀ {n : ℤ} {X : OrthogonalSpectrum G},
      MainGeometricFixedPointCondition (G := G) π O d n X →
        ∃ e : MainSliceExpr (G := G) M O d n, MainSliceExpr.eval M O d n e = X

/--
Reverse-direction scaffold using isotropy-separation orthogonality:
geometric fixed-point connectivity gives orthogonality, orthogonality gives a
diagonal cofiber equation, and that equation yields a slice expression.
-/
structure MainIsotropyOrthogonalSyntaxReconstruction
    (M : SliceCellModel G) (π : HomotopyGroupData G)
    (O : IncompleteTransferSystem G) (d : DimensionFunction G) where
  D : IsotropySeparationData G
  lift : OrthogonalSpectrum G → D.spectrum
  family : ℤ → OrthogonalSpectrum G → SubgroupFamily G
  orthogonal_of_fixedPoints :
    ∀ {n : ℤ} {X : OrthogonalSpectrum G},
      MainGeometricFixedPointCondition (G := G) π O d n X →
        ∀ H : Subgroup G, IsPhiFamilyOrthogonal D H (family n X) (lift X)
  expr_of_diagonal :
    ∀ {n : ℤ} {X : OrthogonalSpectrum G}
      (_hGeo : MainGeometricFixedPointCondition (G := G) π O d n X),
      (∀ H : Subgroup G,
        D.cofiber (D.phi H (lift X)) (D.phi H (lift X)) =
          D.smash (D.phi H (D.eTildeFamily (family n X))) (D.phi H (lift X))) →
        ∃ e : MainSliceExpr (G := G) M O d n, MainSliceExpr.eval M O d n e = X

theorem mainSyntaxReconstructionAxiom_of_isotropyOrthogonal
    (M : SliceCellModel G) (π : HomotopyGroupData G)
    (O : IncompleteTransferSystem G) (d : DimensionFunction G)
    (R : MainIsotropyOrthogonalSyntaxReconstruction (G := G) M π O d) :
    MainSyntaxReconstructionAxiom (G := G) M π O d := by
  refine ⟨?_⟩
  intro n X hGeo
  have hOrth :
      ∀ H : Subgroup G, IsPhiFamilyOrthogonal R.D H (R.family n X) (R.lift X) :=
    R.orthogonal_of_fixedPoints hGeo
  have hDiag :
      ∀ H : Subgroup G,
        R.D.cofiber (R.D.phi H (R.lift X)) (R.D.phi H (R.lift X)) =
          R.D.smash (R.D.phi H (R.D.eTildeFamily (R.family n X))) (R.D.phi H (R.lift X)) := by
    intro H
    exact mainPhi_cofiberDiagonal_of_orthogonality
      (G := G) (D := R.D) (H := H) (F := R.family n X) (X := R.lift X) (hOrth H)
  exact R.expr_of_diagonal hGeo hDiag

theorem mainReconstructionAxiom_of_isotropyOrthogonal
    (M : SliceCellModel G) (π : HomotopyGroupData G)
    (O : IncompleteTransferSystem G) (d : DimensionFunction G)
    (R : MainIsotropyOrthogonalSyntaxReconstruction (G := G) M π O d) :
    MainReconstructionAxiom (G := G) M π O d := by
  refine ⟨?_⟩
  intro n X hGeo
  rcases (mainSyntaxReconstructionAxiom_of_isotropyOrthogonal (G := G) M π O d R).toExpr
      (n := n) (X := X) hGeo with ⟨e, rfl⟩
  exact MainSliceExpr.eval_isSliceConnected (G := G) M O d n e

/--
Surjective syntax presentation at each slice level:
every object is represented by some slice expression.
-/
def MainSyntaxSurjective (M : SliceCellModel G)
    (O : IncompleteTransferSystem G) (d : DimensionFunction G) : Prop :=
  ∀ n : ℤ, ∀ X : OrthogonalSpectrum G,
    ∃ e : MainSliceExpr (G := G) M O d n, MainSliceExpr.eval M O d n e = X

/--
Strong generator-surjectivity hypothesis at level `n`:
every object is already a single admissible slice cell.
-/
def MainCellSurjectiveAtLevel (M : SliceCellModel G)
    (O : IncompleteTransferSystem G) (d : DimensionFunction G) : Prop :=
  ∀ n : ℤ, ∀ X : OrthogonalSpectrum G,
    ∃ c : MainSliceCellData G, c ∈ MainSliceCells (G := G) O d n ∧ M.cellObj c = X

/--
Constructive codec for slice-cell realizations:
encode each object as an admissible cell with exact evaluation.
-/
structure MainCellRealization (M : SliceCellModel G)
    (O : IncompleteTransferSystem G) (d : DimensionFunction G) where
  encode : ℤ → OrthogonalSpectrum G → MainSliceCellData G
  encode_mem :
    ∀ n X, encode n X ∈ MainSliceCells (G := G) O d n
  encode_eval :
    ∀ n X, M.cellObj (encode n X) = X

theorem mainCellSurjectiveAtLevel_of_realization
    (M : SliceCellModel G)
    (O : IncompleteTransferSystem G) (d : DimensionFunction G)
    (R : MainCellRealization (G := G) M O d) :
    MainCellSurjectiveAtLevel (G := G) M O d := by
  intro n X
  refine ⟨R.encode n X, R.encode_mem n X, R.encode_eval n X⟩

noncomputable def mainCellRealization_of_cellSurjectiveAtLevel
    (M : SliceCellModel G)
    (O : IncompleteTransferSystem G) (d : DimensionFunction G)
    (hCellSurj : MainCellSurjectiveAtLevel (G := G) M O d) :
    MainCellRealization (G := G) M O d where
  encode := fun n X => Classical.choose (hCellSurj n X)
  encode_mem := by
    intro n X
    exact (Classical.choose_spec (hCellSurj n X)).1
  encode_eval := by
    intro n X
    exact (Classical.choose_spec (hCellSurj n X)).2

theorem mainReconstructionAxiom_of_syntaxReconstruction
    (M : SliceCellModel G)
    (π : HomotopyGroupData G)
    (O : IncompleteTransferSystem G) (d : DimensionFunction G)
    (hSyntax : MainSyntaxReconstructionAxiom (G := G) M π O d) :
    MainReconstructionAxiom (G := G) M π O d := by
  refine ⟨?_⟩
  intro n X hGeo
  rcases hSyntax.toExpr (n := n) (X := X) hGeo with ⟨e, rfl⟩
  exact MainSliceExpr.eval_isSliceConnected (G := G) M O d n e

theorem mainSyntaxReconstructionAxiom_of_surjective
    (M : SliceCellModel G)
    (π : HomotopyGroupData G)
    (O : IncompleteTransferSystem G) (d : DimensionFunction G)
    (hSurj : MainSyntaxSurjective (G := G) M O d) :
    MainSyntaxReconstructionAxiom (G := G) M π O d := by
  refine ⟨?_⟩
  intro n X hGeo
  let _ := hGeo
  exact hSurj n X

theorem mainSyntaxSurjective_of_cellSurjectiveAtLevel
    (M : SliceCellModel G)
    (O : IncompleteTransferSystem G) (d : DimensionFunction G)
    (hCellSurj : MainCellSurjectiveAtLevel (G := G) M O d) :
    MainSyntaxSurjective (G := G) M O d := by
  intro n X
  rcases hCellSurj n X with ⟨c, hc, hEq⟩
  refine ⟨MainSliceExpr.generator (M := M) (O := O) (d := d) (n := n) c hc, ?_⟩
  simpa [MainSliceExpr.eval] using hEq

theorem mainSyntaxSurjective_of_realization
    (M : SliceCellModel G)
    (O : IncompleteTransferSystem G) (d : DimensionFunction G)
    (R : MainCellRealization (G := G) M O d) :
    MainSyntaxSurjective (G := G) M O d := by
  exact mainSyntaxSurjective_of_cellSurjectiveAtLevel (G := G) M O d
    (mainCellSurjectiveAtLevel_of_realization (G := G) M O d R)

theorem mainSyntaxReconstructionAxiom_of_cellSurjectiveAtLevel
    (M : SliceCellModel G)
    (π : HomotopyGroupData G)
    (O : IncompleteTransferSystem G) (d : DimensionFunction G)
    (hCellSurj : MainCellSurjectiveAtLevel (G := G) M O d) :
    MainSyntaxReconstructionAxiom (G := G) M π O d := by
  exact mainSyntaxReconstructionAxiom_of_surjective (G := G) M π O d
    (mainSyntaxSurjective_of_cellSurjectiveAtLevel (G := G) M O d hCellSurj)

theorem mainReconstructionAxiom_of_cellSurjectiveAtLevel
    (M : SliceCellModel G)
    (π : HomotopyGroupData G)
    (O : IncompleteTransferSystem G) (d : DimensionFunction G)
    (hCellSurj : MainCellSurjectiveAtLevel (G := G) M O d) :
    MainReconstructionAxiom (G := G) M π O d := by
  exact mainReconstructionAxiom_of_syntaxReconstruction (G := G) M π O d
    (mainSyntaxReconstructionAxiom_of_cellSurjectiveAtLevel (G := G) M π O d hCellSurj)

theorem mainReconstructionAxiom_of_realization
    (M : SliceCellModel G)
    (π : HomotopyGroupData G)
    (O : IncompleteTransferSystem G) (d : DimensionFunction G)
    (R : MainCellRealization (G := G) M O d) :
    MainReconstructionAxiom (G := G) M π O d := by
  exact mainReconstructionAxiom_of_cellSurjectiveAtLevel (G := G) M π O d
    (mainCellSurjectiveAtLevel_of_realization (G := G) M O d R)

/--
Conditional cell realization: only objects satisfying the geometric fixed-point
criterion are required to admit admissible cell encodings.
-/
structure MainConditionalCellRealization (M : SliceCellModel G) (π : HomotopyGroupData G)
    (O : IncompleteTransferSystem G) (d : DimensionFunction G) where
  encode :
    ∀ {n : ℤ} {X : OrthogonalSpectrum G},
      MainGeometricFixedPointCondition (G := G) π O d n X →
        MainSliceCellData G
  encode_mem :
    ∀ {n : ℤ} {X : OrthogonalSpectrum G}
      (hGeo : MainGeometricFixedPointCondition (G := G) π O d n X),
      encode hGeo ∈ MainSliceCells (G := G) O d n
  encode_eval :
    ∀ {n : ℤ} {X : OrthogonalSpectrum G}
      (hGeo : MainGeometricFixedPointCondition (G := G) π O d n X),
      M.cellObj (encode hGeo) = X

/--
Conditional surjectivity at each level:
for every object satisfying the geometric fixed-point condition, there exists
an admissible slice cell evaluating to that object.
-/
def MainConditionalCellSurjective (M : SliceCellModel G) (π : HomotopyGroupData G)
    (O : IncompleteTransferSystem G) (d : DimensionFunction G) : Prop :=
  ∀ {n : ℤ} {X : OrthogonalSpectrum G},
    MainGeometricFixedPointCondition (G := G) π O d n X →
      ∃ c : MainSliceCellData G, c ∈ MainSliceCells (G := G) O d n ∧ M.cellObj c = X

theorem mainConditionalCellSurjective_of_realization
    (M : SliceCellModel G)
    (π : HomotopyGroupData G)
    (O : IncompleteTransferSystem G) (d : DimensionFunction G)
    (R : MainCellRealization (G := G) M O d) :
    MainConditionalCellSurjective (G := G) M π O d := by
  intro n X hGeo
  let _ := hGeo
  exact ⟨R.encode n X, R.encode_mem n X, R.encode_eval n X⟩

theorem mainConditionalCellSurjective_of_cellSurjectiveAtLevel
    (M : SliceCellModel G)
    (π : HomotopyGroupData G)
    (O : IncompleteTransferSystem G) (d : DimensionFunction G)
    (hCellSurj : MainCellSurjectiveAtLevel (G := G) M O d) :
    MainConditionalCellSurjective (G := G) M π O d := by
  intro n X hGeo
  let _ := hGeo
  rcases hCellSurj n X with ⟨c, hc, hEval⟩
  exact ⟨c, hc, hEval⟩

noncomputable def mainConditionalCellRealization_of_conditionalCellSurjective
    (M : SliceCellModel G)
    (π : HomotopyGroupData G)
    (O : IncompleteTransferSystem G) (d : DimensionFunction G)
    (hCondSurj : MainConditionalCellSurjective (G := G) M π O d) :
    MainConditionalCellRealization (G := G) M π O d where
  encode := by
    intro n X hGeo
    exact Classical.choose (hCondSurj hGeo)
  encode_mem := by
    intro n X hGeo
    exact (Classical.choose_spec (hCondSurj hGeo)).1
  encode_eval := by
    intro n X hGeo
    exact (Classical.choose_spec (hCondSurj hGeo)).2

def mainConditionalCellRealization_of_realization
    (M : SliceCellModel G)
    (π : HomotopyGroupData G)
    (O : IncompleteTransferSystem G) (d : DimensionFunction G)
    (R : MainCellRealization (G := G) M O d) :
    MainConditionalCellRealization (G := G) M π O d where
  encode := by
    intro n X hGeo
    let _ := hGeo
    exact R.encode n X
  encode_mem := by
    intro n X hGeo
    let _ := hGeo
    exact R.encode_mem n X
  encode_eval := by
    intro n X hGeo
    let _ := hGeo
    exact R.encode_eval n X

noncomputable def mainConditionalCellRealization_of_cellSurjectiveAtLevel
    (M : SliceCellModel G)
    (π : HomotopyGroupData G)
    (O : IncompleteTransferSystem G) (d : DimensionFunction G)
    (hCellSurj : MainCellSurjectiveAtLevel (G := G) M O d) :
    MainConditionalCellRealization (G := G) M π O d :=
  mainConditionalCellRealization_of_realization (G := G) M π O d
    (mainCellRealization_of_cellSurjectiveAtLevel (G := G) M O d hCellSurj)

theorem mainSyntaxReconstructionAxiom_of_conditionalCellRealization
    (M : SliceCellModel G)
    (π : HomotopyGroupData G)
    (O : IncompleteTransferSystem G) (d : DimensionFunction G)
    (R : MainConditionalCellRealization (G := G) M π O d) :
    MainSyntaxReconstructionAxiom (G := G) M π O d := by
  refine ⟨?_⟩
  intro n X hGeo
  let c := R.encode hGeo
  have hc : c ∈ MainSliceCells (G := G) O d n := R.encode_mem hGeo
  refine ⟨MainSliceExpr.generator (M := M) (O := O) (d := d) (n := n) c hc, ?_⟩
  simpa [MainSliceExpr.eval, c] using R.encode_eval hGeo

theorem mainSyntaxReconstructionAxiom_of_conditionalCellSurjective
    (M : SliceCellModel G)
    (π : HomotopyGroupData G)
    (O : IncompleteTransferSystem G) (d : DimensionFunction G)
    (hCondSurj : MainConditionalCellSurjective (G := G) M π O d) :
    MainSyntaxReconstructionAxiom (G := G) M π O d := by
  exact mainSyntaxReconstructionAxiom_of_conditionalCellRealization (G := G) M π O d
    (mainConditionalCellRealization_of_conditionalCellSurjective (G := G) M π O d hCondSurj)

def mainIsotropyOrthogonalSyntaxReconstruction_of_conditionalCellRealization
    (M : SliceCellModel G)
    (π : HomotopyGroupData G)
    (O : IncompleteTransferSystem G) (d : DimensionFunction G)
    (D : IsotropySeparationData G)
    (lift : OrthogonalSpectrum G → D.spectrum)
    (family : ℤ → OrthogonalSpectrum G → SubgroupFamily G)
    (hOrth :
      ∀ {n : ℤ} {X : OrthogonalSpectrum G},
        MainGeometricFixedPointCondition (G := G) π O d n X →
          ∀ H : Subgroup G, IsPhiFamilyOrthogonal D H (family n X) (lift X))
    (R : MainConditionalCellRealization (G := G) M π O d) :
    MainIsotropyOrthogonalSyntaxReconstruction (G := G) M π O d where
  D := D
  lift := lift
  family := family
  orthogonal_of_fixedPoints := hOrth
  expr_of_diagonal := by
    intro n X hGeo hDiag
    let _ := hDiag
    let c := R.encode hGeo
    have hc : c ∈ MainSliceCells (G := G) O d n := R.encode_mem hGeo
    refine ⟨MainSliceExpr.generator (M := M) (O := O) (d := d) (n := n) c hc, ?_⟩
    simpa [MainSliceExpr.eval, c] using R.encode_eval hGeo

theorem mainSyntaxReconstructionAxiom_of_conditionalCellRealization_and_isotropyOrthogonal
    (M : SliceCellModel G)
    (π : HomotopyGroupData G)
    (O : IncompleteTransferSystem G) (d : DimensionFunction G)
    (D : IsotropySeparationData G)
    (lift : OrthogonalSpectrum G → D.spectrum)
    (family : ℤ → OrthogonalSpectrum G → SubgroupFamily G)
    (hOrth :
      ∀ {n : ℤ} {X : OrthogonalSpectrum G},
        MainGeometricFixedPointCondition (G := G) π O d n X →
          ∀ H : Subgroup G, IsPhiFamilyOrthogonal D H (family n X) (lift X))
    (R : MainConditionalCellRealization (G := G) M π O d) :
    MainSyntaxReconstructionAxiom (G := G) M π O d := by
  exact mainSyntaxReconstructionAxiom_of_isotropyOrthogonal (G := G) M π O d
    (mainIsotropyOrthogonalSyntaxReconstruction_of_conditionalCellRealization
      (G := G) M π O d D lift family hOrth R)

theorem mainReconstructionAxiom_of_conditionalCellRealization
    (M : SliceCellModel G)
    (π : HomotopyGroupData G)
    (O : IncompleteTransferSystem G) (d : DimensionFunction G)
    (R : MainConditionalCellRealization (G := G) M π O d) :
    MainReconstructionAxiom (G := G) M π O d := by
  exact mainReconstructionAxiom_of_syntaxReconstruction (G := G) M π O d
    (mainSyntaxReconstructionAxiom_of_conditionalCellRealization (G := G) M π O d R)

theorem mainReconstructionAxiom_of_conditionalCellSurjective
    (M : SliceCellModel G)
    (π : HomotopyGroupData G)
    (O : IncompleteTransferSystem G) (d : DimensionFunction G)
    (hCondSurj : MainConditionalCellSurjective (G := G) M π O d) :
    MainReconstructionAxiom (G := G) M π O d := by
  exact mainReconstructionAxiom_of_conditionalCellRealization (G := G) M π O d
    (mainConditionalCellRealization_of_conditionalCellSurjective (G := G) M π O d hCondSurj)

theorem mainReconstructionAxiom_of_conditionalCellRealization_and_isotropyOrthogonal
    (M : SliceCellModel G)
    (π : HomotopyGroupData G)
    (O : IncompleteTransferSystem G) (d : DimensionFunction G)
    (D : IsotropySeparationData G)
    (lift : OrthogonalSpectrum G → D.spectrum)
    (family : ℤ → OrthogonalSpectrum G → SubgroupFamily G)
    (hOrth :
      ∀ {n : ℤ} {X : OrthogonalSpectrum G},
        MainGeometricFixedPointCondition (G := G) π O d n X →
          ∀ H : Subgroup G, IsPhiFamilyOrthogonal D H (family n X) (lift X))
    (R : MainConditionalCellRealization (G := G) M π O d) :
    MainReconstructionAxiom (G := G) M π O d := by
  exact mainReconstructionAxiom_of_isotropyOrthogonal (G := G) M π O d
    (mainIsotropyOrthogonalSyntaxReconstruction_of_conditionalCellRealization
      (G := G) M π O d D lift family hOrth R)

theorem mainReconstructionAxiom_of_conditionalCellSurjective_and_isotropyOrthogonal
    (M : SliceCellModel G)
    (π : HomotopyGroupData G)
    (O : IncompleteTransferSystem G) (d : DimensionFunction G)
    (D : IsotropySeparationData G)
    (lift : OrthogonalSpectrum G → D.spectrum)
    (family : ℤ → OrthogonalSpectrum G → SubgroupFamily G)
    (hOrth :
      ∀ {n : ℤ} {X : OrthogonalSpectrum G},
        MainGeometricFixedPointCondition (G := G) π O d n X →
          ∀ H : Subgroup G, IsPhiFamilyOrthogonal D H (family n X) (lift X))
    (hCondSurj : MainConditionalCellSurjective (G := G) M π O d) :
    MainReconstructionAxiom (G := G) M π O d := by
  exact mainReconstructionAxiom_of_conditionalCellRealization_and_isotropyOrthogonal
    (G := G) M π O d D lift family hOrth
    (mainConditionalCellRealization_of_conditionalCellSurjective (G := G) M π O d hCondSurj)

/--
Bridge package for isotropy-separation orthogonality data.
This reduces theorem-call parameter noise (`D/lift/family/hOrth`).
-/
structure MainIsotropyOrthogonalBridge (M : SliceCellModel G) (π : HomotopyGroupData G)
    (O : IncompleteTransferSystem G) (d : DimensionFunction G) where
  D : IsotropySeparationData G
  lift : OrthogonalSpectrum G → D.spectrum
  family : ℤ → OrthogonalSpectrum G → SubgroupFamily G
  orthogonal_of_fixedPoints :
    ∀ {n : ℤ} {X : OrthogonalSpectrum G},
      MainGeometricFixedPointCondition (G := G) π O d n X →
        ∀ H : Subgroup G, IsPhiFamilyOrthogonal D H (family n X) (lift X)

def mainIsotropyOrthogonalSyntaxReconstruction_of_bridge_and_conditionalCellRealization
    (M : SliceCellModel G)
    (π : HomotopyGroupData G)
    (O : IncompleteTransferSystem G) (d : DimensionFunction G)
    (B : MainIsotropyOrthogonalBridge (G := G) M π O d)
    (R : MainConditionalCellRealization (G := G) M π O d) :
    MainIsotropyOrthogonalSyntaxReconstruction (G := G) M π O d :=
  mainIsotropyOrthogonalSyntaxReconstruction_of_conditionalCellRealization
    (G := G) M π O d B.D B.lift B.family B.orthogonal_of_fixedPoints R

theorem mainReconstructionAxiom_of_conditionalCellSurjective_and_bridge
    (M : SliceCellModel G)
    (π : HomotopyGroupData G)
    (O : IncompleteTransferSystem G) (d : DimensionFunction G)
    (B : MainIsotropyOrthogonalBridge (G := G) M π O d)
    (hCondSurj : MainConditionalCellSurjective (G := G) M π O d) :
    MainReconstructionAxiom (G := G) M π O d := by
  exact mainReconstructionAxiom_of_conditionalCellSurjective_and_isotropyOrthogonal
    (G := G) M π O d B.D B.lift B.family B.orthogonal_of_fixedPoints hCondSurj

/--
Interface-level characterization theorem:
slice connectivity from generators is equivalent to the geometric fixed-point condition.
-/
theorem MainSliceConnectivity_iff_GeometricFixedPoints
    (M : SliceCellModel G)
    (π : HomotopyGroupData G)
    (O : IncompleteTransferSystem G) (d : DimensionFunction G)
    (hClosure : MainFixedPointClosureAxioms (G := G) M π O d)
    (hReconstruction : MainReconstructionAxiom (G := G) M π O d)
    (n : ℤ) (X : OrthogonalSpectrum G) :
    IsSliceConnected (G := G) M O d n X ↔ MainGeometricFixedPointCondition (G := G) π O d n X := by
  constructor
  · intro hSlice
    exact mainSliceConnectivity_implies_geometricFixedPoints (G := G) M π O d hClosure hSlice
  · intro hGeo
    exact hReconstruction.of_fixedPoints hGeo

/-- Unified witness package for the main characterization theorem. -/
structure MainResultWitness (M : SliceCellModel G) (π : HomotopyGroupData G)
    (O : IncompleteTransferSystem G) (d : DimensionFunction G) : Prop where
  closure : MainFixedPointClosureAxioms (G := G) M π O d
  reconstruction : MainReconstructionAxiom (G := G) M π O d

/--
Recommended theorem inputs for the base characterization:
use a unified forward path and a conditional-surjectivity reverse path.
-/
structure MainRecommendedInput (M : SliceCellModel G) (π : HomotopyGroupData G)
    (O : IncompleteTransferSystem G) (d : DimensionFunction G) where
  forward : MainForwardClosurePath M π O d
  reverse : MainConditionalCellSurjective (G := G) M π O d

/--
Recommended theorem inputs with isotropy-orthogonal bridge data.
This is the preferred reverse-path entry when bridge data is available.
-/
structure MainRecommendedInputWithBridge (M : SliceCellModel G) (π : HomotopyGroupData G)
    (O : IncompleteTransferSystem G) (d : DimensionFunction G) where
  forward : MainForwardClosurePath M π O d
  bridge : MainIsotropyOrthogonalBridge (G := G) M π O d
  reverse : MainConditionalCellSurjective (G := G) M π O d

def mainRecommendedInput_of_global_and_conditionalCellSurjective
    (M : SliceCellModel G)
    (π : HomotopyGroupData G)
    (O : IncompleteTransferSystem G) (d : DimensionFunction G)
    (hGlobal : MainGlobalGeometricFixedPointCondition (G := G) π O d)
    (hCondSurj : MainConditionalCellSurjective (G := G) M π O d) :
    MainRecommendedInput (G := G) M π O d where
  forward := .global hGlobal
  reverse := hCondSurj

def mainRecommendedInput_of_generator_and_conditionalCellSurjective
    (M : SliceCellModel G)
    (π : HomotopyGroupData G)
    (O : IncompleteTransferSystem G) (d : DimensionFunction G)
    (hGen : MainGeneratorGeometricCondition (G := G) M π O d)
    (hConn : MainConnectednessAxiomsWithZero (G := G) π)
    (hCondSurj : MainConditionalCellSurjective (G := G) M π O d) :
    MainRecommendedInput (G := G) M π O d where
  forward := .generator hGen hConn
  reverse := hCondSurj

def mainRecommendedInputWithBridge_of_global_and_conditionalCellSurjective
    (M : SliceCellModel G)
    (π : HomotopyGroupData G)
    (O : IncompleteTransferSystem G) (d : DimensionFunction G)
    (hGlobal : MainGlobalGeometricFixedPointCondition (G := G) π O d)
    (B : MainIsotropyOrthogonalBridge (G := G) M π O d)
    (hCondSurj : MainConditionalCellSurjective (G := G) M π O d) :
    MainRecommendedInputWithBridge (G := G) M π O d where
  forward := .global hGlobal
  bridge := B
  reverse := hCondSurj

def mainRecommendedInputWithBridge_of_generator_and_conditionalCellSurjective
    (M : SliceCellModel G)
    (π : HomotopyGroupData G)
    (O : IncompleteTransferSystem G) (d : DimensionFunction G)
    (hGen : MainGeneratorGeometricCondition (G := G) M π O d)
    (hConn : MainConnectednessAxiomsWithZero (G := G) π)
    (B : MainIsotropyOrthogonalBridge (G := G) M π O d)
    (hCondSurj : MainConditionalCellSurjective (G := G) M π O d) :
    MainRecommendedInputWithBridge (G := G) M π O d where
  forward := .generator hGen hConn
  bridge := B
  reverse := hCondSurj

def mainResultWitness_of_recommendedInput
    (M : SliceCellModel G)
    (π : HomotopyGroupData G)
    (O : IncompleteTransferSystem G) (d : DimensionFunction G)
    (I : MainRecommendedInput (G := G) M π O d) :
    MainResultWitness (G := G) M π O d where
  closure := mainFixedPointClosureAxioms_of_forwardPath (G := G) M π O d I.forward
  reconstruction := mainReconstructionAxiom_of_conditionalCellSurjective (G := G) M π O d I.reverse

def mainResultWitness_of_recommendedInputWithBridge
    (M : SliceCellModel G)
    (π : HomotopyGroupData G)
    (O : IncompleteTransferSystem G) (d : DimensionFunction G)
    (I : MainRecommendedInputWithBridge (G := G) M π O d) :
    MainResultWitness (G := G) M π O d where
  closure := mainFixedPointClosureAxioms_of_forwardPath (G := G) M π O d I.forward
  reconstruction := mainReconstructionAxiom_of_conditionalCellSurjective_and_bridge
    (G := G) M π O d I.bridge I.reverse

theorem MainSliceConnectivity_iff_GeometricFixedPoints_recommended
    (M : SliceCellModel G)
    (π : HomotopyGroupData G)
    (O : IncompleteTransferSystem G) (d : DimensionFunction G)
    (I : MainRecommendedInput (G := G) M π O d)
    (n : ℤ) (X : OrthogonalSpectrum G) :
    IsSliceConnected (G := G) M O d n X ↔ MainGeometricFixedPointCondition (G := G) π O d n X := by
  exact MainSliceConnectivity_iff_GeometricFixedPoints
    (G := G) M π O d
    (mainFixedPointClosureAxioms_of_forwardPath (G := G) M π O d I.forward)
    (mainReconstructionAxiom_of_conditionalCellSurjective (G := G) M π O d I.reverse)
    n
    X

theorem MainSliceConnectivity_iff_GeometricFixedPoints_recommendedWithBridge
    (M : SliceCellModel G)
    (π : HomotopyGroupData G)
    (O : IncompleteTransferSystem G) (d : DimensionFunction G)
    (I : MainRecommendedInputWithBridge (G := G) M π O d)
    (n : ℤ) (X : OrthogonalSpectrum G) :
    IsSliceConnected (G := G) M O d n X ↔ MainGeometricFixedPointCondition (G := G) π O d n X := by
  exact MainSliceConnectivity_iff_GeometricFixedPoints
    (G := G) M π O d
    (mainFixedPointClosureAxioms_of_forwardPath (G := G) M π O d I.forward)
    (mainReconstructionAxiom_of_conditionalCellSurjective_and_bridge
      (G := G) M π O d I.bridge I.reverse)
    n
    X

/-!
### Legacy API (compatibility)

For new code, prefer the stable recommended entry points:
- `Main*RecommendedInput*`
- `Main*SliceConnectivity_iff_*_recommended*`

The declarations below are kept for backward compatibility and may be
consolidated in future cleanup passes.
-/

/-
#### Legacy witness constructors

Migration target:
- `mainResultWitness_of_recommendedInput`
- `mainResultWitness_of_recommendedInputWithBridge`
-/
def mainResultWitness_of_forwardPath_and_conditionalCellSurjective
    (M : SliceCellModel G)
    (π : HomotopyGroupData G)
    (O : IncompleteTransferSystem G) (d : DimensionFunction G)
    (hForward : MainForwardClosurePath M π O d)
    (hCondSurj : MainConditionalCellSurjective (G := G) M π O d) :
    MainResultWitness (G := G) M π O d where
  closure := mainFixedPointClosureAxioms_of_forwardPath (G := G) M π O d hForward
  reconstruction := mainReconstructionAxiom_of_conditionalCellSurjective (G := G) M π O d hCondSurj

def mainResultWitness_of_forwardPath_and_conditionalCellSurjective_and_bridge
    (M : SliceCellModel G)
    (π : HomotopyGroupData G)
    (O : IncompleteTransferSystem G) (d : DimensionFunction G)
    (hForward : MainForwardClosurePath M π O d)
    (B : MainIsotropyOrthogonalBridge (G := G) M π O d)
    (hCondSurj : MainConditionalCellSurjective (G := G) M π O d) :
    MainResultWitness (G := G) M π O d where
  closure := mainFixedPointClosureAxioms_of_forwardPath (G := G) M π O d hForward
  reconstruction :=
    mainReconstructionAxiom_of_conditionalCellSurjective_and_bridge
      (G := G) M π O d B hCondSurj

/-
Legacy global wrappers through `MainConditionalCellRealization`.
Migration target:
- `mainRecommendedInput_of_global_and_conditionalCellSurjective`
- `mainRecommendedInputWithBridge_of_global_and_conditionalCellSurjective`
-/
def mainResultWitness_of_global_and_conditionalCellRealization
    (M : SliceCellModel G)
    (π : HomotopyGroupData G)
    (O : IncompleteTransferSystem G) (d : DimensionFunction G)
    (hGlobal : MainGlobalGeometricFixedPointCondition (G := G) π O d)
    (R : MainConditionalCellRealization (G := G) M π O d) :
    MainResultWitness (G := G) M π O d where
  closure := mainFixedPointClosureAxioms_of_global (G := G) M π O d hGlobal
  reconstruction := mainReconstructionAxiom_of_conditionalCellRealization (G := G) M π O d R

def mainResultWitness_of_global_and_conditionalCellRealization_and_isotropyOrthogonal
    (M : SliceCellModel G)
    (π : HomotopyGroupData G)
    (O : IncompleteTransferSystem G) (d : DimensionFunction G)
    (hGlobal : MainGlobalGeometricFixedPointCondition (G := G) π O d)
    (D : IsotropySeparationData G)
    (lift : OrthogonalSpectrum G → D.spectrum)
    (family : ℤ → OrthogonalSpectrum G → SubgroupFamily G)
    (hOrth :
      ∀ {n : ℤ} {X : OrthogonalSpectrum G},
        MainGeometricFixedPointCondition (G := G) π O d n X →
          ∀ H : Subgroup G, IsPhiFamilyOrthogonal D H (family n X) (lift X))
    (R : MainConditionalCellRealization (G := G) M π O d) :
    MainResultWitness (G := G) M π O d where
  closure := mainFixedPointClosureAxioms_of_global (G := G) M π O d hGlobal
  reconstruction := mainReconstructionAxiom_of_conditionalCellRealization_and_isotropyOrthogonal
    (G := G) M π O d D lift family hOrth R

def mainResultWitness_of_global_and_conditionalCellRealization_and_bridge
    (M : SliceCellModel G)
    (π : HomotopyGroupData G)
    (O : IncompleteTransferSystem G) (d : DimensionFunction G)
    (hGlobal : MainGlobalGeometricFixedPointCondition (G := G) π O d)
    (B : MainIsotropyOrthogonalBridge (G := G) M π O d)
    (R : MainConditionalCellRealization (G := G) M π O d) :
    MainResultWitness (G := G) M π O d :=
  mainResultWitness_of_global_and_conditionalCellRealization_and_isotropyOrthogonal
    (G := G) M π O d hGlobal B.D B.lift B.family B.orthogonal_of_fixedPoints R

/-
Legacy connectedness wrappers through explicit cell-level assumptions.
Migration target:
- `mainRecommendedInput_of_generator_and_conditionalCellSurjective`
- `mainRecommendedInputWithBridge_of_generator_and_conditionalCellSurjective`
-/
def mainResultWitness_of_connectedness_and_conditionalCellRealization
    (M : SliceCellModel G)
    (π : HomotopyGroupData G)
    (O : IncompleteTransferSystem G) (d : DimensionFunction G)
    (hGenerators :
      ∀ {n : ℤ} {c : MainSliceCellData G},
        c ∈ MainSliceCells (G := G) O d n →
          MainGeometricFixedPointCondition (G := G) π O d n (M.cellObj c))
    (hZero :
      ∀ n : ℤ,
        MainGeometricFixedPointCondition (G := G) π O d n (ZeroSpectrum G))
    (hConn : MainConnectednessAxioms (G := G) π)
    (R : MainConditionalCellRealization (G := G) M π O d) :
    MainResultWitness (G := G) M π O d where
  closure :=
    mainFixedPointClosureAxioms_of_connectedness (G := G) M π O d hGenerators hZero hConn
  reconstruction := mainReconstructionAxiom_of_conditionalCellRealization (G := G) M π O d R

def mainResultWitness_of_connectednessWithZero_and_conditionalCellRealization
    (M : SliceCellModel G)
    (π : HomotopyGroupData G)
    (O : IncompleteTransferSystem G) (d : DimensionFunction G)
    (hGenerators :
      ∀ {n : ℤ} {c : MainSliceCellData G},
        c ∈ MainSliceCells (G := G) O d n →
          MainGeometricFixedPointCondition (G := G) π O d n (M.cellObj c))
    (hConn : MainConnectednessAxiomsWithZero (G := G) π)
    (R : MainConditionalCellRealization (G := G) M π O d) :
    MainResultWitness (G := G) M π O d where
  closure :=
    mainFixedPointClosureAxioms_of_connectednessWithZero (G := G) M π O d hGenerators hConn
  reconstruction := mainReconstructionAxiom_of_conditionalCellRealization (G := G) M π O d R

def mainResultWitness_of_connectednessWithZero_and_conditionalCellRealization_and_isotropyOrthogonal
    (M : SliceCellModel G)
    (π : HomotopyGroupData G)
    (O : IncompleteTransferSystem G) (d : DimensionFunction G)
    (hGenerators :
      ∀ {n : ℤ} {c : MainSliceCellData G},
        c ∈ MainSliceCells (G := G) O d n →
          MainGeometricFixedPointCondition (G := G) π O d n (M.cellObj c))
    (hConn : MainConnectednessAxiomsWithZero (G := G) π)
    (D : IsotropySeparationData G)
    (lift : OrthogonalSpectrum G → D.spectrum)
    (family : ℤ → OrthogonalSpectrum G → SubgroupFamily G)
    (hOrth :
      ∀ {n : ℤ} {X : OrthogonalSpectrum G},
        MainGeometricFixedPointCondition (G := G) π O d n X →
          ∀ H : Subgroup G, IsPhiFamilyOrthogonal D H (family n X) (lift X))
    (R : MainConditionalCellRealization (G := G) M π O d) :
    MainResultWitness (G := G) M π O d where
  closure :=
    mainFixedPointClosureAxioms_of_connectednessWithZero (G := G) M π O d hGenerators hConn
  reconstruction := mainReconstructionAxiom_of_conditionalCellRealization_and_isotropyOrthogonal
    (G := G) M π O d D lift family hOrth R

def mainResultWitness_of_connectednessWithZero_and_conditionalCellRealization_and_bridge
    (M : SliceCellModel G)
    (π : HomotopyGroupData G)
    (O : IncompleteTransferSystem G) (d : DimensionFunction G)
    (hGenerators :
      ∀ {n : ℤ} {c : MainSliceCellData G},
        c ∈ MainSliceCells (G := G) O d n →
          MainGeometricFixedPointCondition (G := G) π O d n (M.cellObj c))
    (hConn : MainConnectednessAxiomsWithZero (G := G) π)
    (B : MainIsotropyOrthogonalBridge (G := G) M π O d)
    (R : MainConditionalCellRealization (G := G) M π O d) :
    MainResultWitness (G := G) M π O d :=
  mainResultWitness_of_connectednessWithZero_and_conditionalCellRealization_and_isotropyOrthogonal
    (G := G) M π O d hGenerators hConn B.D B.lift B.family B.orthogonal_of_fixedPoints R

/-
Legacy global/connectedness wrappers through conditional-surjectivity forms.
Migration target: prefer `MainRecommendedInput*` constructors + recommended theorems.
-/
def mainResultWitness_of_global_and_conditionalCellSurjective
    (M : SliceCellModel G)
    (π : HomotopyGroupData G)
    (O : IncompleteTransferSystem G) (d : DimensionFunction G)
    (hGlobal : MainGlobalGeometricFixedPointCondition (G := G) π O d)
    (hCondSurj : MainConditionalCellSurjective (G := G) M π O d) :
    MainResultWitness (G := G) M π O d :=
  mainResultWitness_of_forwardPath_and_conditionalCellSurjective
    (G := G) M π O d (.global hGlobal) hCondSurj

def mainResultWitness_of_global_and_conditionalCellSurjective_and_bridge
    (M : SliceCellModel G)
    (π : HomotopyGroupData G)
    (O : IncompleteTransferSystem G) (d : DimensionFunction G)
    (hGlobal : MainGlobalGeometricFixedPointCondition (G := G) π O d)
    (B : MainIsotropyOrthogonalBridge (G := G) M π O d)
    (hCondSurj : MainConditionalCellSurjective (G := G) M π O d) :
    MainResultWitness (G := G) M π O d :=
  mainResultWitness_of_forwardPath_and_conditionalCellSurjective_and_bridge
    (G := G) M π O d (.global hGlobal) B hCondSurj

def mainResultWitness_of_connectednessWithZero_and_conditionalCellSurjective
    (M : SliceCellModel G)
    (π : HomotopyGroupData G)
    (O : IncompleteTransferSystem G) (d : DimensionFunction G)
    (hGenerators :
      ∀ {n : ℤ} {c : MainSliceCellData G},
        c ∈ MainSliceCells (G := G) O d n →
          MainGeometricFixedPointCondition (G := G) π O d n (M.cellObj c))
    (hConn : MainConnectednessAxiomsWithZero (G := G) π)
    (hCondSurj : MainConditionalCellSurjective (G := G) M π O d) :
    MainResultWitness (G := G) M π O d :=
  mainResultWitness_of_forwardPath_and_conditionalCellSurjective
    (G := G) M π O d
    (.generator
      (mainGeneratorGeometricCondition_of_cells (G := G) M π O d hGenerators)
      hConn)
    hCondSurj

def mainResultWitness_of_connectednessWithZero_and_conditionalCellSurjective_and_bridge
    (M : SliceCellModel G)
    (π : HomotopyGroupData G)
    (O : IncompleteTransferSystem G) (d : DimensionFunction G)
    (hGenerators :
      ∀ {n : ℤ} {c : MainSliceCellData G},
        c ∈ MainSliceCells (G := G) O d n →
          MainGeometricFixedPointCondition (G := G) π O d n (M.cellObj c))
    (hConn : MainConnectednessAxiomsWithZero (G := G) π)
    (B : MainIsotropyOrthogonalBridge (G := G) M π O d)
    (hCondSurj : MainConditionalCellSurjective (G := G) M π O d) :
    MainResultWitness (G := G) M π O d :=
  mainResultWitness_of_forwardPath_and_conditionalCellSurjective_and_bridge
    (G := G) M π O d
    (.generator
      (mainGeneratorGeometricCondition_of_cells (G := G) M π O d hGenerators)
      hConn)
    B
    hCondSurj

def mainResultWitness_of_generatorCondition_and_conditionalCellSurjective
    (M : SliceCellModel G)
    (π : HomotopyGroupData G)
    (O : IncompleteTransferSystem G) (d : DimensionFunction G)
    (hGen : MainGeneratorGeometricCondition (G := G) M π O d)
    (hConn : MainConnectednessAxiomsWithZero (G := G) π)
    (hCondSurj : MainConditionalCellSurjective (G := G) M π O d) :
    MainResultWitness (G := G) M π O d :=
  mainResultWitness_of_forwardPath_and_conditionalCellSurjective
    (G := G) M π O d (.generator hGen hConn) hCondSurj

def mainResultWitness_of_generatorCondition_and_conditionalCellSurjective_and_bridge
    (M : SliceCellModel G)
    (π : HomotopyGroupData G)
    (O : IncompleteTransferSystem G) (d : DimensionFunction G)
    (hGen : MainGeneratorGeometricCondition (G := G) M π O d)
    (hConn : MainConnectednessAxiomsWithZero (G := G) π)
    (B : MainIsotropyOrthogonalBridge (G := G) M π O d)
    (hCondSurj : MainConditionalCellSurjective (G := G) M π O d) :
    MainResultWitness (G := G) M π O d :=
  mainResultWitness_of_forwardPath_and_conditionalCellSurjective_and_bridge
    (G := G) M π O d (.generator hGen hConn) B hCondSurj

/-
Legacy wrappers ending in `realization` / `cellSurjective`.
Migration target: convert once via `mainConditionalCellSurjective_of_realization`
or `mainConditionalCellSurjective_of_cellSurjectiveAtLevel`, then use recommended APIs.
-/
def mainResultWitness_of_global_and_realization
    (M : SliceCellModel G)
    (π : HomotopyGroupData G)
    (O : IncompleteTransferSystem G) (d : DimensionFunction G)
    (hGlobal : MainGlobalGeometricFixedPointCondition (G := G) π O d)
    (R : MainCellRealization (G := G) M O d) :
    MainResultWitness (G := G) M π O d :=
  mainResultWitness_of_global_and_conditionalCellSurjective (G := G) M π O d hGlobal
    (mainConditionalCellSurjective_of_realization (G := G) M π O d R)

def mainResultWitness_of_connectednessWithZero_and_cellSurjective
    (M : SliceCellModel G)
    (π : HomotopyGroupData G)
    (O : IncompleteTransferSystem G) (d : DimensionFunction G)
    (hGenerators :
      ∀ {n : ℤ} {c : MainSliceCellData G},
        c ∈ MainSliceCells (G := G) O d n →
          MainGeometricFixedPointCondition (G := G) π O d n (M.cellObj c))
    (hConn : MainConnectednessAxiomsWithZero (G := G) π)
    (hCellSurj : MainCellSurjectiveAtLevel (G := G) M O d) :
    MainResultWitness (G := G) M π O d :=
  mainResultWitness_of_connectednessWithZero_and_conditionalCellSurjective
    (G := G) M π O d hGenerators hConn
    (mainConditionalCellSurjective_of_cellSurjectiveAtLevel
      (G := G) M π O d hCellSurj)

def mainResultWitness_of_connectednessWithZero_and_realization
    (M : SliceCellModel G)
    (π : HomotopyGroupData G)
    (O : IncompleteTransferSystem G) (d : DimensionFunction G)
    (hGenerators :
      ∀ {n : ℤ} {c : MainSliceCellData G},
        c ∈ MainSliceCells (G := G) O d n →
          MainGeometricFixedPointCondition (G := G) π O d n (M.cellObj c))
    (hConn : MainConnectednessAxiomsWithZero (G := G) π)
    (R : MainCellRealization (G := G) M O d) :
    MainResultWitness (G := G) M π O d :=
  mainResultWitness_of_connectednessWithZero_and_conditionalCellSurjective
    (G := G) M π O d hGenerators hConn
    (mainConditionalCellSurjective_of_realization (G := G) M π O d R)

/-
#### Legacy theorem wrappers

Migration target:
- `MainSliceConnectivity_iff_GeometricFixedPoints_recommended`
- `MainSliceConnectivity_iff_GeometricFixedPoints_recommendedWithBridge`
-/
theorem MainSliceConnectivity_iff_GeometricFixedPoints_of_witness
    (M : SliceCellModel G)
    (π : HomotopyGroupData G)
    (O : IncompleteTransferSystem G) (d : DimensionFunction G)
    (W : MainResultWitness (G := G) M π O d)
    (n : ℤ) (X : OrthogonalSpectrum G) :
    IsSliceConnected (G := G) M O d n X ↔ MainGeometricFixedPointCondition (G := G) π O d n X := by
  exact MainSliceConnectivity_iff_GeometricFixedPoints
    (G := G) M π O d W.closure W.reconstruction n X

theorem MainSliceConnectivity_iff_GeometricFixedPoints_of_global_and_conditionalCellRealization
    (M : SliceCellModel G)
    (π : HomotopyGroupData G)
    (O : IncompleteTransferSystem G) (d : DimensionFunction G)
    (hGlobal : MainGlobalGeometricFixedPointCondition (G := G) π O d)
    (R : MainConditionalCellRealization (G := G) M π O d)
    (n : ℤ) (X : OrthogonalSpectrum G) :
    IsSliceConnected (G := G) M O d n X ↔ MainGeometricFixedPointCondition (G := G) π O d n X := by
  exact MainSliceConnectivity_iff_GeometricFixedPoints_of_witness
    (G := G) M π O d
    (mainResultWitness_of_global_and_conditionalCellRealization (G := G) M π O d hGlobal R)
    n
    X

theorem MainSliceConnectivity_iff_GeometricFixedPoints_of_global_and_conditionalCellRealization_and_isotropyOrthogonal
    (M : SliceCellModel G)
    (π : HomotopyGroupData G)
    (O : IncompleteTransferSystem G) (d : DimensionFunction G)
    (hGlobal : MainGlobalGeometricFixedPointCondition (G := G) π O d)
    (D : IsotropySeparationData G)
    (lift : OrthogonalSpectrum G → D.spectrum)
    (family : ℤ → OrthogonalSpectrum G → SubgroupFamily G)
    (hOrth :
      ∀ {n : ℤ} {X : OrthogonalSpectrum G},
        MainGeometricFixedPointCondition (G := G) π O d n X →
          ∀ H : Subgroup G, IsPhiFamilyOrthogonal D H (family n X) (lift X))
    (R : MainConditionalCellRealization (G := G) M π O d)
    (n : ℤ) (X : OrthogonalSpectrum G) :
    IsSliceConnected (G := G) M O d n X ↔ MainGeometricFixedPointCondition (G := G) π O d n X := by
  exact MainSliceConnectivity_iff_GeometricFixedPoints_of_witness
    (G := G) M π O d
    (mainResultWitness_of_global_and_conditionalCellRealization_and_isotropyOrthogonal
      (G := G) M π O d hGlobal D lift family hOrth R)
    n
    X

theorem MainSliceConnectivity_iff_GeometricFixedPoints_of_global_and_conditionalCellRealization_and_bridge
    (M : SliceCellModel G)
    (π : HomotopyGroupData G)
    (O : IncompleteTransferSystem G) (d : DimensionFunction G)
    (hGlobal : MainGlobalGeometricFixedPointCondition (G := G) π O d)
    (B : MainIsotropyOrthogonalBridge (G := G) M π O d)
    (R : MainConditionalCellRealization (G := G) M π O d)
    (n : ℤ) (X : OrthogonalSpectrum G) :
    IsSliceConnected (G := G) M O d n X ↔ MainGeometricFixedPointCondition (G := G) π O d n X := by
  exact MainSliceConnectivity_iff_GeometricFixedPoints_of_witness
    (G := G) M π O d
    (mainResultWitness_of_global_and_conditionalCellRealization_and_bridge
      (G := G) M π O d hGlobal B R)
    n
    X

theorem MainSliceConnectivity_iff_GeometricFixedPoints_of_forwardPath_and_conditionalCellSurjective
    (M : SliceCellModel G)
    (π : HomotopyGroupData G)
    (O : IncompleteTransferSystem G) (d : DimensionFunction G)
    (hForward : MainForwardClosurePath M π O d)
    (hCondSurj : MainConditionalCellSurjective (G := G) M π O d)
    (n : ℤ) (X : OrthogonalSpectrum G) :
    IsSliceConnected (G := G) M O d n X ↔ MainGeometricFixedPointCondition (G := G) π O d n X := by
  exact MainSliceConnectivity_iff_GeometricFixedPoints_of_witness
    (G := G) M π O d
    (mainResultWitness_of_forwardPath_and_conditionalCellSurjective
      (G := G) M π O d hForward hCondSurj)
    n
    X

theorem MainSliceConnectivity_iff_GeometricFixedPoints_of_forwardPath_and_conditionalCellSurjective_and_bridge
    (M : SliceCellModel G)
    (π : HomotopyGroupData G)
    (O : IncompleteTransferSystem G) (d : DimensionFunction G)
    (hForward : MainForwardClosurePath M π O d)
    (B : MainIsotropyOrthogonalBridge (G := G) M π O d)
    (hCondSurj : MainConditionalCellSurjective (G := G) M π O d)
    (n : ℤ) (X : OrthogonalSpectrum G) :
    IsSliceConnected (G := G) M O d n X ↔ MainGeometricFixedPointCondition (G := G) π O d n X := by
  exact MainSliceConnectivity_iff_GeometricFixedPoints_of_witness
    (G := G) M π O d
    (mainResultWitness_of_forwardPath_and_conditionalCellSurjective_and_bridge
      (G := G) M π O d hForward B hCondSurj)
    n
    X

theorem MainSliceConnectivity_iff_GeometricFixedPoints_of_global_and_conditionalCellSurjective
    (M : SliceCellModel G)
    (π : HomotopyGroupData G)
    (O : IncompleteTransferSystem G) (d : DimensionFunction G)
    (hGlobal : MainGlobalGeometricFixedPointCondition (G := G) π O d)
    (hCondSurj : MainConditionalCellSurjective (G := G) M π O d)
    (n : ℤ) (X : OrthogonalSpectrum G) :
    IsSliceConnected (G := G) M O d n X ↔ MainGeometricFixedPointCondition (G := G) π O d n X := by
  exact MainSliceConnectivity_iff_GeometricFixedPoints_of_forwardPath_and_conditionalCellSurjective
    (G := G) M π O d (.global hGlobal) hCondSurj n X

theorem MainSliceConnectivity_iff_GeometricFixedPoints_of_global_and_conditionalCellSurjective_and_bridge
    (M : SliceCellModel G)
    (π : HomotopyGroupData G)
    (O : IncompleteTransferSystem G) (d : DimensionFunction G)
    (hGlobal : MainGlobalGeometricFixedPointCondition (G := G) π O d)
    (B : MainIsotropyOrthogonalBridge (G := G) M π O d)
    (hCondSurj : MainConditionalCellSurjective (G := G) M π O d)
    (n : ℤ) (X : OrthogonalSpectrum G) :
    IsSliceConnected (G := G) M O d n X ↔ MainGeometricFixedPointCondition (G := G) π O d n X := by
  exact MainSliceConnectivity_iff_GeometricFixedPoints_of_forwardPath_and_conditionalCellSurjective_and_bridge
    (G := G) M π O d (.global hGlobal) B hCondSurj n X

theorem MainSliceConnectivity_iff_GeometricFixedPoints_of_global_and_realization
    (M : SliceCellModel G)
    (π : HomotopyGroupData G)
    (O : IncompleteTransferSystem G) (d : DimensionFunction G)
    (hGlobal : MainGlobalGeometricFixedPointCondition (G := G) π O d)
    (R : MainCellRealization (G := G) M O d)
    (n : ℤ) (X : OrthogonalSpectrum G) :
    IsSliceConnected (G := G) M O d n X ↔ MainGeometricFixedPointCondition (G := G) π O d n X := by
  exact MainSliceConnectivity_iff_GeometricFixedPoints_of_global_and_conditionalCellSurjective
    (G := G) M π O d hGlobal
    (mainConditionalCellSurjective_of_realization (G := G) M π O d R)
    n
    X

theorem MainSliceConnectivity_iff_GeometricFixedPoints_of_syntaxReconstruction
    (M : SliceCellModel G)
    (π : HomotopyGroupData G)
    (O : IncompleteTransferSystem G) (d : DimensionFunction G)
    (hClosure : MainFixedPointClosureAxioms (G := G) M π O d)
    (hSyntax : MainSyntaxReconstructionAxiom (G := G) M π O d)
    (n : ℤ) (X : OrthogonalSpectrum G) :
    IsSliceConnected (G := G) M O d n X ↔ MainGeometricFixedPointCondition (G := G) π O d n X := by
  exact MainSliceConnectivity_iff_GeometricFixedPoints
    (G := G) M π O d hClosure
    (mainReconstructionAxiom_of_syntaxReconstruction (G := G) M π O d hSyntax) n X

theorem MainSliceConnectivity_iff_GeometricFixedPoints_of_global_and_syntaxReconstruction
    (M : SliceCellModel G)
    (π : HomotopyGroupData G)
    (O : IncompleteTransferSystem G) (d : DimensionFunction G)
    (hGlobal : MainGlobalGeometricFixedPointCondition (G := G) π O d)
    (hSyntax : MainSyntaxReconstructionAxiom (G := G) M π O d)
    (n : ℤ) (X : OrthogonalSpectrum G) :
    IsSliceConnected (G := G) M O d n X ↔ MainGeometricFixedPointCondition (G := G) π O d n X := by
  exact MainSliceConnectivity_iff_GeometricFixedPoints_of_syntaxReconstruction
    (G := G) M π O d
    (mainFixedPointClosureAxioms_of_global (G := G) M π O d hGlobal)
    hSyntax n X

/-
Legacy operad wrappers.
Migration target:
- `MainOperadSliceConnectivity_iff_GeometricFixedPoints_recommended`
- `MainOperadSliceConnectivity_iff_GeometricFixedPoints_recommendedWithBridge`
-/
theorem MainOperadSliceConnectivity_iff_GeometricFixedPoints
    (M : SliceCellModel G)
    (π : HomotopyGroupData G)
    (Oinf : NInfinityOperad G) (d : DimensionFunction G)
    (hClosure : MainFixedPointClosureAxioms (G := G) M π Oinf.transferSystem d)
    (hReconstruction : MainReconstructionAxiom (G := G) M π Oinf.transferSystem d)
    (n : ℤ) (X : OrthogonalSpectrum G) :
    IsSliceConnected (G := G) M Oinf.transferSystem d n X ↔
      MainGeometricFixedPointCondition (G := G) π Oinf.transferSystem d n X := by
  exact MainSliceConnectivity_iff_GeometricFixedPoints
    (G := G) M π Oinf.transferSystem d hClosure hReconstruction n X

theorem MainOperadSliceConnectivity_iff_GeometricFixedPoints_of_witness
    (M : SliceCellModel G)
    (π : HomotopyGroupData G)
    (Oinf : NInfinityOperad G) (d : DimensionFunction G)
    (W : MainResultWitness (G := G) M π Oinf.transferSystem d)
    (n : ℤ) (X : OrthogonalSpectrum G) :
    IsSliceConnected (G := G) M Oinf.transferSystem d n X ↔
      MainGeometricFixedPointCondition (G := G) π Oinf.transferSystem d n X := by
  exact MainSliceConnectivity_iff_GeometricFixedPoints_of_witness
    (G := G) M π Oinf.transferSystem d W n X

theorem MainOperadSliceConnectivity_iff_GeometricFixedPoints_of_forwardPath_and_conditionalCellSurjective
    (M : SliceCellModel G)
    (π : HomotopyGroupData G)
    (Oinf : NInfinityOperad G) (d : DimensionFunction G)
    (hForward : MainForwardClosurePath M π Oinf.transferSystem d)
    (hCondSurj : MainConditionalCellSurjective (G := G) M π Oinf.transferSystem d)
    (n : ℤ) (X : OrthogonalSpectrum G) :
    IsSliceConnected (G := G) M Oinf.transferSystem d n X ↔
      MainGeometricFixedPointCondition (G := G) π Oinf.transferSystem d n X := by
  exact MainSliceConnectivity_iff_GeometricFixedPoints_of_forwardPath_and_conditionalCellSurjective
    (G := G) M π Oinf.transferSystem d hForward hCondSurj n X

theorem MainOperadSliceConnectivity_iff_GeometricFixedPoints_of_forwardPath_and_conditionalCellSurjective_and_bridge
    (M : SliceCellModel G)
    (π : HomotopyGroupData G)
    (Oinf : NInfinityOperad G) (d : DimensionFunction G)
    (hForward : MainForwardClosurePath M π Oinf.transferSystem d)
    (B : MainIsotropyOrthogonalBridge (G := G) M π Oinf.transferSystem d)
    (hCondSurj : MainConditionalCellSurjective (G := G) M π Oinf.transferSystem d)
    (n : ℤ) (X : OrthogonalSpectrum G) :
    IsSliceConnected (G := G) M Oinf.transferSystem d n X ↔
      MainGeometricFixedPointCondition (G := G) π Oinf.transferSystem d n X := by
  exact MainSliceConnectivity_iff_GeometricFixedPoints_of_forwardPath_and_conditionalCellSurjective_and_bridge
    (G := G) M π Oinf.transferSystem d hForward B hCondSurj n X

theorem MainOperadSliceConnectivity_iff_GeometricFixedPoints_of_global_and_conditionalCellSurjective
    (M : SliceCellModel G)
    (π : HomotopyGroupData G)
    (Oinf : NInfinityOperad G) (d : DimensionFunction G)
    (hGlobal : MainGlobalGeometricFixedPointCondition (G := G) π Oinf.transferSystem d)
    (hCondSurj : MainConditionalCellSurjective (G := G) M π Oinf.transferSystem d)
    (n : ℤ) (X : OrthogonalSpectrum G) :
    IsSliceConnected (G := G) M Oinf.transferSystem d n X ↔
      MainGeometricFixedPointCondition (G := G) π Oinf.transferSystem d n X := by
  exact MainOperadSliceConnectivity_iff_GeometricFixedPoints_of_forwardPath_and_conditionalCellSurjective
    (G := G) M π Oinf d (.global hGlobal) hCondSurj n X

theorem MainOperadSliceConnectivity_iff_GeometricFixedPoints_of_global_and_conditionalCellSurjective_and_bridge
    (M : SliceCellModel G)
    (π : HomotopyGroupData G)
    (Oinf : NInfinityOperad G) (d : DimensionFunction G)
    (hGlobal : MainGlobalGeometricFixedPointCondition (G := G) π Oinf.transferSystem d)
    (B : MainIsotropyOrthogonalBridge (G := G) M π Oinf.transferSystem d)
    (hCondSurj : MainConditionalCellSurjective (G := G) M π Oinf.transferSystem d)
    (n : ℤ) (X : OrthogonalSpectrum G) :
    IsSliceConnected (G := G) M Oinf.transferSystem d n X ↔
      MainGeometricFixedPointCondition (G := G) π Oinf.transferSystem d n X := by
  exact MainOperadSliceConnectivity_iff_GeometricFixedPoints_of_forwardPath_and_conditionalCellSurjective_and_bridge
    (G := G) M π Oinf d (.global hGlobal) B hCondSurj n X

/--
Recommended inputs for operad-level characterization.
-/
structure MainOperadRecommendedInput (M : SliceCellModel G) (π : HomotopyGroupData G)
    (Oinf : NInfinityOperad G) (d : DimensionFunction G) where
  forward : MainForwardClosurePath M π Oinf.transferSystem d
  reverse : MainConditionalCellSurjective (G := G) M π Oinf.transferSystem d

/--
Recommended inputs for operad-level characterization with bridge data.
-/
structure MainOperadRecommendedInputWithBridge (M : SliceCellModel G) (π : HomotopyGroupData G)
    (Oinf : NInfinityOperad G) (d : DimensionFunction G) where
  forward : MainForwardClosurePath M π Oinf.transferSystem d
  bridge : MainIsotropyOrthogonalBridge (G := G) M π Oinf.transferSystem d
  reverse : MainConditionalCellSurjective (G := G) M π Oinf.transferSystem d

def mainOperadRecommendedInput_of_global_and_conditionalCellSurjective
    (M : SliceCellModel G)
    (π : HomotopyGroupData G)
    (Oinf : NInfinityOperad G) (d : DimensionFunction G)
    (hGlobal : MainGlobalGeometricFixedPointCondition (G := G) π Oinf.transferSystem d)
    (hCondSurj : MainConditionalCellSurjective (G := G) M π Oinf.transferSystem d) :
    MainOperadRecommendedInput (G := G) M π Oinf d where
  forward := .global hGlobal
  reverse := hCondSurj

def mainOperadRecommendedInputWithBridge_of_global_and_conditionalCellSurjective
    (M : SliceCellModel G)
    (π : HomotopyGroupData G)
    (Oinf : NInfinityOperad G) (d : DimensionFunction G)
    (hGlobal : MainGlobalGeometricFixedPointCondition (G := G) π Oinf.transferSystem d)
    (B : MainIsotropyOrthogonalBridge (G := G) M π Oinf.transferSystem d)
    (hCondSurj : MainConditionalCellSurjective (G := G) M π Oinf.transferSystem d) :
    MainOperadRecommendedInputWithBridge (G := G) M π Oinf d where
  forward := .global hGlobal
  bridge := B
  reverse := hCondSurj

theorem MainOperadSliceConnectivity_iff_GeometricFixedPoints_recommended
    (M : SliceCellModel G)
    (π : HomotopyGroupData G)
    (Oinf : NInfinityOperad G) (d : DimensionFunction G)
    (I : MainOperadRecommendedInput (G := G) M π Oinf d)
    (n : ℤ) (X : OrthogonalSpectrum G) :
    IsSliceConnected (G := G) M Oinf.transferSystem d n X ↔
      MainGeometricFixedPointCondition (G := G) π Oinf.transferSystem d n X := by
  exact MainOperadSliceConnectivity_iff_GeometricFixedPoints_of_forwardPath_and_conditionalCellSurjective
    (G := G) M π Oinf d I.forward I.reverse n X

theorem MainOperadSliceConnectivity_iff_GeometricFixedPoints_recommendedWithBridge
    (M : SliceCellModel G)
    (π : HomotopyGroupData G)
    (Oinf : NInfinityOperad G) (d : DimensionFunction G)
    (I : MainOperadRecommendedInputWithBridge (G := G) M π Oinf d)
    (n : ℤ) (X : OrthogonalSpectrum G) :
    IsSliceConnected (G := G) M Oinf.transferSystem d n X ↔
      MainGeometricFixedPointCondition (G := G) π Oinf.transferSystem d n X := by
  exact MainOperadSliceConnectivity_iff_GeometricFixedPoints_of_forwardPath_and_conditionalCellSurjective_and_bridge
    (G := G) M π Oinf d I.forward I.bridge I.reverse n X

theorem MainOperadSliceConnectivity_iff_GeometricFixedPoints_of_global_and_realization
    (M : SliceCellModel G)
    (π : HomotopyGroupData G)
    (Oinf : NInfinityOperad G) (d : DimensionFunction G)
    (hGlobal : MainGlobalGeometricFixedPointCondition (G := G) π Oinf.transferSystem d)
    (R : MainCellRealization (G := G) M Oinf.transferSystem d)
    (n : ℤ) (X : OrthogonalSpectrum G) :
    IsSliceConnected (G := G) M Oinf.transferSystem d n X ↔
      MainGeometricFixedPointCondition (G := G) π Oinf.transferSystem d n X := by
  exact MainOperadSliceConnectivity_iff_GeometricFixedPoints_of_global_and_conditionalCellSurjective
    (G := G) M π Oinf d hGlobal
    (mainConditionalCellSurjective_of_realization (G := G) M π Oinf.transferSystem d R)
    n
    X

/-
Legacy indexing-system wrappers.
Migration target:
- `MainIndexingSystemSliceConnectivity_iff_GeometricFixedPoints_recommended`
- `MainIndexingSystemSliceConnectivity_iff_GeometricFixedPoints_recommendedWithBridge`
-/
theorem MainIndexingSystemSliceConnectivity_iff_GeometricFixedPoints
    (M : SliceCellModel G)
    (π : HomotopyGroupData G)
    (I : IndexingSystem G) (d : DimensionFunction G)
    (hClosure : MainFixedPointClosureAxioms (G := G) M π I.toTransferSystem d)
    (hReconstruction : MainReconstructionAxiom (G := G) M π I.toTransferSystem d)
    (n : ℤ) (X : OrthogonalSpectrum G) :
    IsSliceConnected (G := G) M I.toTransferSystem d n X ↔
      MainGeometricFixedPointCondition (G := G) π I.toTransferSystem d n X := by
  exact MainSliceConnectivity_iff_GeometricFixedPoints
    (G := G) M π I.toTransferSystem d hClosure hReconstruction n X

theorem MainIndexingSystemSliceConnectivity_iff_GeometricFixedPoints_of_witness
    (M : SliceCellModel G)
    (π : HomotopyGroupData G)
    (I : IndexingSystem G) (d : DimensionFunction G)
    (W : MainResultWitness (G := G) M π I.toTransferSystem d)
    (n : ℤ) (X : OrthogonalSpectrum G) :
    IsSliceConnected (G := G) M I.toTransferSystem d n X ↔
      MainGeometricFixedPointCondition (G := G) π I.toTransferSystem d n X := by
  exact MainSliceConnectivity_iff_GeometricFixedPoints_of_witness
    (G := G) M π I.toTransferSystem d W n X

theorem MainIndexingSystemSliceConnectivity_iff_GeometricFixedPoints_of_forwardPath_and_conditionalCellSurjective
    (M : SliceCellModel G)
    (π : HomotopyGroupData G)
    (I : IndexingSystem G) (d : DimensionFunction G)
    (hForward : MainForwardClosurePath M π I.toTransferSystem d)
    (hCondSurj : MainConditionalCellSurjective (G := G) M π I.toTransferSystem d)
    (n : ℤ) (X : OrthogonalSpectrum G) :
    IsSliceConnected (G := G) M I.toTransferSystem d n X ↔
      MainGeometricFixedPointCondition (G := G) π I.toTransferSystem d n X := by
  exact MainSliceConnectivity_iff_GeometricFixedPoints_of_forwardPath_and_conditionalCellSurjective
    (G := G) M π I.toTransferSystem d hForward hCondSurj n X

theorem MainIndexingSystemSliceConnectivity_iff_GeometricFixedPoints_of_forwardPath_and_conditionalCellSurjective_and_bridge
    (M : SliceCellModel G)
    (π : HomotopyGroupData G)
    (I : IndexingSystem G) (d : DimensionFunction G)
    (hForward : MainForwardClosurePath M π I.toTransferSystem d)
    (B : MainIsotropyOrthogonalBridge (G := G) M π I.toTransferSystem d)
    (hCondSurj : MainConditionalCellSurjective (G := G) M π I.toTransferSystem d)
    (n : ℤ) (X : OrthogonalSpectrum G) :
    IsSliceConnected (G := G) M I.toTransferSystem d n X ↔
      MainGeometricFixedPointCondition (G := G) π I.toTransferSystem d n X := by
  exact MainSliceConnectivity_iff_GeometricFixedPoints_of_forwardPath_and_conditionalCellSurjective_and_bridge
    (G := G) M π I.toTransferSystem d hForward B hCondSurj n X

theorem MainIndexingSystemSliceConnectivity_iff_GeometricFixedPoints_of_global_and_conditionalCellSurjective
    (M : SliceCellModel G)
    (π : HomotopyGroupData G)
    (I : IndexingSystem G) (d : DimensionFunction G)
    (hGlobal : MainGlobalGeometricFixedPointCondition (G := G) π I.toTransferSystem d)
    (hCondSurj : MainConditionalCellSurjective (G := G) M π I.toTransferSystem d)
    (n : ℤ) (X : OrthogonalSpectrum G) :
    IsSliceConnected (G := G) M I.toTransferSystem d n X ↔
      MainGeometricFixedPointCondition (G := G) π I.toTransferSystem d n X := by
  exact MainIndexingSystemSliceConnectivity_iff_GeometricFixedPoints_of_forwardPath_and_conditionalCellSurjective
    (G := G) M π I d (.global hGlobal) hCondSurj n X

theorem MainIndexingSystemSliceConnectivity_iff_GeometricFixedPoints_of_global_and_conditionalCellSurjective_and_bridge
    (M : SliceCellModel G)
    (π : HomotopyGroupData G)
    (I : IndexingSystem G) (d : DimensionFunction G)
    (hGlobal : MainGlobalGeometricFixedPointCondition (G := G) π I.toTransferSystem d)
    (B : MainIsotropyOrthogonalBridge (G := G) M π I.toTransferSystem d)
    (hCondSurj : MainConditionalCellSurjective (G := G) M π I.toTransferSystem d)
    (n : ℤ) (X : OrthogonalSpectrum G) :
    IsSliceConnected (G := G) M I.toTransferSystem d n X ↔
      MainGeometricFixedPointCondition (G := G) π I.toTransferSystem d n X := by
  exact MainIndexingSystemSliceConnectivity_iff_GeometricFixedPoints_of_forwardPath_and_conditionalCellSurjective_and_bridge
    (G := G) M π I d (.global hGlobal) B hCondSurj n X

/--
Recommended inputs for indexing-system-level characterization.
-/
structure MainIndexingSystemRecommendedInput (M : SliceCellModel G) (π : HomotopyGroupData G)
    (I : IndexingSystem G) (d : DimensionFunction G) where
  forward : MainForwardClosurePath M π I.toTransferSystem d
  reverse : MainConditionalCellSurjective (G := G) M π I.toTransferSystem d

/--
Recommended inputs for indexing-system-level characterization with bridge data.
-/
structure MainIndexingSystemRecommendedInputWithBridge (M : SliceCellModel G)
    (π : HomotopyGroupData G) (I : IndexingSystem G) (d : DimensionFunction G) where
  forward : MainForwardClosurePath M π I.toTransferSystem d
  bridge : MainIsotropyOrthogonalBridge (G := G) M π I.toTransferSystem d
  reverse : MainConditionalCellSurjective (G := G) M π I.toTransferSystem d

def mainIndexingSystemRecommendedInput_of_global_and_conditionalCellSurjective
    (M : SliceCellModel G)
    (π : HomotopyGroupData G)
    (I : IndexingSystem G) (d : DimensionFunction G)
    (hGlobal : MainGlobalGeometricFixedPointCondition (G := G) π I.toTransferSystem d)
    (hCondSurj : MainConditionalCellSurjective (G := G) M π I.toTransferSystem d) :
    MainIndexingSystemRecommendedInput (G := G) M π I d where
  forward := .global hGlobal
  reverse := hCondSurj

def mainIndexingSystemRecommendedInputWithBridge_of_global_and_conditionalCellSurjective
    (M : SliceCellModel G)
    (π : HomotopyGroupData G)
    (I : IndexingSystem G) (d : DimensionFunction G)
    (hGlobal : MainGlobalGeometricFixedPointCondition (G := G) π I.toTransferSystem d)
    (B : MainIsotropyOrthogonalBridge (G := G) M π I.toTransferSystem d)
    (hCondSurj : MainConditionalCellSurjective (G := G) M π I.toTransferSystem d) :
    MainIndexingSystemRecommendedInputWithBridge (G := G) M π I d where
  forward := .global hGlobal
  bridge := B
  reverse := hCondSurj

theorem MainIndexingSystemSliceConnectivity_iff_GeometricFixedPoints_recommended
    (M : SliceCellModel G)
    (π : HomotopyGroupData G)
    (I : IndexingSystem G) (d : DimensionFunction G)
    (R : MainIndexingSystemRecommendedInput (G := G) M π I d)
    (n : ℤ) (X : OrthogonalSpectrum G) :
    IsSliceConnected (G := G) M I.toTransferSystem d n X ↔
      MainGeometricFixedPointCondition (G := G) π I.toTransferSystem d n X := by
  exact MainIndexingSystemSliceConnectivity_iff_GeometricFixedPoints_of_forwardPath_and_conditionalCellSurjective
    (G := G) M π I d R.forward R.reverse n X

theorem MainIndexingSystemSliceConnectivity_iff_GeometricFixedPoints_recommendedWithBridge
    (M : SliceCellModel G)
    (π : HomotopyGroupData G)
    (I : IndexingSystem G) (d : DimensionFunction G)
    (R : MainIndexingSystemRecommendedInputWithBridge (G := G) M π I d)
    (n : ℤ) (X : OrthogonalSpectrum G) :
    IsSliceConnected (G := G) M I.toTransferSystem d n X ↔
      MainGeometricFixedPointCondition (G := G) π I.toTransferSystem d n X := by
  exact MainIndexingSystemSliceConnectivity_iff_GeometricFixedPoints_of_forwardPath_and_conditionalCellSurjective_and_bridge
    (G := G) M π I d R.forward R.bridge R.reverse n X

theorem MainIndexingSystemSliceConnectivity_iff_GeometricFixedPoints_of_global_and_realization
    (M : SliceCellModel G)
    (π : HomotopyGroupData G)
    (I : IndexingSystem G) (d : DimensionFunction G)
    (hGlobal : MainGlobalGeometricFixedPointCondition (G := G) π I.toTransferSystem d)
    (R : MainCellRealization (G := G) M I.toTransferSystem d)
    (n : ℤ) (X : OrthogonalSpectrum G) :
    IsSliceConnected (G := G) M I.toTransferSystem d n X ↔
      MainGeometricFixedPointCondition (G := G) π I.toTransferSystem d n X := by
  exact MainIndexingSystemSliceConnectivity_iff_GeometricFixedPoints_of_global_and_conditionalCellSurjective
    (G := G) M π I d hGlobal
    (mainConditionalCellSurjective_of_realization (G := G) M π I.toTransferSystem d R)
    n
    X

/-- Trivial homotopy-group data (`π = ∅`) used as a consistency sanity check. -/
def EmptyHomotopyGroupData (K : Type u) [Group K] : HomotopyGroupData K :=
  fun _ _ _ => PEmpty

theorem mainIsConnected_empty {K : Type u} [Group K]
    (t : ℤ) (X : OrthogonalSpectrum K) :
    MainIsConnected (EmptyHomotopyGroupData K) t X := by
  intro H k hk
  exact (inferInstance : IsEmpty PEmpty)

theorem mainConnectednessAxioms_empty :
    MainConnectednessAxioms (G := G) (EmptyHomotopyGroupData G) where
  of_levelwiseEquiv := by
    intro t X Y hXY hConn
    let _ := hXY
    exact mainIsConnected_empty (K := G) t Y
  susp := by
    intro t X hConn
    exact mainIsConnected_empty (K := G) t (SuspSpectrum X)
  cofiber := by
    intro t X Y hX hY
    exact mainIsConnected_empty (K := G) t (CofiberSpectrum X Y)
  colim := by
    intro t ι F hF
    exact mainIsConnected_empty (K := G) t (ColimSpectrum F)

theorem mainConnectednessAxiomsWithZero_empty :
    MainConnectednessAxiomsWithZero (G := G) (EmptyHomotopyGroupData G) where
  toMainConnectednessAxioms := mainConnectednessAxioms_empty (G := G)
  zero := by
    intro t
    exact mainIsConnected_empty (K := G) t (ZeroSpectrum G)

theorem mainGeometricFixedPointCondition_empty
    (O : IncompleteTransferSystem G) (d : DimensionFunction G)
    (n : ℤ) (X : OrthogonalSpectrum G) :
    MainGeometricFixedPointCondition (G := G) (EmptyHomotopyGroupData G) O d n X := by
  intro H
  exact mainIsConnected_empty (K := G) (d O H n) (GeometricFixedPoints (G := G) H X)

theorem mainGlobalGeometricFixedPointCondition_empty
    (O : IncompleteTransferSystem G) (d : DimensionFunction G) :
    MainGlobalGeometricFixedPointCondition (G := G) (EmptyHomotopyGroupData G) O d := by
  intro n X
  exact mainGeometricFixedPointCondition_empty (G := G) O d n X

theorem mainFixedPointClosureAxioms_empty
    (M : SliceCellModel G) (O : IncompleteTransferSystem G) (d : DimensionFunction G) :
    MainFixedPointClosureAxioms (G := G) M (EmptyHomotopyGroupData G) O d := by
  refine mainFixedPointClosureAxioms_of_connectednessWithZero
    (G := G) M (EmptyHomotopyGroupData G) O d ?hGen
    (mainConnectednessAxiomsWithZero_empty (G := G))
  · intro n c hc
    exact mainGeometricFixedPointCondition_empty (G := G) O d n (M.cellObj c)

theorem mainSliceConnectivity_implies_geometricFixedPoints_empty
    (M : SliceCellModel G) (O : IncompleteTransferSystem G) (d : DimensionFunction G)
    {n : ℤ} {X : OrthogonalSpectrum G}
    (hX : IsSliceConnected (G := G) M O d n X) :
    MainGeometricFixedPointCondition (G := G) (EmptyHomotopyGroupData G) O d n X := by
  exact mainSliceConnectivity_implies_geometricFixedPoints (G := G)
    M (EmptyHomotopyGroupData G) O d
    (mainFixedPointClosureAxioms_empty (G := G) M O d) hX

/-
Legacy connectedness/realization theorem family.
Migration target:
- `MainSliceConnectivity_iff_GeometricFixedPoints_recommended`
- `MainSliceConnectivity_iff_GeometricFixedPoints_recommendedWithBridge`
-/
theorem MainSliceConnectivity_iff_GeometricFixedPoints_of_connectedness_and_syntax
    (M : SliceCellModel G)
    (π : HomotopyGroupData G)
    (O : IncompleteTransferSystem G) (d : DimensionFunction G)
    (hGenerators :
      ∀ {n : ℤ} {c : MainSliceCellData G},
        c ∈ MainSliceCells (G := G) O d n →
          MainGeometricFixedPointCondition (G := G) π O d n (M.cellObj c))
    (hZero :
      ∀ n : ℤ,
        MainGeometricFixedPointCondition (G := G) π O d n (ZeroSpectrum G))
    (hConn : MainConnectednessAxioms (G := G) π)
    (hSyntax : MainSyntaxReconstructionAxiom (G := G) M π O d)
    (n : ℤ) (X : OrthogonalSpectrum G) :
    IsSliceConnected (G := G) M O d n X ↔
      MainGeometricFixedPointCondition (G := G) π O d n X := by
  exact MainSliceConnectivity_iff_GeometricFixedPoints_of_syntaxReconstruction
    (G := G) M π O d
    (mainFixedPointClosureAxioms_of_connectedness (G := G) M π O d hGenerators hZero hConn)
    hSyntax n X

theorem MainSliceConnectivity_iff_GeometricFixedPoints_of_connectednessWithZero_and_syntax
    (M : SliceCellModel G)
    (π : HomotopyGroupData G)
    (O : IncompleteTransferSystem G) (d : DimensionFunction G)
    (hGenerators :
      ∀ {n : ℤ} {c : MainSliceCellData G},
        c ∈ MainSliceCells (G := G) O d n →
          MainGeometricFixedPointCondition (G := G) π O d n (M.cellObj c))
    (hConn : MainConnectednessAxiomsWithZero (G := G) π)
    (hSyntax : MainSyntaxReconstructionAxiom (G := G) M π O d)
    (n : ℤ) (X : OrthogonalSpectrum G) :
    IsSliceConnected (G := G) M O d n X ↔
      MainGeometricFixedPointCondition (G := G) π O d n X := by
  exact MainSliceConnectivity_iff_GeometricFixedPoints_of_syntaxReconstruction
    (G := G) M π O d
    (mainFixedPointClosureAxioms_of_connectednessWithZero (G := G) M π O d hGenerators hConn)
    hSyntax n X

theorem MainSliceConnectivity_iff_GeometricFixedPoints_of_connectedness_and_surjectiveSyntax
    (M : SliceCellModel G)
    (π : HomotopyGroupData G)
    (O : IncompleteTransferSystem G) (d : DimensionFunction G)
    (hGenerators :
      ∀ {n : ℤ} {c : MainSliceCellData G},
        c ∈ MainSliceCells (G := G) O d n →
          MainGeometricFixedPointCondition (G := G) π O d n (M.cellObj c))
    (hZero :
      ∀ n : ℤ,
        MainGeometricFixedPointCondition (G := G) π O d n (ZeroSpectrum G))
    (hConn : MainConnectednessAxioms (G := G) π)
    (hSurj : MainSyntaxSurjective (G := G) M O d)
    (n : ℤ) (X : OrthogonalSpectrum G) :
    IsSliceConnected (G := G) M O d n X ↔
      MainGeometricFixedPointCondition (G := G) π O d n X := by
  exact MainSliceConnectivity_iff_GeometricFixedPoints_of_connectedness_and_syntax
    (G := G) M π O d hGenerators hZero hConn
    (mainSyntaxReconstructionAxiom_of_surjective (G := G) M π O d hSurj) n X

theorem MainSliceConnectivity_iff_GeometricFixedPoints_of_connectednessWithZero_and_surjectiveSyntax
    (M : SliceCellModel G)
    (π : HomotopyGroupData G)
    (O : IncompleteTransferSystem G) (d : DimensionFunction G)
    (hGenerators :
      ∀ {n : ℤ} {c : MainSliceCellData G},
        c ∈ MainSliceCells (G := G) O d n →
          MainGeometricFixedPointCondition (G := G) π O d n (M.cellObj c))
    (hConn : MainConnectednessAxiomsWithZero (G := G) π)
    (hSurj : MainSyntaxSurjective (G := G) M O d)
    (n : ℤ) (X : OrthogonalSpectrum G) :
    IsSliceConnected (G := G) M O d n X ↔
      MainGeometricFixedPointCondition (G := G) π O d n X := by
  exact MainSliceConnectivity_iff_GeometricFixedPoints_of_connectednessWithZero_and_syntax
    (G := G) M π O d hGenerators hConn
    (mainSyntaxReconstructionAxiom_of_surjective (G := G) M π O d hSurj) n X

theorem MainSliceConnectivity_iff_GeometricFixedPoints_of_connectedness_and_conditionalCellRealization
    (M : SliceCellModel G)
    (π : HomotopyGroupData G)
    (O : IncompleteTransferSystem G) (d : DimensionFunction G)
    (hGenerators :
      ∀ {n : ℤ} {c : MainSliceCellData G},
        c ∈ MainSliceCells (G := G) O d n →
          MainGeometricFixedPointCondition (G := G) π O d n (M.cellObj c))
    (hZero :
      ∀ n : ℤ,
        MainGeometricFixedPointCondition (G := G) π O d n (ZeroSpectrum G))
    (hConn : MainConnectednessAxioms (G := G) π)
    (R : MainConditionalCellRealization (G := G) M π O d)
    (n : ℤ) (X : OrthogonalSpectrum G) :
    IsSliceConnected (G := G) M O d n X ↔
      MainGeometricFixedPointCondition (G := G) π O d n X := by
  exact MainSliceConnectivity_iff_GeometricFixedPoints_of_connectedness_and_syntax
    (G := G) M π O d hGenerators hZero hConn
    (mainSyntaxReconstructionAxiom_of_conditionalCellRealization (G := G) M π O d R) n X

theorem MainSliceConnectivity_iff_GeometricFixedPoints_of_connectednessWithZero_and_conditionalCellRealization
    (M : SliceCellModel G)
    (π : HomotopyGroupData G)
    (O : IncompleteTransferSystem G) (d : DimensionFunction G)
    (hGenerators :
      ∀ {n : ℤ} {c : MainSliceCellData G},
        c ∈ MainSliceCells (G := G) O d n →
          MainGeometricFixedPointCondition (G := G) π O d n (M.cellObj c))
    (hConn : MainConnectednessAxiomsWithZero (G := G) π)
    (R : MainConditionalCellRealization (G := G) M π O d)
    (n : ℤ) (X : OrthogonalSpectrum G) :
    IsSliceConnected (G := G) M O d n X ↔
      MainGeometricFixedPointCondition (G := G) π O d n X := by
  exact MainSliceConnectivity_iff_GeometricFixedPoints_of_witness
    (G := G)
    M
    π
    O
    d
    (mainResultWitness_of_connectednessWithZero_and_conditionalCellRealization
      (G := G) M π O d hGenerators hConn R)
    n
    X

theorem MainSliceConnectivity_iff_GeometricFixedPoints_of_connectednessWithZero_and_conditionalCellRealization_and_isotropyOrthogonal
    (M : SliceCellModel G)
    (π : HomotopyGroupData G)
    (O : IncompleteTransferSystem G) (d : DimensionFunction G)
    (hGenerators :
      ∀ {n : ℤ} {c : MainSliceCellData G},
        c ∈ MainSliceCells (G := G) O d n →
          MainGeometricFixedPointCondition (G := G) π O d n (M.cellObj c))
    (hConn : MainConnectednessAxiomsWithZero (G := G) π)
    (D : IsotropySeparationData G)
    (lift : OrthogonalSpectrum G → D.spectrum)
    (family : ℤ → OrthogonalSpectrum G → SubgroupFamily G)
    (hOrth :
      ∀ {n : ℤ} {X : OrthogonalSpectrum G},
        MainGeometricFixedPointCondition (G := G) π O d n X →
          ∀ H : Subgroup G, IsPhiFamilyOrthogonal D H (family n X) (lift X))
    (R : MainConditionalCellRealization (G := G) M π O d)
    (n : ℤ) (X : OrthogonalSpectrum G) :
    IsSliceConnected (G := G) M O d n X ↔
      MainGeometricFixedPointCondition (G := G) π O d n X := by
  exact MainSliceConnectivity_iff_GeometricFixedPoints_of_witness
    (G := G)
    M
    π
    O
    d
    (mainResultWitness_of_connectednessWithZero_and_conditionalCellRealization_and_isotropyOrthogonal
      (G := G) M π O d hGenerators hConn D lift family hOrth R)
    n
    X

theorem MainSliceConnectivity_iff_GeometricFixedPoints_of_connectednessWithZero_and_conditionalCellRealization_and_bridge
    (M : SliceCellModel G)
    (π : HomotopyGroupData G)
    (O : IncompleteTransferSystem G) (d : DimensionFunction G)
    (hGenerators :
      ∀ {n : ℤ} {c : MainSliceCellData G},
        c ∈ MainSliceCells (G := G) O d n →
          MainGeometricFixedPointCondition (G := G) π O d n (M.cellObj c))
    (hConn : MainConnectednessAxiomsWithZero (G := G) π)
    (B : MainIsotropyOrthogonalBridge (G := G) M π O d)
    (R : MainConditionalCellRealization (G := G) M π O d)
    (n : ℤ) (X : OrthogonalSpectrum G) :
    IsSliceConnected (G := G) M O d n X ↔
      MainGeometricFixedPointCondition (G := G) π O d n X := by
  exact MainSliceConnectivity_iff_GeometricFixedPoints_of_witness
    (G := G)
    M
    π
    O
    d
    (mainResultWitness_of_connectednessWithZero_and_conditionalCellRealization_and_bridge
      (G := G) M π O d hGenerators hConn B R)
    n
    X

theorem MainSliceConnectivity_iff_GeometricFixedPoints_of_connectednessWithZero_and_conditionalCellSurjective
    (M : SliceCellModel G)
    (π : HomotopyGroupData G)
    (O : IncompleteTransferSystem G) (d : DimensionFunction G)
    (hGenerators :
      ∀ {n : ℤ} {c : MainSliceCellData G},
        c ∈ MainSliceCells (G := G) O d n →
          MainGeometricFixedPointCondition (G := G) π O d n (M.cellObj c))
    (hConn : MainConnectednessAxiomsWithZero (G := G) π)
    (hCondSurj : MainConditionalCellSurjective (G := G) M π O d)
    (n : ℤ) (X : OrthogonalSpectrum G) :
    IsSliceConnected (G := G) M O d n X ↔
      MainGeometricFixedPointCondition (G := G) π O d n X := by
  exact MainSliceConnectivity_iff_GeometricFixedPoints_of_forwardPath_and_conditionalCellSurjective
    (G := G) M π O d
    (.generator
      (mainGeneratorGeometricCondition_of_cells (G := G) M π O d hGenerators)
      hConn)
    hCondSurj
    n
    X

theorem MainSliceConnectivity_iff_GeometricFixedPoints_of_connectednessWithZero_and_conditionalCellSurjective_and_bridge
    (M : SliceCellModel G)
    (π : HomotopyGroupData G)
    (O : IncompleteTransferSystem G) (d : DimensionFunction G)
    (hGenerators :
      ∀ {n : ℤ} {c : MainSliceCellData G},
        c ∈ MainSliceCells (G := G) O d n →
          MainGeometricFixedPointCondition (G := G) π O d n (M.cellObj c))
    (hConn : MainConnectednessAxiomsWithZero (G := G) π)
    (B : MainIsotropyOrthogonalBridge (G := G) M π O d)
    (hCondSurj : MainConditionalCellSurjective (G := G) M π O d)
    (n : ℤ) (X : OrthogonalSpectrum G) :
    IsSliceConnected (G := G) M O d n X ↔
      MainGeometricFixedPointCondition (G := G) π O d n X := by
  exact MainSliceConnectivity_iff_GeometricFixedPoints_of_forwardPath_and_conditionalCellSurjective_and_bridge
    (G := G) M π O d
    (.generator
      (mainGeneratorGeometricCondition_of_cells (G := G) M π O d hGenerators)
      hConn)
    B
    hCondSurj
    n
    X

theorem MainSliceConnectivity_iff_GeometricFixedPoints_of_generatorCondition_and_conditionalCellSurjective
    (M : SliceCellModel G)
    (π : HomotopyGroupData G)
    (O : IncompleteTransferSystem G) (d : DimensionFunction G)
    (hGen : MainGeneratorGeometricCondition (G := G) M π O d)
    (hConn : MainConnectednessAxiomsWithZero (G := G) π)
    (hCondSurj : MainConditionalCellSurjective (G := G) M π O d)
    (n : ℤ) (X : OrthogonalSpectrum G) :
    IsSliceConnected (G := G) M O d n X ↔
      MainGeometricFixedPointCondition (G := G) π O d n X := by
  exact MainSliceConnectivity_iff_GeometricFixedPoints_of_forwardPath_and_conditionalCellSurjective
    (G := G) M π O d (.generator hGen hConn) hCondSurj n X

theorem MainSliceConnectivity_iff_GeometricFixedPoints_of_generatorCondition_and_conditionalCellSurjective_and_bridge
    (M : SliceCellModel G)
    (π : HomotopyGroupData G)
    (O : IncompleteTransferSystem G) (d : DimensionFunction G)
    (hGen : MainGeneratorGeometricCondition (G := G) M π O d)
    (hConn : MainConnectednessAxiomsWithZero (G := G) π)
    (B : MainIsotropyOrthogonalBridge (G := G) M π O d)
    (hCondSurj : MainConditionalCellSurjective (G := G) M π O d)
    (n : ℤ) (X : OrthogonalSpectrum G) :
    IsSliceConnected (G := G) M O d n X ↔
      MainGeometricFixedPointCondition (G := G) π O d n X := by
  exact MainSliceConnectivity_iff_GeometricFixedPoints_of_forwardPath_and_conditionalCellSurjective_and_bridge
    (G := G) M π O d (.generator hGen hConn) B hCondSurj n X

theorem MainSliceConnectivity_iff_GeometricFixedPoints_of_connectedness_and_cellSurjective
    (M : SliceCellModel G)
    (π : HomotopyGroupData G)
    (O : IncompleteTransferSystem G) (d : DimensionFunction G)
    (hGenerators :
      ∀ {n : ℤ} {c : MainSliceCellData G},
        c ∈ MainSliceCells (G := G) O d n →
          MainGeometricFixedPointCondition (G := G) π O d n (M.cellObj c))
    (hZero :
      ∀ n : ℤ,
        MainGeometricFixedPointCondition (G := G) π O d n (ZeroSpectrum G))
    (hConn : MainConnectednessAxioms (G := G) π)
    (hCellSurj : MainCellSurjectiveAtLevel (G := G) M O d)
    (n : ℤ) (X : OrthogonalSpectrum G) :
    IsSliceConnected (G := G) M O d n X ↔
      MainGeometricFixedPointCondition (G := G) π O d n X := by
  exact MainSliceConnectivity_iff_GeometricFixedPoints_of_connectedness_and_surjectiveSyntax
    (G := G) M π O d hGenerators hZero hConn
    (mainSyntaxSurjective_of_cellSurjectiveAtLevel (G := G) M O d hCellSurj) n X

theorem MainSliceConnectivity_iff_GeometricFixedPoints_of_connectednessWithZero_and_cellSurjective
    (M : SliceCellModel G)
    (π : HomotopyGroupData G)
    (O : IncompleteTransferSystem G) (d : DimensionFunction G)
    (hGenerators :
      ∀ {n : ℤ} {c : MainSliceCellData G},
        c ∈ MainSliceCells (G := G) O d n →
          MainGeometricFixedPointCondition (G := G) π O d n (M.cellObj c))
    (hConn : MainConnectednessAxiomsWithZero (G := G) π)
    (hCellSurj : MainCellSurjectiveAtLevel (G := G) M O d)
    (n : ℤ) (X : OrthogonalSpectrum G) :
    IsSliceConnected (G := G) M O d n X ↔
      MainGeometricFixedPointCondition (G := G) π O d n X := by
  exact MainSliceConnectivity_iff_GeometricFixedPoints_of_connectednessWithZero_and_surjectiveSyntax
    (G := G) M π O d hGenerators hConn
    (mainSyntaxSurjective_of_cellSurjectiveAtLevel (G := G) M O d hCellSurj) n X

theorem MainSliceConnectivity_iff_GeometricFixedPoints_of_connectedness_and_realization
    (M : SliceCellModel G)
    (π : HomotopyGroupData G)
    (O : IncompleteTransferSystem G) (d : DimensionFunction G)
    (hGenerators :
      ∀ {n : ℤ} {c : MainSliceCellData G},
        c ∈ MainSliceCells (G := G) O d n →
          MainGeometricFixedPointCondition (G := G) π O d n (M.cellObj c))
    (hZero :
      ∀ n : ℤ,
        MainGeometricFixedPointCondition (G := G) π O d n (ZeroSpectrum G))
    (hConn : MainConnectednessAxioms (G := G) π)
    (R : MainCellRealization (G := G) M O d)
    (n : ℤ) (X : OrthogonalSpectrum G) :
    IsSliceConnected (G := G) M O d n X ↔
      MainGeometricFixedPointCondition (G := G) π O d n X := by
  exact MainSliceConnectivity_iff_GeometricFixedPoints_of_connectedness_and_cellSurjective
    (G := G) M π O d hGenerators hZero hConn
    (mainCellSurjectiveAtLevel_of_realization (G := G) M O d R) n X

theorem MainSliceConnectivity_iff_GeometricFixedPoints_of_connectednessWithZero_and_realization
    (M : SliceCellModel G)
    (π : HomotopyGroupData G)
    (O : IncompleteTransferSystem G) (d : DimensionFunction G)
    (hGenerators :
      ∀ {n : ℤ} {c : MainSliceCellData G},
        c ∈ MainSliceCells (G := G) O d n →
          MainGeometricFixedPointCondition (G := G) π O d n (M.cellObj c))
    (hConn : MainConnectednessAxiomsWithZero (G := G) π)
    (R : MainCellRealization (G := G) M O d)
    (n : ℤ) (X : OrthogonalSpectrum G) :
    IsSliceConnected (G := G) M O d n X ↔
      MainGeometricFixedPointCondition (G := G) π O d n X := by
  exact MainSliceConnectivity_iff_GeometricFixedPoints_of_connectednessWithZero_and_cellSurjective
    (G := G) M π O d hGenerators hConn
    (mainCellSurjectiveAtLevel_of_realization (G := G) M O d R) n X

theorem mainSliceConnectivity_iff_geometricFixedPoints_empty_of_surjectiveSyntax
    (M : SliceCellModel G) (O : IncompleteTransferSystem G) (d : DimensionFunction G)
    (hSurj : MainSyntaxSurjective (G := G) M O d)
    (n : ℤ) (X : OrthogonalSpectrum G) :
    IsSliceConnected (G := G) M O d n X ↔
      MainGeometricFixedPointCondition (G := G) (EmptyHomotopyGroupData G) O d n X := by
  exact MainSliceConnectivity_iff_GeometricFixedPoints_of_connectednessWithZero_and_surjectiveSyntax
    (G := G)
    M
    (EmptyHomotopyGroupData G)
    O
    d
    (fun {n} {c} hc =>
      mainGeometricFixedPointCondition_empty (G := G) O d n (M.cellObj c))
    (mainConnectednessAxiomsWithZero_empty (G := G))
    hSurj
    n
    X

theorem mainSliceConnectivity_iff_geometricFixedPoints_empty_of_conditionalCellRealization
    (M : SliceCellModel G) (O : IncompleteTransferSystem G) (d : DimensionFunction G)
    (R : MainConditionalCellRealization (G := G) M (EmptyHomotopyGroupData G) O d)
    (n : ℤ) (X : OrthogonalSpectrum G) :
    IsSliceConnected (G := G) M O d n X ↔
      MainGeometricFixedPointCondition (G := G) (EmptyHomotopyGroupData G) O d n X := by
  exact MainSliceConnectivity_iff_GeometricFixedPoints_of_syntaxReconstruction
    (G := G)
    M
    (EmptyHomotopyGroupData G)
    O
    d
    (mainFixedPointClosureAxioms_empty (G := G) M O d)
    (mainSyntaxReconstructionAxiom_of_conditionalCellRealization
      (G := G) M (EmptyHomotopyGroupData G) O d R)
    n
    X

theorem mainSliceConnectivity_iff_geometricFixedPoints_empty_of_global_and_conditionalCellRealization
    (M : SliceCellModel G) (O : IncompleteTransferSystem G) (d : DimensionFunction G)
    (R : MainConditionalCellRealization (G := G) M (EmptyHomotopyGroupData G) O d)
    (n : ℤ) (X : OrthogonalSpectrum G) :
    IsSliceConnected (G := G) M O d n X ↔
      MainGeometricFixedPointCondition (G := G) (EmptyHomotopyGroupData G) O d n X := by
  exact MainSliceConnectivity_iff_GeometricFixedPoints_of_global_and_syntaxReconstruction
    (G := G)
    M
    (EmptyHomotopyGroupData G)
    O
    d
    (mainGlobalGeometricFixedPointCondition_empty (G := G) O d)
    (mainSyntaxReconstructionAxiom_of_conditionalCellRealization
      (G := G) M (EmptyHomotopyGroupData G) O d R)
    n
    X

theorem mainSliceConnectivity_iff_geometricFixedPoints_empty_of_cellSurjective
    (M : SliceCellModel G) (O : IncompleteTransferSystem G) (d : DimensionFunction G)
    (hCellSurj : MainCellSurjectiveAtLevel (G := G) M O d)
    (n : ℤ) (X : OrthogonalSpectrum G) :
    IsSliceConnected (G := G) M O d n X ↔
      MainGeometricFixedPointCondition (G := G) (EmptyHomotopyGroupData G) O d n X := by
  exact mainSliceConnectivity_iff_geometricFixedPoints_empty_of_surjectiveSyntax
    (G := G) M O d
    (mainSyntaxSurjective_of_cellSurjectiveAtLevel (G := G) M O d hCellSurj)
    n
    X

theorem mainSliceConnectivity_iff_geometricFixedPoints_empty_of_realization
    (M : SliceCellModel G) (O : IncompleteTransferSystem G) (d : DimensionFunction G)
    (R : MainCellRealization (G := G) M O d)
    (n : ℤ) (X : OrthogonalSpectrum G) :
    IsSliceConnected (G := G) M O d n X ↔
      MainGeometricFixedPointCondition (G := G) (EmptyHomotopyGroupData G) O d n X := by
  exact mainSliceConnectivity_iff_geometricFixedPoints_empty_of_cellSurjective
    (G := G) M O d
    (mainCellSurjectiveAtLevel_of_realization (G := G) M O d R)
    n
    X

def mainResultWitness_empty_of_realization
    (M : SliceCellModel G) (O : IncompleteTransferSystem G) (d : DimensionFunction G)
    (R : MainCellRealization (G := G) M O d) :
    MainResultWitness (G := G) M (EmptyHomotopyGroupData G) O d where
  closure := mainFixedPointClosureAxioms_empty (G := G) M O d
  reconstruction :=
    mainReconstructionAxiom_of_conditionalCellRealization (G := G)
      M
      (EmptyHomotopyGroupData G)
      O
      d
      (mainConditionalCellRealization_of_realization
        (G := G) M (EmptyHomotopyGroupData G) O d R)

theorem mainSliceConnectivity_iff_geometricFixedPoints_empty_of_witness
    (M : SliceCellModel G) (O : IncompleteTransferSystem G) (d : DimensionFunction G)
    (W : MainResultWitness (G := G) M (EmptyHomotopyGroupData G) O d)
    (n : ℤ) (X : OrthogonalSpectrum G) :
    IsSliceConnected (G := G) M O d n X ↔
      MainGeometricFixedPointCondition (G := G) (EmptyHomotopyGroupData G) O d n X := by
  exact MainSliceConnectivity_iff_GeometricFixedPoints_of_witness
    (G := G) M (EmptyHomotopyGroupData G) O d W n X

theorem mainOperadSliceConnectivity_iff_geometricFixedPoints_empty_of_realization
    (M : SliceCellModel G) (Oinf : NInfinityOperad G) (d : DimensionFunction G)
    (R : MainCellRealization (G := G) M Oinf.transferSystem d)
    (n : ℤ) (X : OrthogonalSpectrum G) :
    IsSliceConnected (G := G) M Oinf.transferSystem d n X ↔
      MainGeometricFixedPointCondition
        (G := G) (EmptyHomotopyGroupData G) Oinf.transferSystem d n X := by
  exact MainOperadSliceConnectivity_iff_GeometricFixedPoints_of_global_and_realization
    (G := G)
    M
    (EmptyHomotopyGroupData G)
    Oinf
    d
    (mainGlobalGeometricFixedPointCondition_empty (G := G) Oinf.transferSystem d)
    R
    n
    X

theorem mainIndexingSystemSliceConnectivity_iff_geometricFixedPoints_empty_of_realization
    (M : SliceCellModel G) (I : IndexingSystem G) (d : DimensionFunction G)
    (R : MainCellRealization (G := G) M I.toTransferSystem d)
    (n : ℤ) (X : OrthogonalSpectrum G) :
    IsSliceConnected (G := G) M I.toTransferSystem d n X ↔
      MainGeometricFixedPointCondition
        (G := G) (EmptyHomotopyGroupData G) I.toTransferSystem d n X := by
  exact MainIndexingSystemSliceConnectivity_iff_GeometricFixedPoints_of_global_and_realization
    (G := G)
    M
    (EmptyHomotopyGroupData G)
    I
    d
    (mainGlobalGeometricFixedPointCondition_empty (G := G) I.toTransferSystem d)
    R
    n
    X

end Equivariant
