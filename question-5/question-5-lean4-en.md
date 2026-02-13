# Lean4 Formalization Notes for Question 5 (English)

## Status
This version separates definitions from theorem statements and proves both directions in a **concrete model**.  
In addition, `Equivariant/Paper/MainTheorem.lean` now provides paper-facing theorem
entry points that do not expose `MainFixedPointClosureAxioms` /
`MainReconstructionAxiom` directly at call sites.

## Formal Setup
File: `Question5.lean`

1. Incomplete transfer system  
`IncompleteTransferSystem G` defines a transfer relation on subgroups with reflexivity, transitivity, and subgroup compatibility.  
`IndexingSystem G` is added on top with explicit upward/downward closure fields.

2. Slice cells and generators  
- `SliceCellData G`: `fromSubgroup`, `toSubgroup`, `degree`.  
- `IsOSliceCell O d n c`: admissibility given by transfer-admissibility, a source-threshold bound, and nonnegative degree.  
- `OSliceCells O d n` and `SliceGenerators O d n` (singletons of admissible cells).

3. Localizing subcategory model  
Objects are `SpectrumObj G := Set (SliceCellData G)`.  
`InLocalizing` is an inductive closure with:
- `zero = ∅`
- `susp` (identity in this toy stable model)
- `cofiber = union`
- `colim = iUnion`

Then
`OSliceConnectivity O d n X := InLocalizing (SliceGenerators O d n) X`.

4. Geometric fixed-point side  
- `GeometricFixedPoints O H X := {c ∈ X | O.transfer H c.fromSubgroup}`  
- `GeometricFixedPointCondition O d n X`: every visible cell in `Φ^H(X)` satisfies transfer admissibility and degree lower bound.

The threshold function `d : DimensionFunction G` explicitly depends on `O`, so incompleteness affects connectivity bounds.  
`DimensionFunctionSpec d` enforces monotonicity along transfers: if `H → K`, then `d(O,H,n) ≤ d(O,K,n)`.

## Main Theorem and Proof
Main theorem:
`oSliceConnectivity_iff_geometricFixedPoints` (plus operad and indexing-system versions).

1. Forward direction (`slice ⇒ fixed points`)  
Proved by induction on `InLocalizing`, checking closure for generator/zero/susp/cofiber/colim.  
In the generator case, monotonicity from `DimensionFunctionSpec` transports bounds from `fromSubgroup` to any visible subgroup `H`.

2. Reverse direction (`fixed points ⇒ slice`)  
For each `c ∈ X`, apply the fixed-point condition at `H = c.fromSubgroup` to obtain transfer and threshold bounds;  
use the connective assumption `IsConnective X` to obtain `0 ≤ degree`, completing cell admissibility.  
Express `X` as the union of singleton generators `{c}` and close under `colim`, yielding `OSliceConnectivity`.

So the hard reconstruction step is completed in this model.

## Verification
- `lake build` succeeds (`645 jobs`).
- `Question5.lean` has no `sorry` and no custom `axiom`.
- Unified verification script added: `scripts/verify.sh`.

## Paper-Layer Entry (New)
File: `Equivariant/Paper/MainTheorem.lean`

This module exposes paper-facing main theorem entries (base/operad/indexing):
- `Equivariant.Paper.sliceConnectivity_iff_geometricFixedPoints`
- `Equivariant.Paper.operad_sliceConnectivity_iff_geometricFixedPoints`
- `Equivariant.Paper.indexingSystem_sliceConnectivity_iff_geometricFixedPoints`

Bridge variants:
- `..._withBridge`

Single-call constructors from global assumptions:
- `..._of_global_and_conditionalCellSurjective`
- `..._of_global_and_realization`

These interfaces use `SliceInput` / `OperadInput` / `IndexingInput` wrappers so
the final theorem call no longer carries low-level closure/reconstruction
arguments explicitly.

Additionally, a non-degenerate toy-model entry (without the
`EmptyHomotopyGroupData` shortcut) is now exported:
- `Equivariant.Paper.toy_sliceConnectivity_iff_geometricFixedPoints`
- `Equivariant.Paper.toy_operad_sliceConnectivity_iff_geometricFixedPoints`
- `Equivariant.Paper.toy_indexingSystem_sliceConnectivity_iff_geometricFixedPoints`
in `Equivariant/Paper/ToyModelTheorem.lean`.

## Definition-Lemma-Theorem Map
1. Core definitions  
`Question5.lean`: `IncompleteTransferSystem`, `IndexingSystem`, `IsOSliceCell`,
`OSliceConnectivity`, `GeometricFixedPointCondition`.  
`Equivariant/Slice/Filtration.lean`: `IsSliceConnected` (orthogonal-spectrum layer).

2. Geometric fixed points and closure tools  
`Equivariant/FixedPoints/Geometric.lean`: `GeometricFixedPoints` and levelwise
equivalences for `zero/susp/cofiber/colim`.  
`Equivariant/MainResult.lean`: `mainFixedPointClosureAxioms_of_forwardPath`.

3. Reverse reconstruction chain  
`Equivariant/MainResult.lean`: `MainConditionalCellSurjective`,
`mainReconstructionAxiom_of_conditionalCellSurjective`.

4. Main characterization theorems  
Concrete model: `Question5.oSliceConnectivity_iff_geometricFixedPoints`.  
Paper-layer unified entry: `Equivariant.Paper.sliceConnectivity_iff_geometricFixedPoints`,
plus operad and indexing-system specializations.  
Non-degenerate toy-model entry: `Equivariant.Paper.toy_sliceConnectivity_iff_geometricFixedPoints`.

## Added Layered Interface (Roadmap Execution)
New layered modules were added under `Equivariant/*` to support migration toward a fully categorical implementation:
- `Equivariant/IndexingSystem.lean`: `IncompleteTransferSystem`, `IndexingSystem`, `DimensionFunction`.
- `Equivariant/Spectra/Orthogonal.lean`: abstract `J_G`/`OrthogonalGSpectrum` interface, `SpectrumHom.id/comp`, `OmegaSpectrum`, `StableModelStructure`, and weak-vs-stable equivalence bridge lemmas.
- `Equivariant/Slice/Generators.lean`: abstract `SpectrumLike`, slice generators, `InLocalizing`.
- `Equivariant/FixedPoints/Geo.lean`: geometric fixed-point interface and closure axioms.
- `Equivariant/FixedPoints/Isotropy.lean`: isotropy-separation data interface, functorial compatibility constraints, and derived lemmas such as `phi_isotropy_cofiber`.
- `Equivariant/Slice/MainTheorem.lean`: interface-level characterization theorem.
- `Equivariant/Instances/ToyModel.lean`: bridge instance from the interface theorem to the current cell-set concrete model.

`lakefile.lean` now includes `Equivariant` as a default build root; both `Question5.lean` and the new interface layer build successfully together.

## Latest Addition: Final Entry Theorems in `MainPayloadModel`
To eliminate call-site boilerplate, we added:
- `Equivariant/Instances/MainPayloadModel.lean`

This module provides a constructive instance:
- `model : SliceCellModel G` (reads `MainSliceCellData.realization` directly),
- explicit `realization : MainCellRealization ...` (no extra cell-surjectivity argument needed).

It also exposes three no-extra-assumption entry theorems (inputs are only `O/Oinf/I, d, n, X`):
- `final_transferSystem_sliceConnectivity_iff_geometricFixedPoints`
- `final_operad_sliceConnectivity_iff_geometricFixedPoints`
- `final_indexingSystem_sliceConnectivity_iff_geometricFixedPoints`

Minimal transfer-system usage:
```lean
open Equivariant.Instances.MainPayloadModel

example {G : Type} [Group G]
    (O : Equivariant.IncompleteTransferSystem G)
    (d : Equivariant.DimensionFunction G)
    (n : ℤ) (X : Equivariant.OrthogonalSpectrum G) :
    Equivariant.IsSliceConnected (M := model (G := G)) O d n X ↔
      Equivariant.MainGeometricFixedPointCondition
        (π := Equivariant.EmptyHomotopyGroupData G) O d n X :=
  final_transferSystem_sliceConnectivity_iff_geometricFixedPoints
    (G := G) O d n X
```

Note: these final-entry theorems are complete in the current payload/toy layer; they are not yet the full homotopy-theoretic orthogonal `G`-spectra implementation.

## Recommended API Matrix (Current Stage)

### 1. Base (`IncompleteTransferSystem`)
- Without bridge: `MainSliceConnectivity_iff_GeometricFixedPoints_recommended`
- With bridge: `MainSliceConnectivity_iff_GeometricFixedPoints_recommendedWithBridge`
- Recommended input constructors:
  - `mainRecommendedInput_of_global_and_conditionalCellSurjective`
  - `mainRecommendedInput_of_generator_and_conditionalCellSurjective`
  - `mainRecommendedInputWithBridge_of_global_and_conditionalCellSurjective`
  - `mainRecommendedInputWithBridge_of_generator_and_conditionalCellSurjective`

### 2. Operad (`NInfinityOperad`)
- Without bridge: `MainOperadSliceConnectivity_iff_GeometricFixedPoints_recommended`
- With bridge: `MainOperadSliceConnectivity_iff_GeometricFixedPoints_recommendedWithBridge`
- Recommended input constructors:
  - `mainOperadRecommendedInput_of_global_and_conditionalCellSurjective`
  - `mainOperadRecommendedInputWithBridge_of_global_and_conditionalCellSurjective`

### 3. IndexingSystem
- Without bridge: `MainIndexingSystemSliceConnectivity_iff_GeometricFixedPoints_recommended`
- With bridge: `MainIndexingSystemSliceConnectivity_iff_GeometricFixedPoints_recommendedWithBridge`
- Recommended input constructors:
  - `mainIndexingSystemRecommendedInput_of_global_and_conditionalCellSurjective`
  - `mainIndexingSystemRecommendedInputWithBridge_of_global_and_conditionalCellSurjective`

Suggested shortest path:
1. Prefer `*_recommended` / `*_recommendedWithBridge`.
2. Build inputs via `*_of_global_and_conditionalCellSurjective`.
3. If you only have `MainCellRealization`, first convert with `mainConditionalCellSurjective_of_realization`.

## Ready-to-Copy Snippets

For copy-ready 3x2 examples (base/operad/indexing × with/without bridge), see:
- `docs/recommended-api-examples.md`

## API Stability Tiers

For recommended/transitional/legacy classification and migration guidance, see:
- `docs/api-stability.md`
- `docs/legacy-to-recommended-checklist.md`
- `docs/legacy-to-recommended-bridge-checklist.md`
