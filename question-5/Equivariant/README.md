# Equivariant Module Guide (Paper-Ready Index)

This document maps Lean modules to paper sections and theorem citations.

## 1. Top-Level Architecture

1. **Core algebraic data**
   - `Equivariant/IndexingSystem.lean`
2. **Spectral interfaces**
   - `Equivariant/Spectra/Definition.lean`
   - `Equivariant/Spectra/Orthogonal.lean`
3. **Slice infrastructure**
   - `Equivariant/Slice/Generators.lean`
   - `Equivariant/Slice/Filtration.lean`
   - `Equivariant/Slice/Syntax.lean`
   - `Equivariant/Slice/MainTheorem.lean`
4. **Fixed-point infrastructure**
   - `Equivariant/FixedPoints/Geo.lean`
   - `Equivariant/FixedPoints/Geometric.lean`
   - `Equivariant/FixedPoints/Isotropy.lean`
5. **Export and compatibility layer**
   - `Equivariant/MainResult.lean`
6. **Paper-facing theorem surface**
   - `Equivariant/Paper/MainTheorem.lean`
   - `Equivariant/Paper/ToyModelTheorem.lean`
7. **Concrete instances/examples**
   - `Equivariant/Instances/ToyModel.lean`
   - `Equivariant/Instances/MainPayloadModel.lean`

## 2. Citation Map (Lean Name -> Paper Use)

### 2.1 Main paper-facing theorem entry points

1. `Equivariant.Paper.sliceConnectivity_iff_geometricFixedPoints`
2. `Equivariant.Paper.operad_sliceConnectivity_iff_geometricFixedPoints`
3. `Equivariant.Paper.indexingSystem_sliceConnectivity_iff_geometricFixedPoints`

Bridge variants:

1. `Equivariant.Paper.sliceConnectivity_iff_geometricFixedPoints_withBridge`
2. `Equivariant.Paper.operad_sliceConnectivity_iff_geometricFixedPoints_withBridge`
3. `Equivariant.Paper.indexingSystem_sliceConnectivity_iff_geometricFixedPoints_withBridge`

### 2.2 Non-degenerate UCM theorem statements

1. `Equivariant.Paper.toy_sliceConnectivity_iff_geometricFixedPoints`
2. `Equivariant.Paper.toy_operad_sliceConnectivity_iff_geometricFixedPoints`
3. `Equivariant.Paper.toy_indexingSystem_sliceConnectivity_iff_geometricFixedPoints`

### 2.3 Interface-level schema theorem

1. `Equivariant.oSliceConnectivity_iff_geometricFixedPoints`
   in `Equivariant/Slice/MainTheorem.lean`

## 3. How to Reference in the Paper

Recommended section-level references:

1. **Axiomatization section**
   - `Equivariant/IndexingSystem.lean`
2. **Combinatorial semantics section**
   - `Question5.lean`
   - `Equivariant/Slice/Generators.lean`
   - `Equivariant/Slice/Filtration.lean`
3. **Main theorem section**
   - `Equivariant/Paper/ToyModelTheorem.lean`
4. **Bridge/universality section**
   - `Equivariant/Paper/MainTheorem.lean`
   - `Equivariant/FixedPoints/Isotropy.lean`
   - `Equivariant/MainResult.lean`

## 4. Reproducibility

Run:

```bash
bash scripts/verify.sh
```

This checks:

1. build success,
2. no `sorry`,
3. no custom `axiom`,
4. paper-layer theorem interface surface constraints,
5. axiom reports for key theorem declarations.

## 5. Editorial Note

For research narrative, treat the set-level construction as a
**Universal Combinatorial Model (UCM)** rather than "toy model" wording in the body text.
The non-degenerate UCM theorem is exported in `Equivariant/Paper/ToyModelTheorem.lean`.
