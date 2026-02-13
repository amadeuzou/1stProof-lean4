# 1stProof Lean4: Question 5

This repository contains a Lean 4 formalization of the Question 5 theorem on equivariant slice connectivity.

## Problem Solved

Given a finite group `G`, an incomplete transfer system `O`, and a threshold function `d`, the project formalizes and proves a characterization theorem of the form:

`slice connectivity` iff `geometric fixed-point connectivity`.

The development includes:

1. a concrete universal combinatorial model (UCM),
2. abstract interface layers for slice/fixed-point structures,
3. paper-facing theorem entry points (base / operad / indexing-system variants),
4. machine-checked proofs with no `sorry` and no custom `axiom`.

## AI-Assisted Development Process

The proof engineering workflow used AI as a formalization assistant, with Lean as the correctness oracle:

1. theorem decomposition into small lemmas and interfaces,
2. iterative compile-repair cycles driven by Lean type errors,
3. API stabilization for theorem reuse,
4. documentation synchronization with final theorem names.

In short: AI helped design and refactor proofs, while Lean provided strict mechanical verification of every accepted step.

## Requirements

1. Lean toolchain pinned in `lean-toolchain` (`v4.26.0`),
2. Lake (`lake`),
3. ripgrep (`rg`) for repository checks.

## Quick Start

From repo root:

```bash
lean --version
lake build
```

Run full verification:

```bash
bash scripts/verify.sh
```

This checks:

1. build success,
2. no `sorry`,
3. no custom `axiom`,
4. paper-layer interface surface constraints,
5. axiom reports for key theorem declarations.

## Build the Paper Files

The paper source is:

- `question-5-paper.tex`

The generated PDF artifact is:

- `question-5-paper.pdf`

If your machine has a TeX engine, you can rebuild with:

```bash
pdflatex question-5-paper.tex
```

## Repository Structure

### Top-level

- `Question5.lean`:
  concrete UCM theorem and core definitions.
- `Equivariant.lean`:
  umbrella import for the layered architecture.
- `question-5-paper.tex` / `question-5-paper.pdf`:
  research-paper manuscript source and PDF.
- `question-5-lean4.md`:
  Chinese formalization notes.
- `question-5-lean4-en.md`:
  English formalization notes.
- `paper_framework.md`:
  paper-writing framework and section plan.

### `Equivariant/`

- `IndexingSystem.lean`:
  transfer/indexing abstractions.
- `Spectra/Definition.lean`, `Spectra/Orthogonal.lean`:
  spectral interfaces and structure.
- `Slice/Generators.lean`, `Slice/Filtration.lean`, `Slice/Syntax.lean`, `Slice/MainTheorem.lean`:
  slice generation, closure, syntax, and interface theorem.
- `FixedPoints/Geometric.lean`, `FixedPoints/Geo.lean`, `FixedPoints/Isotropy.lean`:
  geometric fixed-point and bridge utilities.
- `MainResult.lean`:
  theorem export layer and compatibility wrappers.
- `Paper/MainTheorem.lean`, `Paper/ToyModelTheorem.lean`:
  paper-facing theorem surfaces.
- `Instances/ToyModel.lean`, `Instances/MainPayloadModel.lean`:
  concrete instances and examples.
- `README.md`:
  module-level theorem citation map.

### `docs/`

- `theorem-spec.md`, `theorem-spec-en.md`:
  theorem acceptance specification.
- `the-bridge-draft.md`:
  mathematical draft of the realization bridge section.
- `api-stability.md` and migration checklists:
  API usage guidance.

## Key Lean Declarations to Cite

1. `Question5.oSliceConnectivity_iff_geometricFixedPoints`
2. `Equivariant.Paper.sliceConnectivity_iff_geometricFixedPoints`
3. `Equivariant.Paper.toy_sliceConnectivity_iff_geometricFixedPoints`

## Code Repository Link

Lean4 code link: <https://github.com/amadeuzou/1stProof-lean4>
