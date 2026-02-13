# 1stProof-lean4

Lean 4 formalization project for the **[1stProof Challenge](https://1stproof.org/)**.

This repository tracks my ongoing work on formal proofs for the challenge problems, with AI-assisted theorem development and verification.

## Current Progress

Completed formal proof projects:

- `Problem 3`
- `Problem 5`
- `Problem 7`
- `Problem 8`
- `Problem 9`
- `Problem 10`

In progress:

- `Problem 1`
- `Problem 2`
- `Problem 4`
- `Problem 6`

## Repository Structure

Each completed problem lives in its own standalone Lean package:

- `question-3/`
- `question-5/`
- `question-7/`
- `question-8/`
- `question-9/`
- `question-10/`

Typical contents inside each problem folder:

- `lakefile.lean`, `lean-toolchain` (Lean project config)
- Lean source directory (e.g. `Question9/`, `Question10/`)
- `README.md` (problem-specific notes)
- `question-*-paper.tex` / `question-*-paper.pdf` (write-up)
- `question-*-lean4-en.md` (proof summary in natural language)

## AI4Math Agent Workflow (Core Idea)

My AI4Math Agent mainly combines:

- **Codex 5.3**
- **Gemini 3 Pro**

High-level proof process:

1. Parse the original question and isolate formalizable statements.
2. Design Lean definitions and lemma decomposition.
3. Iteratively synthesize and repair proofs with AI assistance.
4. Validate via `lake build` until fully checked.
5. Produce paper-style mathematical write-ups aligned with verified Lean theorems.

## Links

- [1stProof Challenge](https://1stproof.org/)
- [AI4Math Tool: lean4-skills](https://github.com/cameronfreer/lean4-skills)
- [AI4Math Tool: LeanSearchClient](https://github.com/leanprover-community/LeanSearchClient)
- [AI4Math Tool: TheoremSearch](https://github.com/uw-math-ai/TheoremSearch)
