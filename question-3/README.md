# Question 3 Formalization (Lean 4)

This repository formalizes **Question 3** as a machine-checked mathematical result in Lean 4.

## What problem is solved?

The project proves, on restricted sectors of the ring multi-species ASEP model, that:

1. Exchange-type algebraic relations imply local detailed balance.
2. Local detailed balance implies global balance (stationarity equation).
3. Under explicit positivity and normalization assumptions, the constructed weights define a valid stationary probability distribution.
4. A nontrivial discrete-time Markov kernel can be built by uniformization, with strictly positive off-diagonal transitions.

In paper language: the development gives a verified bridge from a Macdonald-style algebraic interface to a complete stationary-measure statement of the form \(F^*/P^*\).

## How to run

Use the pinned Lean toolchain (`v4.26.0`) and Lake.

```bash
[ -f "$HOME/.elan/env" ] && source "$HOME/.elan/env"
lean --version
lake update
lake build
```

Targeted checks for key modules:

```bash
lake env lean Question3.lean
lake env lean Macdonald/Bridge/FinalTheorem.lean
lake env lean Macdonald/Bridge/LiteratureCompletion.lean
```

Check for unfinished placeholders:

```bash
rg -n "sorry|admit|axiom" Question3.lean Macdonald/**/*.lean
```

## Directory and file guide

- `Question3.lean`  
  Core ASEP formalization: swap dynamics, edge/transition rates, local detailed balance, global stationarity, and nonnegativity interface (`RatePairNonneg`).

- `Macdonald/Bridge/PaperTheorem.lean`  
  Paper-facing wrappers and explicit restricted-sector theorem statements.

- `Macdonald/Bridge/FinalTheorem.lean`  
  Final packaged continuous/discrete Markov chain statements:
  - `question3_complete_restricted_qOne`
  - `question3_complete_restricted_qOne_discrete`

- `Macdonald/Bridge/LiteratureCompletion.lean`  
  Literature-interface closure theorem:
  - `paper_main_restricted_qOne_discrete_of_literature_assumptions`

- `Macdonald/Bridge/*.lean`  
  Supporting bridge layers (restricted-sector setup, candidate models, specialization workflow).

- `lakefile.lean`, `lake-manifest.json`, `lean-toolchain`  
  Build configuration and dependency lock.

- `question-3-paper.tex`, `question-3-paper.pdf`  
  Research-paper manuscript and compiled PDF.

- `question-3.tex`  
  Original problem statement source.

## Result summary

The formalization now reaches a paper-grade endpoint for the restricted \(q=1\) setting:

- stationarity is proven from local exchange identities,
- nonnegativity and normalization are explicit assumptions/outputs where needed,
- nontrivial dynamics are formally witnessed,
- final theorems are exposed in reusable theorem interfaces.

## AI-assisted workflow (what was done)

This project was developed with an AI-assisted theorem-engineering workflow:

1. **Problem decomposition**  
   Split the target result into independent layers: local algebra, global balance, positivity, normalization, and nontriviality.

2. **Interface-first design**  
   Introduced explicit structures (candidate/interface assumptions) so special-function identities are black-box inputs, while probability conclusions are fully derived.

3. **Compiler-guided iteration**  
   Repeated Lean compile/proof loops were used to eliminate gaps, strengthen hypotheses, and align theorem signatures.

4. **Proof packaging**  
   Built paper-facing wrappers and final bundled theorems for direct citation in mathematical writing.

5. **Verification pass**  
   Ensured project build success and removal of unfinished placeholders.

## Code repository

Lean 4 code: <https://github.com/amadeuzou/1stProof-lean4>
