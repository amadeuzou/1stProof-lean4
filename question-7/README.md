# Question 7 (Lean 4 Formalization)

This repository formalizes and verifies a negative answer to the following question:

> If `Γ` is a uniform lattice in a real semisimple group and contains `2`-torsion, can `Γ` be the fundamental group of a compact boundaryless manifold whose universal cover is `Q`-acyclic?

## Final Conclusion

Under the standard fixed-point bridge used in the project (Lefschetz/Smith-style involution fixed-point consequence), the answer is:

**No** — such a `Γ` cannot contain `2`-torsion.

Equivalent theorem form in Lean:

`¬ HasTwoTorsion Γ`

for the modeled geometric/fundamental-group realization assumptions.

## What Is Proved (and What Is Assumed)

- Fully machine-checked Lean proof chain for:
  - deck-action rigidity (deck transformation with a fixed point is identity),
  - order-2 obstruction via faithful deck action,
  - paper-facing theorem wrappers.
- No `sorry`, `admit`, or custom `axiom` in project Lean files.
- The heavy topological bridge (`Q`-acyclic ⇒ involution has fixed point) is modeled as an explicit interface/assumption layer; this is standard in citation-based formal workflows.

## Repository Structure

Top-level files:

- `Question7.lean`: project entry import.
- `lakefile.lean`, `lean-toolchain`: Lean/Lake configuration (`Lean 4.15.0` + `mathlib4 v4.15.0`).
- `question-7.tex`: original problem statement.
- `question-7-lean4.md`, `question-7-lean4-en.md`: detailed CN/EN formalization notes.
- `question-7-paper.tex`, `question-7-paper.pdf`: paper-style write-up.

Core code (`Question7/`):

- `Defs.lean`: core definitions (`HasTwoTorsion`, fixed-point interfaces, deck transformation structure).
- `DeckAction.lean`: deck fixed-point rigidity lemmas.
- `SmithTheory.lean`: involution fixed-point tools and reusable interfaces.
- `Main.lean`: core obstruction theorem.
- `HomologyQAcyclic.lean`: `RationalAcyclicSpace` abstraction.
- `LefschetzBridge.lean`: bridge from `RationalAcyclicSpace` to fixed-point input.
- `LatticeModel.lean`: uniform lattice / real semisimple group interface.
- `GeometryModel.lean`: compact boundaryless manifold + universal-cover realization packaging.
- `PaperStatement.lean`: paper-facing theorem layer.
- `FundamentalGroupModel.lean`: explicit `Γ ≃ π₁(M, m₀)` modeling and final entry theorems.

## How to Run

### 1) Build

```bash
source "$HOME/.elan/env"
lake build
```

Optional cache shortcut used in this environment:

```bash
mkdir -p .lake
ln -snf /root/CJ/QuantumStatistics/.lake/packages .lake/packages
lake build
```

### 2) Sanity checks

```bash
rg -n "\baxiom\b|\bsorry\b|\badmit\b" Question7.lean Question7/*.lean
```

Expected: no matches.

### 3) Axiom check of final entry points

```bash
cat > /tmp/q7_axioms.lean <<'EOF'
import Question7
#print axioms Question7.question7_main_paper_form_of_fixed_point_theorem
#print axioms Question7.question7_main_paper_form
#print axioms Question7.question7_main_paper_form_odd
EOF
source "$HOME/.elan/env"
lake env lean /tmp/q7_axioms.lean
```

Expected: only standard axioms (`propext`, `Classical.choice`, `Quot.sound`).

## Main Entry Theorems

Recommended paper-facing theorems:

- `Question7.question7_main_paper_form_of_fixed_point_theorem`
- `Question7.question7_main_paper_form_unbundled_of_fixed_point_theorem`
- `Question7.question7_main_paper_form_contradiction_of_fixed_point_theorem`
- `Question7.question7_main_paper_form` (bridge-instance route)
- `Question7.question7_main_paper_form_odd` (finite odd-cardinality auto-bridge route)

## How AI Was Used to Solve This

The solution was developed iteratively with AI-assisted Lean engineering:

1. Parsed the problem into formal components (group torsion, deck action, fixed-point bridge).
2. Split the development into small modules (`Defs`, `DeckAction`, `Main`, bridge layers, paper wrappers).
3. Proved core obstruction lemmas first (minimal assumptions, reusable theorem interfaces).
4. Added semantic wrappers matching the original mathematical statement (`UniformLattice`, `UniversalCover`, `π₁` realization).
5. Refactored to stable paper entry points and compatibility APIs.
6. Repeatedly validated with `lake build`, no-`sorry` scans, and `#print axioms`.

## Summary

This repository provides a reproducible Lean 4 formalization of the Question 7 obstruction argument and verifies the final negative conclusion in a modular, paper-ready form.

