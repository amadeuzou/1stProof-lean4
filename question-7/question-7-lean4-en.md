# Question 7 Lean4 Formalization Notes (English)

## Problem
`question-7.tex` asks: if `Γ` is a uniform lattice in a real semisimple group and `Γ` has `2`-torsion, can `Γ` be the fundamental group of a closed manifold whose universal cover is `ℚ`-acyclic?

Answer: **No**.

## Paper-Requirement Status (as of February 13, 2026)
- Under the standard paper convention “you may cite classical fixed-point theorems”: **largely satisfied**.  
  The proof pipeline is explicit and machine-checked, and the heavy topological step is isolated as an auditable input.
- Under the strongest convention “100% in-repo derivation including full Smith/Lefschetz homological machinery”: **not yet satisfied**.  
  This repository still does not contain a full internal development of singular homology and Lefschetz-number fixed-point theory.

## Formalization Approach
This version uses a modular and assumption-explicit approach: no `axiom` and no `sorry` in Lean code. The deepest Smith/Lefschetz fixed-point statement is represented as an explicit input property.
So the Lean chain is internally complete and machine-checked, while the full singular-homology-to-Lefschetz infrastructure is not unfolded inside this repository yet.

Code layout:

- `Question7/Defs.lean`: basic definitions (`HasTwoTorsion`, deck transformations, fixed-point input).
- `Question7/DeckAction.lean`: proves a deck transformation with one fixed point is identity.
- `Question7/SmithTheory.lean`: wraps the fixed-point input as a reusable theorem interface and provides two concrete instances:
  - `Subsingleton` case;
  - finite odd-cardinality case (via `Equiv.Perm.exists_fixed_point_of_prime` with `p = 2`).
- `Question7/Main.lean`: combines all ingredients into `no_two_torsion_of_realization`.
- `Question7/LatticeModel.lean`: interface layer for uniform lattice / real semisimple ambient group assumptions.
- `Question7/GeometryModel.lean`: packaging for compact boundaryless manifold plus universal-cover realization.
- `Question7/HomologyQAcyclic.lean`: homology-facing `ℚ`-acyclic interface package.
- `Question7/LefschetzBridge.lean`: Lefschetz/Smith bridge into fixed-point input.
- `Question7/PaperStatement.lean`: theorem exported in wording close to the original question.
- `Question7/FundamentalGroupModel.lean`: explicit model of the hypothesis `Γ ≃ π₁(M, m₀)` and final contradiction theorem.
  It also provides the one-shot input bundle `OriginalQuestionInput`.
  For the finite odd-cardinality path, it additionally provides `OriginalQuestionInputOdd`.
  It now also provides the bridge-agnostic bundle `OriginalQuestionInputCore`.
- `Question7.lean`: entry file importing `Question7.FundamentalGroupModel`.

Key `RealizationData` fields:
- `deckLift : Γ →* DeckTransformation p` models the lift as an actual group homomorphism;
- `DeckTransformation p` already carries `comm : p ∘ g = p`, so no separate `deckLift_comm` field is needed;
- `deckLift_injective : Function.Injective deckLift` enforces faithfulness (trivial kernel);
- involutivity of `deckLift γ` is then derived automatically from `orderOf γ = 2` in the main proof.

Additional semantic refinements:
- `IsRealSemisimpleGroup H` now carries concrete ambient fields: `TopologicalGroup H`, `T2Space H`, and `LocallyCompactSpace H`;
- `IsUniformLatticeIn Γ H` now includes an explicit discreteness field `DiscreteTopology Γ` and a cocompactness condition `embedding_cocompact : Tendsto embedding (cocompact Γ) (cocompact H)`;
- `CompactBoundarylessManifold` now uses `HasBoundarylessManifoldStructure M` (an existential proposition built from `BoundarylessManifold`) instead of a `True` placeholder;
- `UniversalCoverRealization` now records `simplyConnectedCover : SimplyConnectedSpace E` (instead of a `True` placeholder for the universal-cover aspect).
- In paper-facing exported theorems, `[PreconnectedSpace E]` is no longer a manual assumption; it is inferred from `simplyConnectedCover`.

The main theorem input is now minimized to:
- `hData.HasOrderTwoDeckFixedPointProperty`: only requires fixed points for deck lifts of order-2 group elements;
- `question7_answer_is_no` derives this minimal input automatically from the stronger global hypothesis `HasInvolutiveHomeomorphFixedPointProperty E`.
- A typeclass `InvolutionFixedPointInput E` is also introduced so fixed-point input can be supplied by instances.
- Added `IsQAcyclic E` and `QAcyclicInvolutionFixedPointBridge E`:
  these model the intended “Q-acyclic + Smith/Lefschetz bridge gives fixed points” pipeline.
- `IsQAcyclic E` now carries a `ConnectedSpace E` field, so qacyclic-flavored exported results no longer need a manual `[PreconnectedSpace E]` assumption.
- Added an automatic bridge instance: if `RationalAcyclicSpace E` and `E` has finite odd cardinality, `LefschetzInvolutionFixedPointBridge E` is inferred automatically.
- Added `question7_answer_is_no_of_input_of_connected`, which bridges from `ConnectedSpace E` into the core obstruction proof automatically.
- As a consequence, `question7_answer_is_no_of_subsingleton_cover` no longer needs an explicit `[PreconnectedSpace E]` assumption.
- Added connected-space wrappers for the finite odd-cardinality obstruction and contradiction/nonexistence forms.
- Added simply-connected wrappers (`input`, `finite odd`, contradiction, nonexistence) and a connected-space deck-action identity wrapper.

## Math-to-Code Mapping
- Mathematical “`Γ` has 2-torsion”  
  maps to `HasTwoTorsion Γ := ∃ γ, orderOf γ = 2`.
- Mathematical “deck action is free” (fixed point implies identity)  
  maps to `deckTransformation_eq_refl_homeomorph_of_fixed_point`.
- Mathematical Smith/Lefschetz input for involutive actions  
  maps to `HasInvolutiveHomeomorphFixedPointProperty E`.
- Final obstruction theorem  
  maps to `question7_answer_is_no` (deriving `¬ HasTwoTorsion Γ` from these inputs).
- Paper-facing theorem aligned with the original statement  
  maps to `question7_no_for_uniform_lattice_manifold_model`.
- Finite odd-cardinality paper-facing corollary  
  maps to `question7_no_for_uniform_lattice_manifold_model_of_rationalAcyclic_fintype_odd` (no manual Lefschetz bridge argument needed).
- Paper-facing theorem with explicit fundamental-group witness  
  maps to `question7_no_for_uniform_lattice_with_fundamental_group`.
- One-shot bundled-input theorem  
  maps to `question7_no_of_original_input` (input is `OriginalQuestionInput`).
- One-shot bundled-input theorem (finite odd-cardinality route)  
  maps to `question7_no_of_original_input_rationalAcyclic_fintype_odd` (input is `OriginalQuestionInputOdd`).
- Core bundled-input theorem pair  
  maps to `question7_no_of_original_input_core` (Lefschetz-bridge route) and
  `question7_no_of_original_input_core_rationalAcyclic_fintype_odd` (finite odd-cardinality auto-bridge route).
- Compatibility layer now includes `[simp]` `toCore` lemmas and `via_core` theorems, making the legacy bundled APIs transparently reducible to the core layer.
  Legacy entry theorems (`question7_no_of_original_input`, etc.) now directly delegate to the core proof chain.

## Paper-Style Proof Pipeline (Citation-Based)
1. Assume `Γ` has 2-torsion: choose `γ` with `orderOf γ = 2`.
2. Map `γ` through `deckLift : Γ →* DeckTransformation p`; involutivity of the deck lift is derived in `Question7/Main.lean`.
3. Use the fixed-point theorem input `HasInvolutiveHomeomorphFixedPointProperty E` to obtain a fixed point.
4. Apply deck-action rigidity (`Question7/DeckAction.lean`): a deck transformation with a fixed point is identity.
5. By injectivity of `deckLift`, infer `γ = 1`, contradicting `orderOf γ = 2`; therefore `¬ HasTwoTorsion Γ`.

## External Theorem Citation Points
- In this repository, the heavy step is abstracted as:
  - `HasInvolutiveHomeomorphFixedPointProperty E` (propositional input);
  - `LefschetzInvolutionFixedPointBridge E` (bridge from `ℚ`-acyclic assumptions to the fixed-point input).
- In a paper, cite the specific classical source you are using (depending on your space category):
  - Lefschetz Fixed Point Theorem, or
  - Smith fixed-point results for `p`-group actions.
- Lean entry points for this layer:
  - explicit-citation style: `question7_main_paper_form_of_fixed_point_theorem`;
  - bridge-instance style: `question7_main_paper_form`.

**Recommended Paper Entry Points**
- `question7_main_paper_form_of_fixed_point_theorem`: preferred paper entry (explicit fixed-point theorem input; no bridge typeclass name in the theorem signature).
- `question7_main_paper_form_unbundled_of_fixed_point_theorem`: same theorem with `hGeom + hPi1 + hFixed` arguments.
- `question7_main_paper_form_contradiction_of_fixed_point_theorem`: contradiction form of the explicit-citation route (`False`).
- `question7_main_paper_form`: primary core entry (bridge route, input `OriginalQuestionInputCore`).
- `question7_main_paper_form_unbundled`: same theorem with `hGeom + hPi1` arguments.
- `question7_main_paper_form_odd`: finite odd-cardinality entry (auto-bridge route).
- `question7_main_paper_form_contradiction` / `question7_main_paper_form_odd_contradiction`: contradiction forms returning `False`.
- One-shot bundled-input contradiction form  
  maps to `question7_original_form_answer_of_input` (`HasTwoTorsion Γ → False`).
- Minimal-assumption obstruction theorem  
  maps to `no_two_torsion_of_realization` (input is `HasOrderTwoDeckFixedPointProperty`).
- Typeclass-driven obstruction theorem  
  maps to `question7_answer_is_no_of_input` (input supplied by `InvolutionFixedPointInput E`).
- Q-acyclic bridge obstruction theorem  
  maps to `question7_answer_is_no_of_qacyclic_bridge` (input supplied by `IsQAcyclic` plus bridge instance).
- Q-acyclic + finite odd-cardinality auto-bridge theorem  
  maps to `question7_answer_is_no_of_qacyclic_fintype_odd_cover` (bridge instance is obtained automatically from the odd-cardinality consequence inside `IsQAcyclic`).
- Contradiction-form theorem  
  maps to `question7_contradiction_of_realization_and_two_torsion` (returns `False` directly).
- Nonexistence-form theorem  
  maps to `no_realizationData_nonempty_of_two_torsion` (under 2-torsion, no such `RealizationData` can exist).
- Q-acyclic bridge nonexistence theorem  
  maps to `no_realizationData_nonempty_of_two_torsion_qacyclic_bridge`.
- Q-acyclic + finite odd-cardinality nonexistence theorem  
  maps to `no_realizationData_nonempty_of_two_torsion_qacyclic_fintype_odd`.
- Special-case corollary  
  maps to `question7_answer_is_no_of_subsingleton_cover` (fixed-point input is discharged automatically when `E` is `Subsingleton` and `Inhabited`).
- Finite odd-cardinality corollary  
  maps to `question7_answer_is_no_of_fintype_odd_cover` (fixed-point input is discharged automatically from a `Fact (Odd (Fintype.card E))` instance).

## Build and Verification
```bash
source "$HOME/.elan/env"
mkdir -p .lake
ln -snf /root/CJ/QuantumStatistics/.lake/packages .lake/packages
lake build
rg -n "\baxiom\b|\bsorry\b|\badmit\b" Question7.lean Question7/*.lean
cat > /tmp/q7_axioms.lean <<'EOF'
import Question7
#print axioms Question7.question7_main_paper_form_of_fixed_point_theorem
#print axioms Question7.question7_main_paper_form
#print axioms Question7.question7_main_paper_form_odd
#print axioms Question7.question7_main_paper_form_contradiction_of_fixed_point_theorem
EOF
lake env lean /tmp/q7_axioms.lean
```

Acceptance conditions:
1. `lake build` succeeds;
2. no `axiom`/`sorry`/`admit` remains in `Question7.lean` and `Question7/*.lean`;
3. `#print axioms` only reports standard axioms (`propext`, `Classical.choice`, `Quot.sound`);
4. `Question7` is wired into `default_target` in `lakefile.lean` (not a zero-job build).
