# Lean4 Formalization Notes for Question 9 (English)

## 1. Goal and Formal Model
This project formalizes `question-9.tex`, which asks for a polynomial map \(\mathbf F\) that detects when the scaling tensor \(\lambda\) is separable (rank-1 outer-product form).
Main layers:
- `Question9/Defs.lean`: indices, `Lambda`, `valid`, `nonzeroOnValid`, `separable`.
- `Question9/Geometry.lean`: concrete `QInput` from camera matrices.
- `Question9/Plucker.lean`: Pl\"ucker relations and reusable pattern machinery.
- `Question9/PolynomialMap.lean` + `Question9/Characterization.lean`: quartic coordinate map and exact equivalence `FZero ↔ separable`.

## 2. Verified Core Results
1. **Abstract equivalence**: `Characterization.fzero_iff_separable`
   \[
   FZero(S,\lambda) \iff \lambda\ \text{is separable}.
   \]
2. **Connection to scaled tensors**: `Main.concrete_q_characterization_of_genericStrong`
   transfers the statement to inputs of the form \(Y=\lambda\cdot Q(A)\) under `IsGenericStrong A`.
3. **Forward Pl\"ucker vanishing**: theorems `concrete_plucker_forward_of_separable*` prove
   `separable lam → pluckerMap(...)=0`.
4. **Conditional reverse pipeline**: `exists_reverse_solution_of_bridgeRecoverability` and
   `exists_reverse_solution_of_bridgeExtractors` show reverse implication once bridge-recovery assumptions are available.

## 3. New in this round: quadratic `HFamily`
Added `Question9/HFamily.lean` with an explicit finite quadratic residual family:
- `HConditionIndex`: finite index type for the three bilinear families (`h1/h2/h3`),
- `hConditionResidualFin`: explicit finite coordinate map (uniform degree `2`),
- `hConditionResidualFin_zero_iff_separable`: for `nonzeroOnValid`,
  \[
  (\forall t,\ F(\lambda)_t=0)\iff \lambda\ \text{is separable},
  \]
- `concrete_hConditionResidualFin_characterization_of_genericStrong`: concrete connection to
  \(Y=\lambda\cdot Q(A)\) via `extractLambdaFromInput`.

## 4. New: pure-input layer `PureInputFamily`
Added `Question9/PureInputFamily.lean` to organize a **pure `InputVector`** route (no `extractLambdaFromInput`):
- introduces `SwapZeroForwardCompleteness` (a forward-completeness assumption),
- proves an `iff` theorem for the fixed pure map `swapZeroMapFin` under
  `BridgeRecoverability + SwapZeroForwardCompleteness`,
- packages the corresponding existence statement:
  `exists_question_solution_of_swapZeroMapFin_under_assumptions`.

This provides a concrete upgrade path on the `Y`-space side while keeping assumptions explicit.

## 5. New in this round: `n=5` forward-completeness counterexample
Added to `Question9/Counterexample.lean`:
- `sepLam5_separable` (an explicit separable tensor),
- `swapZeroMapFin_counterexample_on_sepLam5` (under `IsGenericStrong A`, this separable tensor does **not** force all `swapZeroMapFin` coordinates to vanish),
- `not_swapZeroForwardCompleteness5_of_genericStrong_exists`.

So the forward assumption in `PureInputFamily` is not generally valid on `n=5` (under the same generic-camera existence premise).

## 6. New: corrected working candidate `NormalizedInputFamily`
Added `Question9/NormalizedInputFamily.lean` with
`cameraNormalizedHMapFin`:
- input is still `Y : InputVector n`, with fixed camera `A`,
- internally composes `extractLambdaFromInput (QInput A) Y` with the quadratic `HFamily`,
- proves `cameraNormalizedHMapFin_scaled_iff_separable_of_genericStrong`:
  for `Y = scaleInput lam (QInput A)`, under `IsGenericStrong A` and `nonzeroOnValid lam`,
  \[
  (\forall t,\ \text{cameraNormalizedHMapFin}(A,Y)_t=0)\iff \text{separable}(\lambda).
  \]
- packages existence in `exists_cameraNormalizedHMapFin_solution`.

This gives a working replacement path without the swap-family gaps, though it is still camera-fixed (not yet fully A-independent).

## 7. New: polynomialized version without divisions `NormalizedPolynomialFamily`
Added `Question9/NormalizedPolynomialFamily.lean`, which cross-multiplies the normalization coordinates to remove division:
- `cameraNormalizedHPolyFin`: explicit coordinates using only `Y` and `QInput A` via `+/-/*` (no `/`), with uniform total degree `4`,
- `cameraNormalizedHPolyFin_scaled_iff_separable_of_genericStrong`: for `Y = scaleInput lam (QInput A)`, under `IsGenericStrong A` and `nonzeroOnValid lam`, gives an unconditional `↔`,
- `exists_cameraNormalizedHPolyFin_solution`: existence packaging.

This upgrades the camera-fixed working route from a rational form to an explicit polynomial form (still A-dependent, but division-free).

## 8. Counterexample Boundary (new)
`Question9/Counterexample.lean` constructs an explicit `n=5` sign-valued tensor:
- `counterLam5Real_satisfies_swapBalances` (all six swap-balance families hold),
- `counterLam5Real_not_bridge` and `counterLam5Real_not_separable` (yet not bridge-consistent, hence not separable),
- `not_bridgeRecoverability5_of_genericStrong_exists`,
- `not_bridgeExtractors5_of_genericStrong_exists`,
- `not_permutedHExtractors5_of_genericStrong_exists`.

Therefore, the current six swap-zero families are insufficient for a full reverse characterization.

## 9. Current Status vs. the Original Question
- The Lean development is fully checked (no `sorry/admit/axiom`, `lake build` passes).
- We now have:
  - a complete formal abstract characterization framework (quartic `FMap` plus quadratic `HFamily`),
  - a pure-input `swapZeroMapFin` iff-upgrade framework under explicit assumptions,
  - a working corrected family `cameraNormalizedHMapFin` with no bridge/forward gap (camera-fixed),
  - and a division-free polynomialized variant `cameraNormalizedHPolyFin` (still camera-fixed, same `↔` outcome),
  - two formal obstructions on `n=5` (under generic-camera existence): `BridgeRecoverability` fails and `SwapZeroForwardCompleteness` fails.
- To reach full 100% semantics of the original question, one must introduce a strictly stronger polynomial family (or extra geometric constraints) and prove an unconditional reverse implication.

## 10. Validation
```bash
source "$HOME/.elan/env"
lake build
rg -n "sorry|admit|axiom" Question9
```
