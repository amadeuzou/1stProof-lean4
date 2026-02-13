# Question 3 Lean4 Formalization Notes (English)

## 1. What this version changes
This version moves from abstract assumptions to explicit formulas:

- Parameters: `x : Fin n → ℝ`, `t : ℝ`
- Exchange ratio:
  \[
  \text{ratio}(i)=\frac{t x_i - x_{i+1}}{x_i - t x_{i+1}}
  \]
- Local rates:
  \[
  \text{ratePlus}=t x_i - x_{i+1},\quad
  \text{rateMinus}=x_i - t x_{i+1}
  \]
- Dynamics: adjacent swaps on words `WordState Species n` via `swapAt`

So transition rules are local and parameter-driven, not defined by evaluating full polynomials.

## 2. Core definitions in `Question3.lean`
- `AdjIndex`, `leftIndex`, `rightIndex`
- `swapAt`
- `ratePlus`, `rateMinus`, `ratio`
- `localRate`
- `WeightExchange`:
  \[
  \text{weight}(\text{swapAt }w\,a)=\text{ratio}(a)\cdot \text{weight}(w)
  \]

## 3. Proof pipeline
- `ratio_mul_rateMinus`: proves the explicit algebraic identity
  \[
  \text{ratio}\cdot\text{rateMinus}=\text{ratePlus}.
  \]
- `local_detailed_of_gt`: detailed balance on one local edge from explicit formulas.
- `local_detailed`: handles all three order cases (`>`, `=`, `<`).
- `detailed_balance_explicit`: lifts edge-wise detailed balance to the full kernel.
- `stationary_global_balance_explicit`: derives global balance / stationarity.
- `nontrivial_local`: gives a nontriviality witness under inversion + positivity assumptions.

## 4. Semantic link to \(F^*/P^*\)
- `ASEPWeightModel`: models interpolation-polynomial weights as proportional to ASEP weights.
- `global_balance_of_scaled_model`: stationarity is preserved under nonzero scaling.
- `global_balance_normalized`: for any constant `Pstar`, `weight / Pstar` still satisfies global balance.
- `FstarAtQ1ByDefinition` and `PiFromFstarPstar`: explicit code-level objects for \(F^*\) and \(F^*/P^*\).
- `FstarWeightExchangeQ1` and `fstar_weight_exchange_q1`: explicit literature-bridge interface for the \(q=1\) exchange property of the real \(F^*\)-weights.
- `question3_stationary_definitional`: final packaged theorem in the “define \(F^*\) via ASEP weight” regime.
- `question3_stationary_via_fstar_bridge`: stationarity theorem driven directly by the bridge interface.
- `question3_full_via_fstar_bridge`: one-shot theorem combining stationarity and nontriviality through the bridge (recommended entry point).

## 5. New: `S_n(\lambda)` and paper-level wrappers

- `Macdonald/Bridge/SnLambda.lean`
  - Defines `SnLambdaState` (permutation-orbit subtype).
  - Provides `stationary/nontrivial/full` theorems on this restricted state space.
  - Includes a restricted-input entry theorem:
    `exists_explicit_chain_on_SnLambda_of_restricted`.

- `Macdonald/Bridge/FstarSnLambda.lean`
  - Lifts `FstarSpecializedData` automatically to `S_n(\lambda)`.
  - Adds `FstarSnLambdaData` with `question3_full` on the restricted space.

- `Macdonald/Bridge/FstarRestricted.lean`
  - Introduces `FstarCandidateOnRestricted`, a program-style paper interface.
  - Exposes `question3_full/stationary/nontrivial` in one package.
  - Includes an `n=2` canonical route without an external exchange hypothesis.

- `Macdonald/Bridge/PaperTheorem.lean`
  - Adds paper-style theorem wrappers:
    `paper_main_restricted_qOne` and
    `paper_main_restricted_qOne_explicit_formula`.

## 6. New: complete restricted theorem (no external exchange input)

- `Macdonald/Bridge/SnLambda.lean`
  - `complete_chain_on_SnLambda_of_restricted` now gives a fully explicit canonical construction
    under `hn : 2 ≤ n` and `IsRestrictedWord lam`:
    `x_i = -i`, `t = 1`, `F^* = 1`, `P^* = |S_n(λ)|`.
  - It simultaneously proves:
    1) stationarity,
    2) nonnegative transition rates (Markov semantics),
    3) `pi ≥ 0` and `∑ pi = 1` (probability distribution),
    4) nontriviality.

- `Macdonald/Bridge/PaperTheorem.lean`
  - `paper_main_restricted_qOne_complete` is now a one-shot paper-style theorem:
    there exist explicit `x,t,F^*,P^*,pi` such that
    `pi = F^*/P^*`, stationarity holds, the chain is nontrivial,
    and transitions are local/polynomial-free.
  - `paper_main_restricted_qOne_final` fixes and names the repository-level
    final `q=1` objects
    `paperFstar_restricted_qOne / paperPstar_restricted_qOne / paperPi_restricted_qOne`
    and provides the full package directly (stationarity, nonnegativity,
    normalization, nontriviality, and the ratio formula).

- `Macdonald/Bridge/FinalTheorem.lean`
  - Introduces semantic wrappers `ContinuousTimeMarkovChain` and `IsStationaryDist`.
  - `question3_complete_restricted_qOne` packages the result as a semantic
    existence theorem: a Markov chain exists on `S_n(λ)`, with `pi = F^*/P^*`,
    plus stationarity, nonnegativity, normalization, nontriviality, and locality.
  - Adds the discrete-time probability-kernel construction:
    `paperDiscreteKernel` and `question3_complete_restricted_qOne_discrete`,
    proving row-sum-1 transitions, stationarity of `pi = F^*/P^*`,
    and existence of a positive off-diagonal transition (nontriviality).

- `Macdonald/Bridge/LiteratureCompletion.lean`
  - Adds the literature-facing closure theorem
    `paper_main_restricted_qOne_discrete_of_literature_assumptions`:
    given `FstarCandidateOnRestricted` plus verifiable assumptions
    (nonnegative `ratePlus/rateMinus`, nonnegative normalized `pi`),
    it yields a discrete-time Markov chain with stationary `pi = F^*/P^*`
    and a positive off-diagonal transition.
  - This isolates the remaining gap to proving these assumptions for the
    external interpolation-polynomial objects themselves.

## 7. Verification
- `lake build`: passed (`1516 jobs`)
- Whole project: no `sorry`, no custom `axiom`
