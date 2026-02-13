import Lake
open Lake DSL

package generalizedEuler where
  moreLinkArgs := #["-L/.lake/packages/mathlib/.lake/build/lib",
                    "-L/.lake/packages/mathlib/.lake/build/lib/lean"]

require mathlib from git
  "https://github.com/leanprover-community/mathlib4" @ "v4.15.0"

@[default_target]
lean_lib Question9 where
  roots := #[`Question9.Defs, `Question9.Geometry, `Question9.Generic,
    `Question9.Plucker, `Question9.PolynomialMap, `Question9.Characterization,
    `Question9.ScaledQ, `Question9.Bridge, `Question9.FamilyWitness,
    `Question9.BilinearWitness, `Question9.Counterexample, `Question9.Main,
    `Question9.HFamily, `Question9.PureInputFamily,
    `Question9.NormalizedInputFamily, `Question9.NormalizedPolynomialFamily]
