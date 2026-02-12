import Lake
open Lake DSL

package generalizedEuler where
  moreLinkArgs := #["-L/.lake/packages/mathlib/.lake/build/lib",
                    "-L/.lake/packages/mathlib/.lake/build/lib/lean"]

require mathlib from git
  "https://github.com/leanprover-community/mathlib4" @ "v4.15.0"

@[default_target]
lean_lib Question10 where
  roots := #[`Question10.Defs, `Question10.SparseMatVec, `Question10.PCG,
    `Question10.Complexity, `Question10.Main]
