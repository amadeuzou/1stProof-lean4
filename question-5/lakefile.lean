import Lake
open Lake DSL

package generalizedEuler where
  moreLinkArgs := #["-L/.lake/packages/mathlib/.lake/build/lib",
                    "-L/.lake/packages/mathlib/.lake/build/lib/lean"]

require mathlib from git
  "https://github.com/leanprover-community/mathlib4" @ "v4.26.0"

@[default_target]
lean_lib Question5 where
  roots := #[`Question5, `Equivariant]
