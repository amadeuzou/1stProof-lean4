import Lake
open Lake DSL

package generalizedEuler where
  moreLinkArgs := #["-L/.lake/packages/mathlib/.lake/build/lib",
                    "-L/.lake/packages/mathlib/.lake/build/lib/lean"]

require mathlib from git
  "https://github.com/leanprover-community/mathlib4" @ "v4.15.0"

@[default_target]
lean_lib generalizedEuler where
  roots := #[`Question8]
