import Lake
open Lake DSL

package generalizedEuler where
  moreLinkArgs := #["-L/.lake/packages/mathlib/.lake/build/lib",
                    "-L/.lake/packages/mathlib/.lake/build/lib/lean"]

require mathlib from git
  "https://github.com/leanprover-community/mathlib4" @ "v4.26.0"

@[default_target]
lean_lib generalizedEuler where
  roots := #[
    `Question3,
    `Macdonald.Conventions,
    `Macdonald.Hecke.Operators,
    `Macdonald.Hecke.DemazureLusztig,
    `Macdonald.Nonsymmetric.E,
    `Macdonald.Bridge.Question3Finite,
    `Macdonald.Bridge.QOneSpecialization,
    `Macdonald.Bridge.Evaluation,
    `Macdonald.Bridge.Specialization,
    `Macdonald.Bridge.Concrete,
    `Macdonald.Bridge.FstarModel,
    `Macdonald.Bridge.FstarSpecialized,
    `Macdonald.Bridge.FstarWorkflow,
    `Macdonald.Bridge.FstarSnLambda,
    `Macdonald.Bridge.FstarRestricted,
    `Macdonald.Bridge.PaperTheorem,
    `Macdonald.Bridge.FinalTheorem,
    `Macdonald.Bridge.LiteratureCompletion,
    `Macdonald.Bridge.TwoSite,
    `Macdonald.Bridge.SnLambda,
    `Macdonald.Bridge.Program
  ]
