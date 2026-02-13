import Question7.HomologyQAcyclic

set_option autoImplicit false

universe u

namespace Question7

/--
Bridge interface for the topological heavy step:
derive involutive fixed points from the `ℚ`-acyclic package (e.g. via
Lefschetz/Smith theory).
-/
class LefschetzInvolutionFixedPointBridge (E : Type u)
    [TopologicalSpace E] [RationalAcyclicSpace E] : Prop where
  hasFixedPoint : HasInvolutiveHomeomorphFixedPointProperty E

instance (E : Type u) [TopologicalSpace E] [RationalAcyclicSpace E]
    [LefschetzInvolutionFixedPointBridge E] :
    QAcyclicInvolutionFixedPointBridge E where
  hasFixedPoint := LefschetzInvolutionFixedPointBridge.hasFixedPoint (E := E)

theorem hasInvolutiveFixedPointProperty_of_lefschetz
    (E : Type u) [TopologicalSpace E] [RationalAcyclicSpace E]
    [LefschetzInvolutionFixedPointBridge E] :
    HasInvolutiveHomeomorphFixedPointProperty E :=
  LefschetzInvolutionFixedPointBridge.hasFixedPoint (E := E)

instance (E : Type u) [TopologicalSpace E] [RationalAcyclicSpace E]
    [Fintype E] [DecidableEq E] [Fact (Odd (Fintype.card E))] :
    LefschetzInvolutionFixedPointBridge E where
  hasFixedPoint :=
    RationalAcyclicSpace.oddFinite_involution_has_fixedPoint (E := E) (Fact.out)

end Question7
