import Question7.Defs

set_option autoImplicit false

universe u

namespace Question7

/--
Homology-facing package for "`E` is `ℚ`-acyclic".
The current fields are intentionally lightweight but are named to match the
intended future singular-homology formalization.
-/
class RationalAcyclicSpace (E : Type u) [TopologicalSpace E] : Prop where
  connected : ConnectedSpace E
  oddFinite_involution_has_fixedPoint :
    ∀ [Fintype E] [DecidableEq E], Odd (Fintype.card E) →
      HasInvolutiveHomeomorphFixedPointProperty E

instance (E : Type u) [TopologicalSpace E] [RationalAcyclicSpace E] : IsQAcyclic E where
  connected := RationalAcyclicSpace.connected (E := E)
  oddFinite_involution_has_fixedPoint :=
    RationalAcyclicSpace.oddFinite_involution_has_fixedPoint (E := E)

theorem fixedPointInput_of_rationalAcyclic_oddFinite
    (E : Type u) [TopologicalSpace E] [RationalAcyclicSpace E]
    [Fintype E] [DecidableEq E] (hodd : Odd (Fintype.card E)) :
    HasInvolutiveHomeomorphFixedPointProperty E :=
  RationalAcyclicSpace.oddFinite_involution_has_fixedPoint (E := E) hodd

end Question7
