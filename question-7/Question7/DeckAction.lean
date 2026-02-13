import Question7.Defs

set_option autoImplicit false

universe v w

namespace Question7

variable {E : Type v} {X : Type w}
variable [TopologicalSpace E] [TopologicalSpace X]
variable {p : E → X}

/--
If a deck transformation fixes one point, it is globally the identity.
This uses `IsCoveringMap.eq_of_comp_eq`.
-/
theorem deckTransformation_eq_refl_homeomorph_of_fixed_point
    (hp : IsCoveringMap p) [PreconnectedSpace E]
    (g : DeckTransformation p) {x : E} (hx : g x = x) :
    g.toHomeomorph = Homeomorph.refl E := by
  have hfun : (g.toHomeomorph : E → E) = id :=
    hp.eq_of_comp_eq g.toHomeomorph.continuous continuous_id g.comm x (by simpa using hx)
  ext y
  exact congrArg (fun f : E → E => f y) hfun

theorem deckTransformation_eq_refl_homeomorph_of_fixed_point_of_connected
    (hp : IsCoveringMap p) [ConnectedSpace E]
    (g : DeckTransformation p) {x : E} (hx : g x = x) :
    g.toHomeomorph = Homeomorph.refl E := by
  letI : PreconnectedSpace E := inferInstance
  exact deckTransformation_eq_refl_homeomorph_of_fixed_point hp g hx

theorem deckTransformation_eq_refl_of_fixed_point
    (hp : IsCoveringMap p) [PreconnectedSpace E]
    (g : DeckTransformation p) {x : E} (hx : g x = x) :
    g = DeckTransformation.refl p := by
  apply DeckTransformation.ext
  exact deckTransformation_eq_refl_homeomorph_of_fixed_point hp g hx

theorem deckTransformation_eq_refl_of_fixed_point_of_connected
    (hp : IsCoveringMap p) [ConnectedSpace E]
    (g : DeckTransformation p) {x : E} (hx : g x = x) :
    g = DeckTransformation.refl p := by
  apply DeckTransformation.ext
  exact deckTransformation_eq_refl_homeomorph_of_fixed_point_of_connected hp g hx

end Question7
