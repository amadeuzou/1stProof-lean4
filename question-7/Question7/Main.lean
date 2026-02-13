import Question7.DeckAction
import Question7.SmithTheory
import Mathlib.AlgebraicTopology.FundamentalGroupoid.SimplyConnected

set_option autoImplicit false

universe u v w

namespace Question7

/--
Data package encoding the realization of `Γ` via covering transformations on `E`.
This avoids introducing additional global axioms and keeps all assumptions explicit.
-/
structure RealizationData (Γ : Type u) (E : Type v) (X : Type w)
    [Group Γ] [TopologicalSpace E] [TopologicalSpace X] where
  p : E → X
  isCoveringMap : IsCoveringMap p
  deckLift : Γ →* DeckTransformation p
  deckLift_injective : Function.Injective deckLift

namespace RealizationData

variable {Γ : Type u} {E : Type v} {X : Type w}
variable [Group Γ] [TopologicalSpace E] [TopologicalSpace X]

def HasOrderTwoDeckFixedPointProperty (hData : RealizationData Γ E X) : Prop :=
  ∀ γ : Γ, orderOf γ = 2 → ∃ x : E, hData.deckLift γ x = x

theorem deckLift_sq_eq_one (hData : RealizationData Γ E X) {γ : Γ}
    (hγsq : γ * γ = (1 : Γ)) :
    hData.deckLift γ * hData.deckLift γ = (1 : DeckTransformation hData.p) := by
  calc
    hData.deckLift γ * hData.deckLift γ = hData.deckLift (γ * γ) := by
      exact (hData.deckLift.map_mul γ γ).symm
    _ = hData.deckLift (1 : Γ) := by rw [hγsq]
    _ = (1 : DeckTransformation hData.p) := by simp

theorem deckLift_involutive_of_order_two (hData : RealizationData Γ E X) {γ : Γ}
    (hOrderγ : orderOf γ = 2) :
    Function.Involutive (hData.deckLift γ) := by
  have hγsq : γ * γ = (1 : Γ) := by
    have hpow : γ ^ 2 = (1 : Γ) := by
      simpa [hOrderγ] using (pow_orderOf_eq_one γ)
    simpa [pow_two] using hpow
  have hDeckSq : hData.deckLift γ * hData.deckLift γ = (1 : DeckTransformation hData.p) :=
    hData.deckLift_sq_eq_one hγsq
  intro x
  have hAtX : (hData.deckLift γ * hData.deckLift γ) x = (1 : DeckTransformation hData.p) x :=
    congrArg (fun g : DeckTransformation hData.p => g x) hDeckSq
  simpa using hAtX

theorem hasOrderTwoDeckFixedPointProperty_of_homeomorph_fixedPointProperty
    (hData : RealizationData Γ E X)
    (hFixed : HasInvolutiveHomeomorphFixedPointProperty E) :
    hData.HasOrderTwoDeckFixedPointProperty := by
  intro γ hOrderγ
  have hInv : Function.Involutive (hData.deckLift γ) :=
    hData.deckLift_involutive_of_order_two hOrderγ
  exact fixed_point_of_involutive_homeomorph hFixed (hData.deckLift γ).toHomeomorph hInv

theorem hasOrderTwoDeckFixedPointProperty_of_fintype_odd
    (hData : RealizationData Γ E X)
    [Fintype E] [DecidableEq E] (hodd : Odd (Fintype.card E)) :
    hData.HasOrderTwoDeckFixedPointProperty := by
  intro γ hOrderγ
  have hInv : Function.Involutive (hData.deckLift γ) :=
    hData.deckLift_involutive_of_order_two hOrderγ
  exact fixed_point_of_involutive_homeomorph_of_fintype_odd
    (hData.deckLift γ).toHomeomorph hInv hodd

end RealizationData

theorem no_two_torsion_of_realization
    {Γ : Type u} {E : Type v} {X : Type w}
    [Group Γ] [TopologicalSpace E] [TopologicalSpace X] [PreconnectedSpace E]
    (hData : RealizationData Γ E X)
    (hDeckFixed : hData.HasOrderTwoDeckFixedPointProperty) :
    ¬ HasTwoTorsion Γ := by
  intro hTorsion
  rcases hTorsion with ⟨γ, hOrderγ⟩
  obtain ⟨x, hx⟩ := hDeckFixed γ hOrderγ
  have hDeckRefl : (hData.deckLift γ).toHomeomorph = Homeomorph.refl E :=
    deckTransformation_eq_refl_homeomorph_of_fixed_point hData.isCoveringMap (hData.deckLift γ) hx
  have hDeckOne : hData.deckLift γ = (1 : DeckTransformation hData.p) := by
    apply DeckTransformation.ext
    simpa using hDeckRefl
  have hγone : γ = 1 := hData.deckLift_injective (by simpa using hDeckOne)
  have hOrderOne : orderOf (1 : Γ) = 2 := by
    calc
      orderOf (1 : Γ) = orderOf γ := by rw [hγone]
      _ = 2 := hOrderγ
  have hImpossible : (1 : ℕ) = 2 := by
    calc
      (1 : ℕ) = orderOf (1 : Γ) := by symm; exact orderOf_one
      _ = 2 := hOrderOne
  exact (by decide : (1 : ℕ) ≠ 2) hImpossible

theorem no_two_torsion_of_realization_of_connected
    {Γ : Type u} {E : Type v} {X : Type w}
    [Group Γ] [TopologicalSpace E] [TopologicalSpace X] [ConnectedSpace E]
    (hData : RealizationData Γ E X)
    (hDeckFixed : hData.HasOrderTwoDeckFixedPointProperty) :
    ¬ HasTwoTorsion Γ := by
  letI : PreconnectedSpace E := inferInstance
  exact no_two_torsion_of_realization hData hDeckFixed

theorem question7_answer_is_no
    {Γ : Type u} {E : Type v} {X : Type w}
    [Group Γ] [TopologicalSpace E] [TopologicalSpace X] [PreconnectedSpace E]
    (hData : RealizationData Γ E X)
    (hFixed : HasInvolutiveHomeomorphFixedPointProperty E) :
    ¬ HasTwoTorsion Γ :=
  no_two_torsion_of_realization hData
    (hData.hasOrderTwoDeckFixedPointProperty_of_homeomorph_fixedPointProperty hFixed)

theorem question7_answer_is_no_of_connected
    {Γ : Type u} {E : Type v} {X : Type w}
    [Group Γ] [TopologicalSpace E] [TopologicalSpace X] [ConnectedSpace E]
    (hData : RealizationData Γ E X)
    (hFixed : HasInvolutiveHomeomorphFixedPointProperty E) :
    ¬ HasTwoTorsion Γ :=
  no_two_torsion_of_realization_of_connected hData
    (hData.hasOrderTwoDeckFixedPointProperty_of_homeomorph_fixedPointProperty hFixed)

theorem question7_answer_is_no_of_input
    {Γ : Type u} {E : Type v} {X : Type w}
    [Group Γ] [TopologicalSpace E] [TopologicalSpace X] [PreconnectedSpace E]
    [InvolutionFixedPointInput E]
    (hData : RealizationData Γ E X) :
    ¬ HasTwoTorsion Γ :=
  question7_answer_is_no hData (InvolutionFixedPointInput.hasFixedPoint (E := E))

theorem question7_answer_is_no_of_input_of_connected
    {Γ : Type u} {E : Type v} {X : Type w}
    [Group Γ] [TopologicalSpace E] [TopologicalSpace X] [ConnectedSpace E]
    [InvolutionFixedPointInput E]
    (hData : RealizationData Γ E X) :
    ¬ HasTwoTorsion Γ := by
  letI : PreconnectedSpace E := inferInstance
  exact question7_answer_is_no_of_input hData

theorem question7_answer_is_no_of_input_of_simplyConnected
    {Γ : Type u} {E : Type v} {X : Type w}
    [Group Γ] [TopologicalSpace E] [TopologicalSpace X] [SimplyConnectedSpace E]
    [InvolutionFixedPointInput E]
    (hData : RealizationData Γ E X) :
    ¬ HasTwoTorsion Γ := by
  letI : ConnectedSpace E := inferInstance
  exact question7_answer_is_no_of_input_of_connected hData

theorem question7_answer_is_no_of_qacyclic_bridge
    {Γ : Type u} {E : Type v} {X : Type w}
    [Group Γ] [TopologicalSpace E] [TopologicalSpace X]
    [IsQAcyclic E] [QAcyclicInvolutionFixedPointBridge E]
    (hData : RealizationData Γ E X) :
    ¬ HasTwoTorsion Γ :=
  question7_answer_is_no_of_input_of_connected hData

theorem question7_answer_is_no_of_qacyclic_bridge_of_simplyConnected
    {Γ : Type u} {E : Type v} {X : Type w}
    [Group Γ] [TopologicalSpace E] [TopologicalSpace X] [SimplyConnectedSpace E]
    [IsQAcyclic E] [QAcyclicInvolutionFixedPointBridge E]
    (hData : RealizationData Γ E X) :
    ¬ HasTwoTorsion Γ :=
  question7_answer_is_no_of_qacyclic_bridge hData

theorem question7_answer_is_no_of_qacyclic_fintype_odd_cover
    {Γ : Type u} {E : Type v} {X : Type w}
    [Group Γ] [TopologicalSpace E] [TopologicalSpace X]
    [IsQAcyclic E] [Fintype E] [DecidableEq E] [Fact (Odd (Fintype.card E))]
    (hData : RealizationData Γ E X) :
    ¬ HasTwoTorsion Γ :=
  question7_answer_is_no_of_qacyclic_bridge hData

theorem question7_answer_is_no_of_subsingleton_cover
    {Γ : Type u} {E : Type v} {X : Type w}
    [Group Γ] [TopologicalSpace E] [TopologicalSpace X]
    [Subsingleton E] [Inhabited E]
    (hData : RealizationData Γ E X) :
    ¬ HasTwoTorsion Γ := by
  letI : ConnectedSpace E := inferInstance
  exact question7_answer_is_no_of_input_of_connected hData

theorem question7_answer_is_no_of_fintype_odd_cover
    {Γ : Type u} {E : Type v} {X : Type w}
    [Group Γ] [TopologicalSpace E] [TopologicalSpace X] [PreconnectedSpace E]
    [Fintype E] [DecidableEq E] [Fact (Odd (Fintype.card E))]
    (hData : RealizationData Γ E X) :
    ¬ HasTwoTorsion Γ :=
  question7_answer_is_no_of_input hData

theorem question7_answer_is_no_of_fintype_odd_cover_of_connected
    {Γ : Type u} {E : Type v} {X : Type w}
    [Group Γ] [TopologicalSpace E] [TopologicalSpace X] [ConnectedSpace E]
    [Fintype E] [DecidableEq E] [Fact (Odd (Fintype.card E))]
    (hData : RealizationData Γ E X) :
    ¬ HasTwoTorsion Γ :=
  question7_answer_is_no_of_input_of_connected hData

theorem question7_answer_is_no_of_fintype_odd_cover_of_simplyConnected
    {Γ : Type u} {E : Type v} {X : Type w}
    [Group Γ] [TopologicalSpace E] [TopologicalSpace X] [SimplyConnectedSpace E]
    [Fintype E] [DecidableEq E] [Fact (Odd (Fintype.card E))]
    (hData : RealizationData Γ E X) :
    ¬ HasTwoTorsion Γ := by
  letI : ConnectedSpace E := inferInstance
  exact question7_answer_is_no_of_fintype_odd_cover_of_connected hData

theorem question7_contradiction_of_realization_and_two_torsion
    {Γ : Type u} {E : Type v} {X : Type w}
    [Group Γ] [TopologicalSpace E] [TopologicalSpace X] [PreconnectedSpace E]
    [InvolutionFixedPointInput E]
    (hData : RealizationData Γ E X) (hTorsion : HasTwoTorsion Γ) : False :=
  (question7_answer_is_no_of_input hData) hTorsion

theorem question7_contradiction_of_realization_and_two_torsion_of_connected
    {Γ : Type u} {E : Type v} {X : Type w}
    [Group Γ] [TopologicalSpace E] [TopologicalSpace X] [ConnectedSpace E]
    [InvolutionFixedPointInput E]
    (hData : RealizationData Γ E X) (hTorsion : HasTwoTorsion Γ) : False :=
  (question7_answer_is_no_of_input_of_connected hData) hTorsion

theorem question7_contradiction_of_realization_and_two_torsion_of_simplyConnected
    {Γ : Type u} {E : Type v} {X : Type w}
    [Group Γ] [TopologicalSpace E] [TopologicalSpace X] [SimplyConnectedSpace E]
    [InvolutionFixedPointInput E]
    (hData : RealizationData Γ E X) (hTorsion : HasTwoTorsion Γ) : False := by
  letI : ConnectedSpace E := inferInstance
  exact question7_contradiction_of_realization_and_two_torsion_of_connected hData hTorsion

theorem no_realizationData_nonempty_of_two_torsion
    {Γ : Type u} {E : Type v} {X : Type w}
    [Group Γ] [TopologicalSpace E] [TopologicalSpace X] [PreconnectedSpace E]
    [InvolutionFixedPointInput E]
    (hTorsion : HasTwoTorsion Γ) :
    ¬ Nonempty (RealizationData Γ E X) := by
  intro hNonempty
  rcases hNonempty with ⟨hData⟩
  exact (question7_answer_is_no_of_input hData) hTorsion

theorem no_realizationData_nonempty_of_two_torsion_of_connected
    {Γ : Type u} {E : Type v} {X : Type w}
    [Group Γ] [TopologicalSpace E] [TopologicalSpace X] [ConnectedSpace E]
    [InvolutionFixedPointInput E]
    (hTorsion : HasTwoTorsion Γ) :
    ¬ Nonempty (RealizationData Γ E X) := by
  intro hNonempty
  rcases hNonempty with ⟨hData⟩
  exact (question7_answer_is_no_of_input_of_connected hData) hTorsion

theorem no_realizationData_nonempty_of_two_torsion_of_simplyConnected
    {Γ : Type u} {E : Type v} {X : Type w}
    [Group Γ] [TopologicalSpace E] [TopologicalSpace X] [SimplyConnectedSpace E]
    [InvolutionFixedPointInput E]
    (hTorsion : HasTwoTorsion Γ) :
    ¬ Nonempty (RealizationData Γ E X) := by
  intro hNonempty
  rcases hNonempty with ⟨hData⟩
  exact (question7_answer_is_no_of_input_of_simplyConnected hData) hTorsion

theorem no_realizationData_nonempty_of_two_torsion_qacyclic_bridge
    {Γ : Type u} {E : Type v} {X : Type w}
    [Group Γ] [TopologicalSpace E] [TopologicalSpace X]
    [IsQAcyclic E] [QAcyclicInvolutionFixedPointBridge E]
    (hTorsion : HasTwoTorsion Γ) :
    ¬ Nonempty (RealizationData Γ E X) := by
  intro hNonempty
  rcases hNonempty with ⟨hData⟩
  exact (question7_answer_is_no_of_qacyclic_bridge hData) hTorsion

theorem no_realizationData_nonempty_of_two_torsion_qacyclic_fintype_odd
    {Γ : Type u} {E : Type v} {X : Type w}
    [Group Γ] [TopologicalSpace E] [TopologicalSpace X]
    [IsQAcyclic E] [Fintype E] [DecidableEq E] [Fact (Odd (Fintype.card E))]
    (hTorsion : HasTwoTorsion Γ) :
    ¬ Nonempty (RealizationData Γ E X) := by
  intro hNonempty
  rcases hNonempty with ⟨hData⟩
  exact (question7_answer_is_no_of_qacyclic_fintype_odd_cover hData) hTorsion

end Question7
