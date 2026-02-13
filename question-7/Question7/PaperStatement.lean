import Question7.GeometryModel
import Question7.LatticeModel
import Question7.LefschetzBridge

set_option autoImplicit false

universe u v w z

namespace Question7

/--
Question 7 in a paper-facing modular form:
under the geometric realization assumptions and the Lefschetz/Smith bridge,
`Γ` cannot contain `2`-torsion.
-/
theorem question7_no_for_uniform_lattice_manifold_model_of_fixed_point_theorem
    {Γ : Type u} {E : Type v} {M : Type w} {H : Type z}
    [Group Γ] [TopologicalSpace Γ]
    [TopologicalSpace E] [TopologicalSpace M]
    [Group H] [TopologicalSpace H]
    [IsRealSemisimpleGroup H] [IsUniformLatticeIn Γ H]
    [RationalAcyclicSpace E]
    (hGeom : UniversalCoverRealization Γ E M)
    (hFixed : HasInvolutiveHomeomorphFixedPointProperty E) :
    ¬ HasTwoTorsion Γ := by
  letI : SimplyConnectedSpace E := hGeom.simplyConnectedCover
  letI : PreconnectedSpace E := inferInstance
  exact question7_answer_is_no hGeom.realization hFixed

/--
Question 7 in a paper-facing modular form:
under the geometric realization assumptions and the Lefschetz/Smith bridge,
`Γ` cannot contain `2`-torsion.
-/
theorem question7_no_for_uniform_lattice_manifold_model
    {Γ : Type u} {E : Type v} {M : Type w} {H : Type z}
    [Group Γ] [TopologicalSpace Γ]
    [TopologicalSpace E] [TopologicalSpace M]
    [Group H] [TopologicalSpace H]
    [IsRealSemisimpleGroup H] [IsUniformLatticeIn Γ H]
    [RationalAcyclicSpace E] [LefschetzInvolutionFixedPointBridge E]
    (hGeom : UniversalCoverRealization Γ E M) :
    ¬ HasTwoTorsion Γ := by
  exact question7_no_for_uniform_lattice_manifold_model_of_fixed_point_theorem
    (Γ := Γ) (E := E) (M := M) (H := H) hGeom
    (hasInvolutiveFixedPointProperty_of_lefschetz E)

theorem question7_answer_to_original_question
    {Γ : Type u} {E : Type v} {M : Type w} {H : Type z}
    [Group Γ] [TopologicalSpace Γ]
    [TopologicalSpace E] [TopologicalSpace M]
    [Group H] [TopologicalSpace H]
    [IsRealSemisimpleGroup H] [IsUniformLatticeIn Γ H]
    [RationalAcyclicSpace E] [LefschetzInvolutionFixedPointBridge E]
    (hGeom : UniversalCoverRealization Γ E M) :
    HasTwoTorsion Γ → False := by
  intro hTorsion
  exact (question7_no_for_uniform_lattice_manifold_model
    (Γ := Γ) (E := E) (M := M) (H := H) hGeom) hTorsion

theorem question7_no_for_uniform_lattice_manifold_model_of_rationalAcyclic_fintype_odd
    {Γ : Type u} {E : Type v} {M : Type w} {H : Type z}
    [Group Γ] [TopologicalSpace Γ]
    [TopologicalSpace E] [TopologicalSpace M]
    [Group H] [TopologicalSpace H]
    [IsRealSemisimpleGroup H] [IsUniformLatticeIn Γ H]
    [RationalAcyclicSpace E] [Fintype E] [DecidableEq E] [Fact (Odd (Fintype.card E))]
    (hGeom : UniversalCoverRealization Γ E M) :
    ¬ HasTwoTorsion Γ :=
  question7_no_for_uniform_lattice_manifold_model
    (Γ := Γ) (E := E) (M := M) (H := H) hGeom

end Question7
