import Question8.Core

set_option autoImplicit false

/-!
External smooth obstruction input for Question 8.

The core development in `Question8.Core` is axiom-free with respect to symplectic
non-existence statements; this file records how the final answer is obtained from
the cited Gromov-type obstruction as an explicit hypothesis parameter.
-/

theorem no_compact_lagrangian_sphere_in_R4_from_citation :
    (hNoSphere : NoCompactLagrangianSphereInR4) → NoCompactLagrangianSphereInR4 := by
  intro hNoSphere
  exact hNoSphere

theorem octahedron_no_smoothing_from_citation :
    (hNoSphere : NoCompactLagrangianSphereInR4) → ¬ HasLagrangianSmoothing octahedronPoly := by
  intro hNoSphere
  exact octahedron_no_smoothing_from_obstruction hNoSphere

theorem Question8_Answer_strong_from_citation :
    (hNoSphere : NoCompactLagrangianSphereInR4) →
    ∃ K : PolyhedralLagrangian,
      K.faceLagrangianWrtOmegaStd ∧ FourFacesMeeting K ∧ ¬ HasLagrangianSmoothing K := by
  intro hNoSphere
  exact Question8_Answer_strong_from_obstruction hNoSphere

/-- Final negative answer to Question 8, conditional on the cited Gromov obstruction. -/
theorem Question8_Answer_from_citation :
    (hNoSphere : NoCompactLagrangianSphereInR4) →
    ∃ K : PolyhedralLagrangian, FourFacesMeeting K ∧ ¬ HasLagrangianSmoothing K := by
  intro hNoSphere
  exact Question8_Answer_from_obstruction hNoSphere

theorem not_all_four_faces_are_smoothable_from_citation :
    (hNoSphere : NoCompactLagrangianSphereInR4) →
    ¬ (∀ K : PolyhedralLagrangian, FourFacesMeeting K → HasLagrangianSmoothing K) := by
  intro hNoSphere
  exact not_all_four_faces_are_smoothable_from_obstruction hNoSphere

theorem Question8_negative_universal_from_citation :
    (hNoSphere : NoCompactLagrangianSphereInR4) →
    ¬ (∀ K : PolyhedralLagrangian,
      K.faceLagrangianWrtOmegaStd → FourFacesMeeting K → HasLagrangianSmoothing K) := by
  intro hNoSphere
  exact Question8_negative_universal_from_obstruction hNoSphere

/-- Backward-compatible theorem name with explicit cited-obstruction parameter. -/
theorem octahedron_no_smoothing :
    (hNoSphere : NoCompactLagrangianSphereInR4) →
    ¬ HasLagrangianSmoothing octahedronPoly :=
  octahedron_no_smoothing_from_citation

/-- Backward-compatible theorem name with explicit cited-obstruction parameter. -/
theorem Question8_Answer_strong :
    (hNoSphere : NoCompactLagrangianSphereInR4) →
    ∃ K : PolyhedralLagrangian,
      K.faceLagrangianWrtOmegaStd ∧ FourFacesMeeting K ∧ ¬ HasLagrangianSmoothing K :=
  Question8_Answer_strong_from_citation

/-- Backward-compatible theorem name with explicit cited-obstruction parameter. -/
theorem Question8_Answer :
    (hNoSphere : NoCompactLagrangianSphereInR4) →
    ∃ K : PolyhedralLagrangian, FourFacesMeeting K ∧ ¬ HasLagrangianSmoothing K :=
  Question8_Answer_from_citation

/-- Backward-compatible theorem name with explicit cited-obstruction parameter. -/
theorem Question8_negative_universal :
    (hNoSphere : NoCompactLagrangianSphereInR4) →
    ¬ (∀ K : PolyhedralLagrangian,
      K.faceLagrangianWrtOmegaStd → FourFacesMeeting K → HasLagrangianSmoothing K) :=
  Question8_negative_universal_from_citation
