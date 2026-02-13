import Question7.PaperStatement
import Mathlib.AlgebraicTopology.FundamentalGroupoid.FundamentalGroup

set_option autoImplicit false

universe u v w z

namespace Question7

/--
Records the exact "Γ is the fundamental group of `M`" hypothesis from the
problem statement.
-/
structure FundamentalGroupRealization (Γ : Type u) (M : Type w)
    [Group Γ] [TopologicalSpace M] where
  basepoint : M
  iso : FundamentalGroup M basepoint ≃* Γ

/--
Bridge-agnostic one-shot package for the original question assumptions.
This keeps geometric realization and `π₁` identification together, while the
fixed-point bridge route is supplied at theorem level.
-/
structure OriginalQuestionInputCore (Γ : Type u) (E : Type v) (M : Type w) (H : Type z)
    [Group Γ] [TopologicalSpace Γ]
    [TopologicalSpace E] [TopologicalSpace M]
    [Group H] [TopologicalSpace H]
    [IsRealSemisimpleGroup H] [IsUniformLatticeIn Γ H]
    [RationalAcyclicSpace E] where
  geom : UniversalCoverRealization Γ E M
  pi1 : FundamentalGroupRealization Γ M

/--
One-shot package for the original question assumptions, keeping geometric
realization and `π₁` identification together.
-/
structure OriginalQuestionInput (Γ : Type u) (E : Type v) (M : Type w) (H : Type z)
    [Group Γ] [TopologicalSpace Γ]
    [TopologicalSpace E] [TopologicalSpace M]
    [Group H] [TopologicalSpace H]
    [IsRealSemisimpleGroup H] [IsUniformLatticeIn Γ H]
    [RationalAcyclicSpace E] [LefschetzInvolutionFixedPointBridge E] where
  geom : UniversalCoverRealization Γ E M
  pi1 : FundamentalGroupRealization Γ M

/--
One-shot package for the original question assumptions in the finite odd-cardinality
regime, where the Lefschetz bridge is inferred automatically.
-/
structure OriginalQuestionInputOdd (Γ : Type u) (E : Type v) (M : Type w) (H : Type z)
    [Group Γ] [TopologicalSpace Γ]
    [TopologicalSpace E] [TopologicalSpace M]
    [Group H] [TopologicalSpace H]
    [IsRealSemisimpleGroup H] [IsUniformLatticeIn Γ H]
    [RationalAcyclicSpace E] [Fintype E] [DecidableEq E] [Fact (Odd (Fintype.card E))] where
  geom : UniversalCoverRealization Γ E M
  pi1 : FundamentalGroupRealization Γ M

def OriginalQuestionInput.toCore
    {Γ : Type u} {E : Type v} {M : Type w} {H : Type z}
    [Group Γ] [TopologicalSpace Γ]
    [TopologicalSpace E] [TopologicalSpace M]
    [Group H] [TopologicalSpace H]
    [IsRealSemisimpleGroup H] [IsUniformLatticeIn Γ H]
    [RationalAcyclicSpace E] [LefschetzInvolutionFixedPointBridge E]
    (hInput : OriginalQuestionInput Γ E M H) :
    OriginalQuestionInputCore Γ E M H where
  geom := hInput.geom
  pi1 := hInput.pi1

@[simp] theorem OriginalQuestionInput.toCore_geom
    {Γ : Type u} {E : Type v} {M : Type w} {H : Type z}
    [Group Γ] [TopologicalSpace Γ]
    [TopologicalSpace E] [TopologicalSpace M]
    [Group H] [TopologicalSpace H]
    [IsRealSemisimpleGroup H] [IsUniformLatticeIn Γ H]
    [RationalAcyclicSpace E] [LefschetzInvolutionFixedPointBridge E]
    (hInput : OriginalQuestionInput Γ E M H) :
    hInput.toCore.geom = hInput.geom := rfl

@[simp] theorem OriginalQuestionInput.toCore_pi1
    {Γ : Type u} {E : Type v} {M : Type w} {H : Type z}
    [Group Γ] [TopologicalSpace Γ]
    [TopologicalSpace E] [TopologicalSpace M]
    [Group H] [TopologicalSpace H]
    [IsRealSemisimpleGroup H] [IsUniformLatticeIn Γ H]
    [RationalAcyclicSpace E] [LefschetzInvolutionFixedPointBridge E]
    (hInput : OriginalQuestionInput Γ E M H) :
    hInput.toCore.pi1 = hInput.pi1 := rfl

def OriginalQuestionInputOdd.toCore
    {Γ : Type u} {E : Type v} {M : Type w} {H : Type z}
    [Group Γ] [TopologicalSpace Γ]
    [TopologicalSpace E] [TopologicalSpace M]
    [Group H] [TopologicalSpace H]
    [IsRealSemisimpleGroup H] [IsUniformLatticeIn Γ H]
    [RationalAcyclicSpace E] [Fintype E] [DecidableEq E] [Fact (Odd (Fintype.card E))]
    (hInput : OriginalQuestionInputOdd Γ E M H) :
    OriginalQuestionInputCore Γ E M H where
  geom := hInput.geom
  pi1 := hInput.pi1

@[simp] theorem OriginalQuestionInputOdd.toCore_geom
    {Γ : Type u} {E : Type v} {M : Type w} {H : Type z}
    [Group Γ] [TopologicalSpace Γ]
    [TopologicalSpace E] [TopologicalSpace M]
    [Group H] [TopologicalSpace H]
    [IsRealSemisimpleGroup H] [IsUniformLatticeIn Γ H]
    [RationalAcyclicSpace E] [Fintype E] [DecidableEq E] [Fact (Odd (Fintype.card E))]
    (hInput : OriginalQuestionInputOdd Γ E M H) :
    hInput.toCore.geom = hInput.geom := rfl

@[simp] theorem OriginalQuestionInputOdd.toCore_pi1
    {Γ : Type u} {E : Type v} {M : Type w} {H : Type z}
    [Group Γ] [TopologicalSpace Γ]
    [TopologicalSpace E] [TopologicalSpace M]
    [Group H] [TopologicalSpace H]
    [IsRealSemisimpleGroup H] [IsUniformLatticeIn Γ H]
    [RationalAcyclicSpace E] [Fintype E] [DecidableEq E] [Fact (Odd (Fintype.card E))]
    (hInput : OriginalQuestionInputOdd Γ E M H) :
    hInput.toCore.pi1 = hInput.pi1 := rfl

/--
Question 7 answer in a formulation that explicitly includes the fundamental
group realization datum.
-/
theorem question7_no_for_uniform_lattice_with_fundamental_group
    {Γ : Type u} {E : Type v} {M : Type w} {H : Type z}
    [Group Γ] [TopologicalSpace Γ]
    [TopologicalSpace E] [TopologicalSpace M]
    [Group H] [TopologicalSpace H]
    [IsRealSemisimpleGroup H] [IsUniformLatticeIn Γ H]
    [RationalAcyclicSpace E] [LefschetzInvolutionFixedPointBridge E]
    (hGeom : UniversalCoverRealization Γ E M)
    (_hPi1 : FundamentalGroupRealization Γ M) :
    ¬ HasTwoTorsion Γ := by
  exact question7_no_for_uniform_lattice_manifold_model
    (Γ := Γ) (E := E) (M := M) (H := H) hGeom

theorem question7_no_for_uniform_lattice_with_fundamental_group_of_rationalAcyclic_fintype_odd
    {Γ : Type u} {E : Type v} {M : Type w} {H : Type z}
    [Group Γ] [TopologicalSpace Γ]
    [TopologicalSpace E] [TopologicalSpace M]
    [Group H] [TopologicalSpace H]
    [IsRealSemisimpleGroup H] [IsUniformLatticeIn Γ H]
    [RationalAcyclicSpace E] [Fintype E] [DecidableEq E] [Fact (Odd (Fintype.card E))]
    (hGeom : UniversalCoverRealization Γ E M)
    (_hPi1 : FundamentalGroupRealization Γ M) :
    ¬ HasTwoTorsion Γ := by
  exact question7_no_for_uniform_lattice_manifold_model_of_rationalAcyclic_fintype_odd
    (Γ := Γ) (E := E) (M := M) (H := H) hGeom

theorem question7_no_of_original_input_core
    {Γ : Type u} {E : Type v} {M : Type w} {H : Type z}
    [Group Γ] [TopologicalSpace Γ]
    [TopologicalSpace E] [TopologicalSpace M]
    [Group H] [TopologicalSpace H]
    [IsRealSemisimpleGroup H] [IsUniformLatticeIn Γ H]
    [RationalAcyclicSpace E] [LefschetzInvolutionFixedPointBridge E]
    (hInput : OriginalQuestionInputCore Γ E M H) :
    ¬ HasTwoTorsion Γ :=
  question7_no_for_uniform_lattice_with_fundamental_group
    (Γ := Γ) (E := E) (M := M) (H := H) hInput.geom hInput.pi1

theorem question7_no_of_original_input
    {Γ : Type u} {E : Type v} {M : Type w} {H : Type z}
    [Group Γ] [TopologicalSpace Γ]
    [TopologicalSpace E] [TopologicalSpace M]
    [Group H] [TopologicalSpace H]
    [IsRealSemisimpleGroup H] [IsUniformLatticeIn Γ H]
    [RationalAcyclicSpace E] [LefschetzInvolutionFixedPointBridge E]
    (hInput : OriginalQuestionInput Γ E M H) :
    ¬ HasTwoTorsion Γ :=
  question7_no_of_original_input_core
    (Γ := Γ) (E := E) (M := M) (H := H) hInput.toCore

theorem question7_no_of_original_input_via_core
    {Γ : Type u} {E : Type v} {M : Type w} {H : Type z}
    [Group Γ] [TopologicalSpace Γ]
    [TopologicalSpace E] [TopologicalSpace M]
    [Group H] [TopologicalSpace H]
    [IsRealSemisimpleGroup H] [IsUniformLatticeIn Γ H]
    [RationalAcyclicSpace E] [LefschetzInvolutionFixedPointBridge E]
    (hInput : OriginalQuestionInput Γ E M H) :
    ¬ HasTwoTorsion Γ :=
  question7_no_of_original_input_core
    (Γ := Γ) (E := E) (M := M) (H := H) hInput.toCore

theorem question7_no_of_original_input_core_rationalAcyclic_fintype_odd
    {Γ : Type u} {E : Type v} {M : Type w} {H : Type z}
    [Group Γ] [TopologicalSpace Γ]
    [TopologicalSpace E] [TopologicalSpace M]
    [Group H] [TopologicalSpace H]
    [IsRealSemisimpleGroup H] [IsUniformLatticeIn Γ H]
    [RationalAcyclicSpace E] [Fintype E] [DecidableEq E] [Fact (Odd (Fintype.card E))]
    (hInput : OriginalQuestionInputCore Γ E M H) :
    ¬ HasTwoTorsion Γ :=
  question7_no_for_uniform_lattice_with_fundamental_group_of_rationalAcyclic_fintype_odd
    (Γ := Γ) (E := E) (M := M) (H := H) hInput.geom hInput.pi1

theorem question7_no_of_original_input_rationalAcyclic_fintype_odd
    {Γ : Type u} {E : Type v} {M : Type w} {H : Type z}
    [Group Γ] [TopologicalSpace Γ]
    [TopologicalSpace E] [TopologicalSpace M]
    [Group H] [TopologicalSpace H]
    [IsRealSemisimpleGroup H] [IsUniformLatticeIn Γ H]
    [RationalAcyclicSpace E] [Fintype E] [DecidableEq E] [Fact (Odd (Fintype.card E))]
    (hInput : OriginalQuestionInputOdd Γ E M H) :
    ¬ HasTwoTorsion Γ :=
  question7_no_of_original_input_core_rationalAcyclic_fintype_odd
    (Γ := Γ) (E := E) (M := M) (H := H) hInput.toCore

/--
Final paper-facing entry theorem (bridge route), expressed using the bridge-agnostic
core input package.
-/
theorem question7_main_paper_form_of_fixed_point_theorem
    {Γ : Type u} {E : Type v} {M : Type w} {H : Type z}
    [Group Γ] [TopologicalSpace Γ]
    [TopologicalSpace E] [TopologicalSpace M]
    [Group H] [TopologicalSpace H]
    [IsRealSemisimpleGroup H] [IsUniformLatticeIn Γ H]
    [RationalAcyclicSpace E]
    (hInput : OriginalQuestionInputCore Γ E M H)
    (hFixed : HasInvolutiveHomeomorphFixedPointProperty E) :
    ¬ HasTwoTorsion Γ :=
  question7_no_for_uniform_lattice_manifold_model_of_fixed_point_theorem
    (Γ := Γ) (E := E) (M := M) (H := H) hInput.geom hFixed

/--
Unbundled paper-facing entry theorem using an explicit fixed-point theorem input.
-/
theorem question7_main_paper_form_unbundled_of_fixed_point_theorem
    {Γ : Type u} {E : Type v} {M : Type w} {H : Type z}
    [Group Γ] [TopologicalSpace Γ]
    [TopologicalSpace E] [TopologicalSpace M]
    [Group H] [TopologicalSpace H]
    [IsRealSemisimpleGroup H] [IsUniformLatticeIn Γ H]
    [RationalAcyclicSpace E]
    (hGeom : UniversalCoverRealization Γ E M)
    (hPi1 : FundamentalGroupRealization Γ M)
    (hFixed : HasInvolutiveHomeomorphFixedPointProperty E) :
    ¬ HasTwoTorsion Γ :=
  question7_main_paper_form_of_fixed_point_theorem
    (Γ := Γ) (E := E) (M := M) (H := H) ⟨hGeom, hPi1⟩ hFixed

/--
Contradiction-form paper-facing theorem with explicit fixed-point theorem input.
-/
theorem question7_main_paper_form_contradiction_of_fixed_point_theorem
    {Γ : Type u} {E : Type v} {M : Type w} {H : Type z}
    [Group Γ] [TopologicalSpace Γ]
    [TopologicalSpace E] [TopologicalSpace M]
    [Group H] [TopologicalSpace H]
    [IsRealSemisimpleGroup H] [IsUniformLatticeIn Γ H]
    [RationalAcyclicSpace E]
    (hInput : OriginalQuestionInputCore Γ E M H)
    (hFixed : HasInvolutiveHomeomorphFixedPointProperty E)
    (hTorsion : HasTwoTorsion Γ) :
    False :=
  (question7_main_paper_form_of_fixed_point_theorem
    (Γ := Γ) (E := E) (M := M) (H := H) hInput hFixed) hTorsion

/--
Final paper-facing entry theorem (bridge route), expressed using the bridge-agnostic
core input package.
-/
theorem question7_main_paper_form
    {Γ : Type u} {E : Type v} {M : Type w} {H : Type z}
    [Group Γ] [TopologicalSpace Γ]
    [TopologicalSpace E] [TopologicalSpace M]
    [Group H] [TopologicalSpace H]
    [IsRealSemisimpleGroup H] [IsUniformLatticeIn Γ H]
    [RationalAcyclicSpace E] [LefschetzInvolutionFixedPointBridge E]
    (hInput : OriginalQuestionInputCore Γ E M H) :
    ¬ HasTwoTorsion Γ :=
  question7_main_paper_form_of_fixed_point_theorem
    (Γ := Γ) (E := E) (M := M) (H := H) hInput
    (hasInvolutiveFixedPointProperty_of_lefschetz E)

/--
Unbundled paper-facing entry theorem (bridge route).
-/
theorem question7_main_paper_form_unbundled
    {Γ : Type u} {E : Type v} {M : Type w} {H : Type z}
    [Group Γ] [TopologicalSpace Γ]
    [TopologicalSpace E] [TopologicalSpace M]
    [Group H] [TopologicalSpace H]
    [IsRealSemisimpleGroup H] [IsUniformLatticeIn Γ H]
    [RationalAcyclicSpace E] [LefschetzInvolutionFixedPointBridge E]
    (hGeom : UniversalCoverRealization Γ E M)
    (hPi1 : FundamentalGroupRealization Γ M) :
    ¬ HasTwoTorsion Γ :=
  question7_main_paper_form
    (Γ := Γ) (E := E) (M := M) (H := H) ⟨hGeom, hPi1⟩

/--
Final paper-facing entry theorem in the finite odd-cardinality route.
-/
theorem question7_main_paper_form_odd
    {Γ : Type u} {E : Type v} {M : Type w} {H : Type z}
    [Group Γ] [TopologicalSpace Γ]
    [TopologicalSpace E] [TopologicalSpace M]
    [Group H] [TopologicalSpace H]
    [IsRealSemisimpleGroup H] [IsUniformLatticeIn Γ H]
    [RationalAcyclicSpace E] [Fintype E] [DecidableEq E] [Fact (Odd (Fintype.card E))]
    (hInput : OriginalQuestionInputCore Γ E M H) :
    ¬ HasTwoTorsion Γ :=
  question7_no_of_original_input_core_rationalAcyclic_fintype_odd
    (Γ := Γ) (E := E) (M := M) (H := H) hInput

/--
Unbundled paper-facing entry theorem in the finite odd-cardinality route.
-/
theorem question7_main_paper_form_odd_unbundled
    {Γ : Type u} {E : Type v} {M : Type w} {H : Type z}
    [Group Γ] [TopologicalSpace Γ]
    [TopologicalSpace E] [TopologicalSpace M]
    [Group H] [TopologicalSpace H]
    [IsRealSemisimpleGroup H] [IsUniformLatticeIn Γ H]
    [RationalAcyclicSpace E] [Fintype E] [DecidableEq E] [Fact (Odd (Fintype.card E))]
    (hGeom : UniversalCoverRealization Γ E M)
    (hPi1 : FundamentalGroupRealization Γ M) :
    ¬ HasTwoTorsion Γ :=
  question7_main_paper_form_odd
    (Γ := Γ) (E := E) (M := M) (H := H) ⟨hGeom, hPi1⟩

theorem question7_no_of_original_input_rationalAcyclic_fintype_odd_via_core
    {Γ : Type u} {E : Type v} {M : Type w} {H : Type z}
    [Group Γ] [TopologicalSpace Γ]
    [TopologicalSpace E] [TopologicalSpace M]
    [Group H] [TopologicalSpace H]
    [IsRealSemisimpleGroup H] [IsUniformLatticeIn Γ H]
    [RationalAcyclicSpace E] [Fintype E] [DecidableEq E] [Fact (Odd (Fintype.card E))]
    (hInput : OriginalQuestionInputOdd Γ E M H) :
    ¬ HasTwoTorsion Γ :=
  question7_no_of_original_input_core_rationalAcyclic_fintype_odd
    (Γ := Γ) (E := E) (M := M) (H := H) hInput.toCore

theorem question7_original_form_answer
    {Γ : Type u} {E : Type v} {M : Type w} {H : Type z}
    [Group Γ] [TopologicalSpace Γ]
    [TopologicalSpace E] [TopologicalSpace M]
    [Group H] [TopologicalSpace H]
    [IsRealSemisimpleGroup H] [IsUniformLatticeIn Γ H]
    [RationalAcyclicSpace E] [LefschetzInvolutionFixedPointBridge E]
    (hGeom : UniversalCoverRealization Γ E M)
    (hPi1 : FundamentalGroupRealization Γ M)
    (hTorsion : HasTwoTorsion Γ) :
    False :=
  (question7_main_paper_form_unbundled
    (Γ := Γ) (E := E) (M := M) (H := H) hGeom hPi1) hTorsion

theorem question7_original_form_answer_of_input_core
    {Γ : Type u} {E : Type v} {M : Type w} {H : Type z}
    [Group Γ] [TopologicalSpace Γ]
    [TopologicalSpace E] [TopologicalSpace M]
    [Group H] [TopologicalSpace H]
    [IsRealSemisimpleGroup H] [IsUniformLatticeIn Γ H]
    [RationalAcyclicSpace E] [LefschetzInvolutionFixedPointBridge E]
    (hInput : OriginalQuestionInputCore Γ E M H)
    (hTorsion : HasTwoTorsion Γ) :
    False :=
  (question7_main_paper_form
    (Γ := Γ) (E := E) (M := M) (H := H) hInput) hTorsion

theorem question7_original_form_answer_of_input
    {Γ : Type u} {E : Type v} {M : Type w} {H : Type z}
    [Group Γ] [TopologicalSpace Γ]
    [TopologicalSpace E] [TopologicalSpace M]
    [Group H] [TopologicalSpace H]
    [IsRealSemisimpleGroup H] [IsUniformLatticeIn Γ H]
    [RationalAcyclicSpace E] [LefschetzInvolutionFixedPointBridge E]
    (hInput : OriginalQuestionInput Γ E M H)
    (hTorsion : HasTwoTorsion Γ) :
    False :=
  question7_original_form_answer_of_input_core
    (Γ := Γ) (E := E) (M := M) (H := H) hInput.toCore hTorsion

theorem question7_main_paper_form_contradiction
    {Γ : Type u} {E : Type v} {M : Type w} {H : Type z}
    [Group Γ] [TopologicalSpace Γ]
    [TopologicalSpace E] [TopologicalSpace M]
    [Group H] [TopologicalSpace H]
    [IsRealSemisimpleGroup H] [IsUniformLatticeIn Γ H]
    [RationalAcyclicSpace E] [LefschetzInvolutionFixedPointBridge E]
    (hInput : OriginalQuestionInputCore Γ E M H)
    (hTorsion : HasTwoTorsion Γ) :
    False :=
  (question7_main_paper_form
    (Γ := Γ) (E := E) (M := M) (H := H) hInput) hTorsion

theorem question7_original_form_answer_of_input_via_core
    {Γ : Type u} {E : Type v} {M : Type w} {H : Type z}
    [Group Γ] [TopologicalSpace Γ]
    [TopologicalSpace E] [TopologicalSpace M]
    [Group H] [TopologicalSpace H]
    [IsRealSemisimpleGroup H] [IsUniformLatticeIn Γ H]
    [RationalAcyclicSpace E] [LefschetzInvolutionFixedPointBridge E]
    (hInput : OriginalQuestionInput Γ E M H)
    (hTorsion : HasTwoTorsion Γ) :
    False :=
  question7_original_form_answer_of_input_core
    (Γ := Γ) (E := E) (M := M) (H := H) hInput.toCore hTorsion

theorem question7_original_form_answer_of_rationalAcyclic_fintype_odd
    {Γ : Type u} {E : Type v} {M : Type w} {H : Type z}
    [Group Γ] [TopologicalSpace Γ]
    [TopologicalSpace E] [TopologicalSpace M]
    [Group H] [TopologicalSpace H]
    [IsRealSemisimpleGroup H] [IsUniformLatticeIn Γ H]
    [RationalAcyclicSpace E] [Fintype E] [DecidableEq E] [Fact (Odd (Fintype.card E))]
    (hGeom : UniversalCoverRealization Γ E M)
    (hPi1 : FundamentalGroupRealization Γ M)
    (hTorsion : HasTwoTorsion Γ) :
    False :=
  (question7_main_paper_form_odd_unbundled
    (Γ := Γ) (E := E) (M := M) (H := H) hGeom hPi1) hTorsion

theorem question7_original_form_answer_of_input_core_rationalAcyclic_fintype_odd
    {Γ : Type u} {E : Type v} {M : Type w} {H : Type z}
    [Group Γ] [TopologicalSpace Γ]
    [TopologicalSpace E] [TopologicalSpace M]
    [Group H] [TopologicalSpace H]
    [IsRealSemisimpleGroup H] [IsUniformLatticeIn Γ H]
    [RationalAcyclicSpace E] [Fintype E] [DecidableEq E] [Fact (Odd (Fintype.card E))]
    (hInput : OriginalQuestionInputCore Γ E M H)
    (hTorsion : HasTwoTorsion Γ) :
    False :=
  (question7_main_paper_form_odd
    (Γ := Γ) (E := E) (M := M) (H := H) hInput) hTorsion

theorem question7_original_form_answer_of_input_rationalAcyclic_fintype_odd
    {Γ : Type u} {E : Type v} {M : Type w} {H : Type z}
    [Group Γ] [TopologicalSpace Γ]
    [TopologicalSpace E] [TopologicalSpace M]
    [Group H] [TopologicalSpace H]
    [IsRealSemisimpleGroup H] [IsUniformLatticeIn Γ H]
    [RationalAcyclicSpace E] [Fintype E] [DecidableEq E] [Fact (Odd (Fintype.card E))]
    (hInput : OriginalQuestionInputOdd Γ E M H)
    (hTorsion : HasTwoTorsion Γ) :
    False :=
  question7_original_form_answer_of_input_core_rationalAcyclic_fintype_odd
    (Γ := Γ) (E := E) (M := M) (H := H) hInput.toCore hTorsion

theorem question7_main_paper_form_odd_contradiction
    {Γ : Type u} {E : Type v} {M : Type w} {H : Type z}
    [Group Γ] [TopologicalSpace Γ]
    [TopologicalSpace E] [TopologicalSpace M]
    [Group H] [TopologicalSpace H]
    [IsRealSemisimpleGroup H] [IsUniformLatticeIn Γ H]
    [RationalAcyclicSpace E] [Fintype E] [DecidableEq E] [Fact (Odd (Fintype.card E))]
    (hInput : OriginalQuestionInputCore Γ E M H)
    (hTorsion : HasTwoTorsion Γ) :
    False :=
  (question7_main_paper_form_odd
    (Γ := Γ) (E := E) (M := M) (H := H) hInput) hTorsion

theorem question7_original_form_answer_of_input_rationalAcyclic_fintype_odd_via_core
    {Γ : Type u} {E : Type v} {M : Type w} {H : Type z}
    [Group Γ] [TopologicalSpace Γ]
    [TopologicalSpace E] [TopologicalSpace M]
    [Group H] [TopologicalSpace H]
    [IsRealSemisimpleGroup H] [IsUniformLatticeIn Γ H]
    [RationalAcyclicSpace E] [Fintype E] [DecidableEq E] [Fact (Odd (Fintype.card E))]
    (hInput : OriginalQuestionInputOdd Γ E M H)
    (hTorsion : HasTwoTorsion Γ) :
    False :=
  question7_original_form_answer_of_input_core_rationalAcyclic_fintype_odd
    (Γ := Γ) (E := E) (M := M) (H := H) hInput.toCore hTorsion

end Question7
