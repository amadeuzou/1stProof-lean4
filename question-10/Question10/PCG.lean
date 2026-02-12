import Question10.SparseMatVec

namespace Question10
namespace ProblemData

variable (P : ProblemData)

def frobInner (X Y : P.Unknown) : ℝ :=
  ∑ i : Fin P.n, ∑ j : Fin P.r, X i j * Y i j

def Symmetric (A : P.Unknown → P.Unknown) : Prop :=
  ∀ X Y, P.frobInner (A X) Y = P.frobInner X (A Y)

def PosDef (A : P.Unknown → P.Unknown) : Prop :=
  ∀ X, X ≠ 0 → 0 < P.frobInner (A X) X

def PosSemidef (A : P.Unknown → P.Unknown) : Prop :=
  ∀ X, 0 ≤ P.frobInner (A X) X

def SPD (A : P.Unknown → P.Unknown) : Prop :=
  P.Symmetric A ∧ P.PosDef A

def preconditionerMatrix (mu : ℝ) : Matrix (Fin P.n) (Fin P.n) ℝ :=
  P.K + mu • (1 : Matrix (Fin P.n) (Fin P.n) ℝ)

def preconditionerApply (mu : ℝ) (X : P.Unknown) : P.Unknown :=
  (P.preconditionerMatrix mu) * X

def defaultMu : ℝ := P.lambda

def PCGAdmissible (A M : P.Unknown → P.Unknown) : Prop :=
  P.SPD A ∧ P.SPD M

theorem defaultMu_pos : 0 < P.defaultMu := P.hlambda

theorem frobInner_add_left (X Y Z : P.Unknown) :
    P.frobInner (X + Y) Z = P.frobInner X Z + P.frobInner Y Z := by
  unfold ProblemData.frobInner
  simp [add_mul, Finset.sum_add_distrib, add_assoc, add_left_comm, add_comm]

theorem frobInner_add_right (X Y Z : P.Unknown) :
    P.frobInner X (Y + Z) = P.frobInner X Y + P.frobInner X Z := by
  unfold ProblemData.frobInner
  simp [mul_add, Finset.sum_add_distrib, add_assoc, add_left_comm, add_comm]

theorem frobInner_smul_left (a : ℝ) (X Z : P.Unknown) :
    P.frobInner (a • X) Z = a * P.frobInner X Z := by
  unfold ProblemData.frobInner
  simp [mul_assoc, Finset.mul_sum, Finset.sum_mul, mul_left_comm, mul_comm, mul_assoc]

theorem frobInner_smul_right (a : ℝ) (X Z : P.Unknown) :
    P.frobInner X (a • Z) = a * P.frobInner X Z := by
  unfold ProblemData.frobInner
  simp [mul_assoc, Finset.mul_sum, Finset.sum_mul, mul_left_comm, mul_comm, mul_assoc]

theorem symmetric_add {A B : P.Unknown → P.Unknown}
    (hA : P.Symmetric A)
    (hB : P.Symmetric B) :
    P.Symmetric (fun X => A X + B X) := by
  intro X Y
  rw [P.frobInner_add_left, hA X Y, hB X Y, P.frobInner_add_right]

theorem symmetric_smul {A : P.Unknown → P.Unknown}
    (a : ℝ)
    (hA : P.Symmetric A) :
    P.Symmetric (fun X => a • A X) := by
  intro X Y
  rw [P.frobInner_smul_left, hA X Y, P.frobInner_smul_right]

theorem posDef_of_psd_add_smul
    (hDataNonneg : P.PosSemidef P.dataTerm)
    (hKPos : P.PosDef P.kMul) :
    P.PosDef P.systemOp := by
  intro X hX
  have h1 : 0 ≤ P.frobInner (P.dataTerm X) X := hDataNonneg X
  have h2 : 0 < P.frobInner (P.kMul X) X := hKPos X hX
  have hl : 0 < P.lambda := P.hlambda
  have hEq : P.frobInner (P.systemOp X) X =
      P.frobInner (P.dataTerm X) X + P.lambda * P.frobInner (P.kMul X) X := by
    simp [ProblemData.systemOp, P.frobInner_add_left, P.frobInner_smul_left]
  rw [hEq]
  nlinarith

theorem spd_systemOp_of_assumptions
    (hDataSymm : P.Symmetric P.dataTerm)
    (hDataNonneg : P.PosSemidef P.dataTerm)
    (hKSymm : P.Symmetric P.kMul)
    (hKPos : P.PosDef P.kMul) :
    P.SPD P.systemOp := by
  refine ⟨?_, ?_⟩
  · have hSymRegularizer : P.Symmetric (fun X => P.lambda • P.kMul X) :=
      P.symmetric_smul P.lambda hKSymm
    simpa [ProblemData.systemOp] using P.symmetric_add hDataSymm hSymRegularizer
  · exact P.posDef_of_psd_add_smul hDataNonneg hKPos

theorem frobInner_self_nonneg (X : P.Unknown) : 0 ≤ P.frobInner X X := by
  unfold ProblemData.frobInner
  refine Finset.sum_nonneg ?_
  intro i hi
  refine Finset.sum_nonneg ?_
  intro j hj
  nlinarith

theorem preconditionerApply_eq (mu : ℝ) (X : P.Unknown) :
    P.preconditionerApply mu X = P.kMul X + mu • X := by
  simp [ProblemData.preconditionerApply, ProblemData.preconditionerMatrix, ProblemData.kMul,
    Matrix.add_mul]

theorem symmetric_id : P.Symmetric (fun X : P.Unknown => X) := by
  intro X Y
  rfl

theorem spd_preconditioner_of_kernel_assumptions
    (hKSymm : P.Symmetric P.kMul)
    (hKPos : P.PosDef P.kMul) :
    P.SPD (P.preconditionerApply P.defaultMu) := by
  refine ⟨?_, ?_⟩
  · have hSymScaledId : P.Symmetric (fun X => P.defaultMu • X) :=
      P.symmetric_smul P.defaultMu P.symmetric_id
    have hSymAdd : P.Symmetric (fun X => P.kMul X + P.defaultMu • X) :=
      P.symmetric_add hKSymm hSymScaledId
    have hEqFun : P.preconditionerApply P.defaultMu = (fun X => P.kMul X + P.defaultMu • X) := by
      funext X
      simp [P.preconditionerApply_eq P.defaultMu X]
    simpa [hEqFun] using hSymAdd
  · intro X hX
    have hk : 0 < P.frobInner (P.kMul X) X := hKPos X hX
    have hSelf : 0 ≤ P.frobInner X X := P.frobInner_self_nonneg X
    have hmu : 0 < P.defaultMu := P.defaultMu_pos
    have hEq : P.frobInner (P.preconditionerApply P.defaultMu X) X =
        P.frobInner (P.kMul X) X + P.defaultMu * P.frobInner X X := by
      rw [P.preconditionerApply_eq P.defaultMu]
      simp [P.frobInner_add_left, P.frobInner_smul_left]
    rw [hEq]
    nlinarith

theorem pcgAdmissible_of_spd
    {A M : P.Unknown → P.Unknown}
    (hA : P.SPD A)
    (hM : P.SPD M) :
    P.PCGAdmissible A M := ⟨hA, hM⟩

theorem pcg_ready_with_default_preconditioner
    (hA : P.SPD P.systemOp)
    (hM : P.SPD (P.preconditionerApply P.defaultMu)) :
    P.PCGAdmissible P.systemOp (P.preconditionerApply P.defaultMu) := by
  exact P.pcgAdmissible_of_spd hA hM

theorem pcg_ready_of_structured_assumptions
    (hDataSymm : P.Symmetric P.dataTerm)
    (hDataNonneg : P.PosSemidef P.dataTerm)
    (hKSymm : P.Symmetric P.kMul)
    (hKPos : P.PosDef P.kMul)
    (hM : P.SPD (P.preconditionerApply P.defaultMu)) :
    P.PCGAdmissible P.systemOp (P.preconditionerApply P.defaultMu) := by
  exact P.pcgAdmissible_of_spd
    (P.spd_systemOp_of_assumptions hDataSymm hDataNonneg hKSymm hKPos) hM

theorem pcg_ready_fully_structured
    (hDataSymm : P.Symmetric P.dataTerm)
    (hDataNonneg : P.PosSemidef P.dataTerm)
    (hKSymm : P.Symmetric P.kMul)
    (hKPos : P.PosDef P.kMul) :
    P.PCGAdmissible P.systemOp (P.preconditionerApply P.defaultMu) := by
  exact P.pcgAdmissible_of_spd
    (P.spd_systemOp_of_assumptions hDataSymm hDataNonneg hKSymm hKPos)
    (P.spd_preconditioner_of_kernel_assumptions hKSymm hKPos)

theorem preconditionerMatrix_form (mu : ℝ) :
    P.preconditionerMatrix mu = P.K + mu • (1 : Matrix (Fin P.n) (Fin P.n) ℝ) := rfl

end ProblemData
end Question10
