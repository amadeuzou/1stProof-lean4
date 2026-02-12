import Question10.Defs

namespace Question10
namespace ProblemData

variable (P : ProblemData)

def matVecUsingObservations (X : P.Unknown) : P.Unknown := P.systemOp X

def costSampleScore : Nat := 2 * P.r

def costSampleAccumulate : Nat := P.n * P.r

def costDataTerm : Nat := P.q * (P.costSampleScore + P.costSampleAccumulate)

def costKernelRegularizer : Nat := P.n * P.n * P.r

def costSystemMatVec : Nat := P.costDataTerm + P.costKernelRegularizer

theorem matVecUsingObservations_eq (X : P.Unknown) :
    P.matVecUsingObservations X = P.systemOp X := rfl

theorem costDataTerm_eq :
    P.costDataTerm = P.q * (2 * P.r + P.n * P.r) := by
  simp [costDataTerm, costSampleScore, costSampleAccumulate]

theorem costSystemMatVec_eq :
    P.costSystemMatVec = P.q * (2 * P.r + P.n * P.r) + P.n * P.n * P.r := by
  simp [costSystemMatVec, costKernelRegularizer, P.costDataTerm_eq]

theorem costSystemMatVec_le_ambient_scaled :
    P.costSystemMatVec ≤
      P.ambientTensorSize * (2 * P.r + P.n * P.r) + P.n * P.n * P.r := by
  have hmul :
      P.q * (2 * P.r + P.n * P.r) ≤
        P.ambientTensorSize * (2 * P.r + P.n * P.r) :=
    Nat.mul_le_mul_right _ P.avoid_ambient_enumeration
  calc
    P.costSystemMatVec
        = P.q * (2 * P.r + P.n * P.r) + P.n * P.n * P.r := P.costSystemMatVec_eq
    _ ≤ P.ambientTensorSize * (2 * P.r + P.n * P.r) + P.n * P.n * P.r :=
      Nat.add_le_add hmul le_rfl

theorem costSystemMatVec_lt_ambient_scaled
    (hqStrict : P.q < P.ambientTensorSize) :
    P.costSystemMatVec <
      P.ambientTensorSize * (2 * P.r + P.n * P.r) + P.n * P.n * P.r := by
  have hfactor : 0 < 2 * P.r + P.n * P.r := by
    have h2r : 0 < 2 * P.r := Nat.mul_pos (by decide) P.hr
    exact Nat.add_pos_left h2r _
  have hmul :
      P.q * (2 * P.r + P.n * P.r) <
        P.ambientTensorSize * (2 * P.r + P.n * P.r) :=
    Nat.mul_lt_mul_of_pos_right hqStrict hfactor
  calc
    P.costSystemMatVec
        = P.q * (2 * P.r + P.n * P.r) + P.n * P.n * P.r := P.costSystemMatVec_eq
    _ < P.ambientTensorSize * (2 * P.r + P.n * P.r) + P.n * P.n * P.r :=
      Nat.add_lt_add_right hmul _

end ProblemData
end Question10
