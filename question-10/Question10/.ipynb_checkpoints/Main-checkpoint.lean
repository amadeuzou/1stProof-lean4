import Question10.Complexity

namespace Question10
namespace ProblemData

variable (P : ProblemData)

theorem sparse_matvec_avoids_ambient_enumeration :
    P.observationCount ≤ P.ambientTensorSize ∧
      P.costSystemMatVec ≤
        P.ambientTensorSize * (2 * P.r + P.n * P.r) + P.n * P.n * P.r := by
  exact ⟨P.avoid_ambient_enumeration, P.costSystemMatVec_le_ambient_scaled⟩

theorem main_solver_statement
    (hDataSymm : P.Symmetric P.dataTerm)
    (hDataNonneg : P.PosSemidef P.dataTerm)
    (hKSymm : P.Symmetric P.kMul)
    (hKPos : P.PosDef P.kMul) :
    P.PCGAdmissible P.systemOp (P.preconditionerApply P.defaultMu) ∧
      P.costSystemMatVec = P.q * (2 * P.r + P.n * P.r) + P.n * P.n * P.r ∧
      (∀ iters : Nat, P.totalCost iters = iters * P.costPCGIter) := by
  refine ⟨P.pcg_ready_fully_structured hDataSymm hDataNonneg hKSymm hKPos,
    P.costSystemMatVec_eq, ?_⟩
  intro iters
  exact P.totalCost_eq iters

theorem sparse_matvec_strictly_better_than_ambient
    (hqStrict : P.q < P.ambientTensorSize) :
    P.costSystemMatVec <
      P.ambientTensorSize * (2 * P.r + P.n * P.r) + P.n * P.n * P.r := by
  exact P.costSystemMatVec_lt_ambient_scaled hqStrict

end ProblemData
end Question10
