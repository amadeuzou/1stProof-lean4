import Question10.PCG

namespace Question10

def IsBigONat (f g : Nat → Nat) : Prop :=
  ∃ C : Nat, 0 < C ∧ ∀ t, f t ≤ C * g t

theorem isBigONat_refl (f : Nat → Nat) : IsBigONat f f := by
  refine ⟨1, by decide, ?_⟩
  intro t
  simp

def iterCostFamily (n r q : Nat → Nat) : Nat → Nat :=
  fun t => q t * (2 * r t + n t * r t) + 2 * (n t * n t * r t) + 6 * (n t * r t)

def totalCostFamily (n r q iters : Nat → Nat) : Nat → Nat :=
  fun t => iters t * iterCostFamily n r q t

theorem totalCostFamily_isBigO_self
    (n r q iters : Nat → Nat) :
    IsBigONat (totalCostFamily n r q iters) (totalCostFamily n r q iters) :=
  isBigONat_refl _

namespace ProblemData

variable (P : ProblemData)

def costPreconditionerSolve : Nat := P.n * P.n * P.r

def costVectorUpdates : Nat := 6 * (P.n * P.r)

def costPCGIter : Nat := P.costSystemMatVec + P.costPreconditionerSolve + P.costVectorUpdates

def totalCost (iters : Nat) : Nat := iters * P.costPCGIter

theorem costPCGIter_eq :
    P.costPCGIter =
      P.q * (2 * P.r + P.n * P.r) + P.n * P.n * P.r + P.n * P.n * P.r + 6 * (P.n * P.r) := by
  simp [costPCGIter, costPreconditionerSolve, costVectorUpdates, P.costSystemMatVec_eq]

theorem totalCost_eq (iters : Nat) :
    P.totalCost iters = iters * P.costPCGIter := rfl

theorem totalCost_add (a b : Nat) :
    P.totalCost (a + b) = P.totalCost a + P.totalCost b := by
  simp [totalCost, Nat.add_mul, Nat.mul_add, Nat.add_assoc, Nat.add_comm, Nat.add_left_comm]

theorem totalCost_mono {a b : Nat} (h : a ≤ b) :
    P.totalCost a ≤ P.totalCost b := by
  simpa [totalCost] using Nat.mul_le_mul_right P.costPCGIter h

theorem totalCost_isBigO_linearIters :
    IsBigONat (fun t => P.totalCost t) (fun t => t * P.costPCGIter) := by
  refine ⟨1, by decide, ?_⟩
  intro t
  simp [totalCost]

end ProblemData
end Question10
