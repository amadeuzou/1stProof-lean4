import Mathlib

namespace Question10

open BigOperators Matrix

abbrev Mat (n r : Nat) := Matrix (Fin n) (Fin r) ℝ

structure ProblemData where
  n : Nat
  r : Nat
  M : Nat
  q : Nat
  hn : 0 < n
  hr : 0 < r
  hq : q ≤ n * M
  K : Matrix (Fin n) (Fin n) ℝ
  Z : Matrix (Fin M) (Fin r) ℝ
  B : Matrix (Fin n) (Fin r) ℝ
  obs : Fin q → Fin n × Fin M
  lambda : ℝ
  hlambda : 0 < lambda

namespace ProblemData

variable (P : ProblemData)

abbrev Unknown := Mat P.n P.r

def kMul (X : P.Unknown) : P.Unknown := P.K * X

def rhs : P.Unknown := P.kMul P.B

def sampleScore (X : P.Unknown) (p : Fin P.q) : ℝ :=
  let im := P.obs p
  let i : Fin P.n := im.1
  let m : Fin P.M := im.2
  ∑ t : Fin P.r, (P.kMul X) i t * P.Z m t

def dataTerm (X : P.Unknown) : P.Unknown :=
  fun j l =>
    ∑ p : Fin P.q,
      let im := P.obs p
      let i : Fin P.n := im.1
      let m : Fin P.M := im.2
      P.K j i * P.Z m l * P.sampleScore X p

def systemOp (X : P.Unknown) : P.Unknown :=
  P.dataTerm X + P.lambda • P.kMul X

def observationCount : Nat := P.q

def ambientTensorSize : Nat := P.n * P.M

theorem avoid_ambient_enumeration : P.observationCount ≤ P.ambientTensorSize := P.hq

end ProblemData
end Question10
