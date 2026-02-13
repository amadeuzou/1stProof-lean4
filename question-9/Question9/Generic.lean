import Question9.Geometry
import Mathlib.Algebra.MvPolynomial.CommRing

namespace Question9

abbrev CameraVar (n : Nat) := Idx n × Fin 3 × Fin 4

def evalCameraVar {n : Nat} (A : CameraMatrices n) : CameraVar n → ℝ
  | ⟨a, i, j⟩ => A a i j

def AnchorNonzeroCondition {n : Nat} (A : CameraMatrices n) : Prop :=
  ∀ a b c d, valid a b c d → QInput A (anchorQIndex a b c d) ≠ 0

abbrev GenericFamily (n m : Nat) := Fin m → MvPolynomial (CameraVar n) ℝ

noncomputable def cameraRowPoly {n : Nat} (a : Idx n) (i : Fin 3) :
    Fin 4 → MvPolynomial (CameraVar n) ℝ :=
  fun j => MvPolynomial.X (a, i, j)

noncomputable def Q_entryPoly
    {n : Nat}
    (a b c d : Idx n)
    (i j k l : Fin 3) : MvPolynomial (CameraVar n) ℝ :=
  Matrix.det (matrixFromFourRows
    (cameraRowPoly a i)
    (cameraRowPoly b j)
    (cameraRowPoly c k)
    (cameraRowPoly d l))

noncomputable def anchorQPoly {n : Nat} (a b c d : Idx n) :
    MvPolynomial (CameraVar n) ℝ :=
  Q_entryPoly a b c d rowAnchor rowAnchor rowAnchor rowAnchor

def IsGenericWith {n m : Nat} (A : CameraMatrices n) (G : GenericFamily n m) : Prop :=
  ∀ t, MvPolynomial.eval (evalCameraVar A) (G t) ≠ 0

def IsGeneric {n : Nat} (A : CameraMatrices n) : Prop :=
  ∀ a b c d, valid a b c d →
    MvPolynomial.eval (evalCameraVar A) (anchorQPoly a b c d) ≠ 0

def IsGenericStrong {n : Nat} (A : CameraMatrices n) : Prop :=
  ∀ idx : QIndex n, validIndex idx → QInput A idx ≠ 0

theorem eval_Q_entryPoly
    {n : Nat}
    (A : CameraMatrices n)
    (a b c d : Idx n)
    (i j k l : Fin 3) :
    MvPolynomial.eval (evalCameraVar A) (Q_entryPoly a b c d i j k l) =
      Q_entry A a b c d i j k l := by
  let Mpoly : Matrix (Fin 4) (Fin 4) (MvPolynomial (CameraVar n) ℝ) :=
    matrixFromFourRows
      (cameraRowPoly a i)
      (cameraRowPoly b j)
      (cameraRowPoly c k)
      (cameraRowPoly d l)
  have hMap :
      (MvPolynomial.eval (evalCameraVar A)).mapMatrix Mpoly =
        matrixFromFourRows (A a i) (A b j) (A c k) (A d l) := by
    ext p q
    fin_cases p <;> simp [Mpoly, matrixFromFourRows, cameraRowPoly, evalCameraVar]
  have hDetMap :
      MvPolynomial.eval (evalCameraVar A) (Matrix.det Mpoly) =
        Matrix.det ((MvPolynomial.eval (evalCameraVar A)).mapMatrix Mpoly) := by
    simpa using RingHom.map_det (MvPolynomial.eval (evalCameraVar A)) Mpoly
  simpa [Q_entryPoly, Q_entry, Mpoly] using hDetMap.trans (by simp [hMap])

theorem eval_anchorQPoly
    {n : Nat}
    (A : CameraMatrices n)
    (a b c d : Idx n) :
    MvPolynomial.eval (evalCameraVar A) (anchorQPoly a b c d) =
      QInput A (anchorQIndex a b c d) := by
  simpa [anchorQPoly, QInput, anchorQIndex] using
    eval_Q_entryPoly A a b c d rowAnchor rowAnchor rowAnchor rowAnchor

theorem isGenericWith_iff_eval_nonzero
    {n m : Nat} (A : CameraMatrices n) (G : GenericFamily n m) :
    IsGenericWith A G ↔ ∀ t, MvPolynomial.eval (evalCameraVar A) (G t) ≠ 0 := by
  rfl

theorem isGeneric_of_anchorNonzero
    {n : Nat}
    (A : CameraMatrices n)
    (hAnchor : AnchorNonzeroCondition A) :
    IsGeneric A := by
  intro a b c d hvalid
  simpa [eval_anchorQPoly] using hAnchor a b c d hvalid

theorem anchorNonzero_of_isGeneric
    {n : Nat}
    (A : CameraMatrices n)
    (hGeneric : IsGeneric A) :
    AnchorNonzeroCondition A := by
  intro a b c d hvalid
  simpa [eval_anchorQPoly] using hGeneric a b c d hvalid

theorem anchor_nonzero_of_isGeneric
    {n : Nat}
    (A : CameraMatrices n)
    (hGeneric : IsGeneric A) :
    AnchorNonzeroCondition A := by
  exact anchorNonzero_of_isGeneric A hGeneric

theorem qInput_nonzero_of_isGeneric_anchorRows
    {n : Nat}
    (A : CameraMatrices n)
    (hGeneric : IsGeneric A)
    (idx : QIndex n)
    (hValid : validIndex idx)
    (hRows : AnchorRows idx) :
    QInput A idx ≠ 0 := by
  have hAnchor : QInput A (anchorQIndex idx.a idx.b idx.c idx.d) ≠ 0 := by
    exact anchor_nonzero_of_isGeneric A hGeneric idx.a idx.b idx.c idx.d hValid
  rw [qInput_eq_anchor_of_anchorRows A idx hRows]
  exact hAnchor

theorem qInput_nonzero_of_isGenericStrong
    {n : Nat}
    (A : CameraMatrices n)
    (hGeneric : IsGenericStrong A)
    (idx : QIndex n)
    (hValid : validIndex idx) :
    QInput A idx ≠ 0 := by
  exact hGeneric idx hValid

theorem isGenericStrong_implies_isGeneric
    {n : Nat}
    (A : CameraMatrices n)
    (hStrong : IsGenericStrong A) :
    IsGeneric A := by
  intro a b c d hvalid
  have hq : QInput A (anchorQIndex a b c d) ≠ 0 := hStrong (anchorQIndex a b c d) hvalid
  simpa [eval_anchorQPoly] using hq

end Question9
