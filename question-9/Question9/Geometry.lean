import Question9.Defs
import Mathlib.LinearAlgebra.Determinant

namespace Question9

open Matrix

abbrev CameraMatrices (n : Nat) := Idx n → Matrix (Fin 3) (Fin 4) ℝ

def matrixFromFourRows
    {R : Type*}
    (r1 r2 r3 r4 : Fin 4 → R) : Matrix (Fin 4) (Fin 4) R :=
  fun p q =>
    match p.1 with
    | 0 => r1 q
    | 1 => r2 q
    | 2 => r3 q
    | _ => r4 q

def f0 : Fin 4 := ⟨0, by decide⟩
def f1 : Fin 4 := ⟨1, by decide⟩
def f2 : Fin 4 := ⟨2, by decide⟩
def f3 : Fin 4 := ⟨3, by decide⟩

@[simp] theorem matrixFromFourRows_f0
    {R : Type*}
    (r1 r2 r3 r4 : Fin 4 → R) :
    matrixFromFourRows r1 r2 r3 r4 f0 = r1 := by
  funext q
  simp [matrixFromFourRows, f0]

@[simp] theorem matrixFromFourRows_f1
    {R : Type*}
    (r1 r2 r3 r4 : Fin 4 → R) :
    matrixFromFourRows r1 r2 r3 r4 f1 = r2 := by
  funext q
  simp [matrixFromFourRows, f1]

theorem matrixFromFourRows_swap12_submatrix
    {R : Type*}
    (r1 r2 r3 r4 : Fin 4 → R) :
    matrixFromFourRows r2 r1 r3 r4 =
      (matrixFromFourRows r1 r2 r3 r4).submatrix (Equiv.swap f0 f1) id := by
  ext p q
  fin_cases p <;> simp [matrixFromFourRows, f0, f1, Equiv.swap_apply_def]

theorem matrixFromFourRows_swap13_submatrix
    {R : Type*}
    (r1 r2 r3 r4 : Fin 4 → R) :
    matrixFromFourRows r3 r2 r1 r4 =
      (matrixFromFourRows r1 r2 r3 r4).submatrix (Equiv.swap f0 f2) id := by
  ext p q
  fin_cases p <;> simp [matrixFromFourRows, f0, f2, Equiv.swap_apply_def]

theorem matrixFromFourRows_swap34_submatrix
    {R : Type*}
    (r1 r2 r3 r4 : Fin 4 → R) :
    matrixFromFourRows r1 r2 r4 r3 =
      (matrixFromFourRows r1 r2 r3 r4).submatrix (Equiv.swap f2 f3) id := by
  ext p q
  fin_cases p <;> simp [matrixFromFourRows, f2, f3, Equiv.swap_apply_def]

noncomputable def Q_entry
    {n : Nat}
    (A : CameraMatrices n)
    (a b c d : Idx n)
    (i j k l : Fin 3) : ℝ :=
  Matrix.det (matrixFromFourRows (A a i) (A b j) (A c k) (A d l))

theorem Q_entry_zero_of_first_two_rows_eq
    {n : Nat}
    (A : CameraMatrices n)
    (a b c d : Idx n)
    (i j k l : Fin 3)
    (hrow : A a i = A b j) :
    Q_entry A a b c d i j k l = 0 := by
  unfold Q_entry
  have hrows :
      matrixFromFourRows (A a i) (A b j) (A c k) (A d l) f0 =
        matrixFromFourRows (A a i) (A b j) (A c k) (A d l) f1 := by
    simp [hrow]
  exact Matrix.det_zero_of_row_eq (M := matrixFromFourRows (A a i) (A b j) (A c k) (A d l))
    (show f0 ≠ f1 by decide) hrows

theorem Q_entry_zero_of_repeat_first_two
    {n : Nat}
    (A : CameraMatrices n)
    (a c d : Idx n)
    (i k l : Fin 3) :
    Q_entry A a a c d i i k l = 0 := by
  exact Q_entry_zero_of_first_two_rows_eq A a a c d i i k l rfl

theorem Q_entry_swap_first_two
    {n : Nat}
    (A : CameraMatrices n)
    (a b c d : Idx n)
    (i j k l : Fin 3) :
    Q_entry A b a c d j i k l = - Q_entry A a b c d i j k l := by
  unfold Q_entry
  rw [matrixFromFourRows_swap12_submatrix]
  rw [Matrix.det_permute (σ := Equiv.swap f0 f1)]
  have hsign : ((↑↑(Equiv.Perm.sign (Equiv.swap f0 f1)) : ℝ)) = -1 := by
    norm_num [Equiv.Perm.sign_swap (show f0 ≠ f1 by decide)]
  rw [hsign]
  ring

theorem Q_entry_swap_first_third
    {n : Nat}
    (A : CameraMatrices n)
    (a b c d : Idx n)
    (i j k l : Fin 3) :
    Q_entry A c b a d k j i l = - Q_entry A a b c d i j k l := by
  unfold Q_entry
  rw [matrixFromFourRows_swap13_submatrix]
  rw [Matrix.det_permute (σ := Equiv.swap f0 f2)]
  have hsign : ((↑↑(Equiv.Perm.sign (Equiv.swap f0 f2)) : ℝ)) = -1 := by
    norm_num [Equiv.Perm.sign_swap (show f0 ≠ f2 by decide)]
  rw [hsign]
  ring

theorem Q_entry_swap_third_fourth
    {n : Nat}
    (A : CameraMatrices n)
    (a b c d : Idx n)
    (i j k l : Fin 3) :
    Q_entry A a b d c i j l k = - Q_entry A a b c d i j k l := by
  unfold Q_entry
  rw [matrixFromFourRows_swap34_submatrix]
  rw [Matrix.det_permute (σ := Equiv.swap f2 f3)]
  have hsign : ((↑↑(Equiv.Perm.sign (Equiv.swap f2 f3)) : ℝ)) = -1 := by
    norm_num [Equiv.Perm.sign_swap (show f2 ≠ f3 by decide)]
  rw [hsign]
  ring

structure QIndex (n : Nat) where
  a : Idx n
  b : Idx n
  c : Idx n
  d : Idx n
  i : Fin 3
  j : Fin 3
  k : Fin 3
  l : Fin 3

abbrev InputVector (n : Nat) := QIndex n → ℝ

def validIndex {n : Nat} (idx : QIndex n) : Prop :=
  valid idx.a idx.b idx.c idx.d

noncomputable def QInput {n : Nat} (A : CameraMatrices n) : InputVector n :=
  fun idx => Q_entry A idx.a idx.b idx.c idx.d idx.i idx.j idx.k idx.l

def scaleInput {n : Nat} (lam : Lambda n) (T : InputVector n) : InputVector n :=
  fun idx => lam idx.a idx.b idx.c idx.d * T idx

def isScaledInput {n : Nat} (Y : InputVector n) (lam : Lambda n) (Q : InputVector n) : Prop :=
  ∀ idx, validIndex idx → Y idx = lam idx.a idx.b idx.c idx.d * Q idx

def rowAnchor : Fin 3 := ⟨0, by decide⟩

def AnchorRows {n : Nat} (idx : QIndex n) : Prop :=
  idx.i = rowAnchor ∧ idx.j = rowAnchor ∧ idx.k = rowAnchor ∧ idx.l = rowAnchor

def anchorQIndex {n : Nat} (a b c d : Idx n) : QIndex n where
  a := a
  b := b
  c := c
  d := d
  i := rowAnchor
  j := rowAnchor
  k := rowAnchor
  l := rowAnchor

theorem qInput_eq_anchor_of_anchorRows
    {n : Nat}
    (A : CameraMatrices n)
    (idx : QIndex n)
    (hRows : AnchorRows idx) :
    QInput A idx = QInput A (anchorQIndex idx.a idx.b idx.c idx.d) := by
  cases idx with
  | mk a b c d i j k l =>
      rcases hRows with ⟨hi, hj, hk, hl⟩
      have hi' : i = rowAnchor := by simpa using hi
      have hj' : j = rowAnchor := by simpa using hj
      have hk' : k = rowAnchor := by simpa using hk
      have hl' : l = rowAnchor := by simpa using hl
      simp [QInput, anchorQIndex, hi', hj', hk', hl']

noncomputable def extractLambdaFromInput
    {n : Nat}
    (Q Y : InputVector n) : Lambda n :=
  fun a b c d => Y (anchorQIndex a b c d) / Q (anchorQIndex a b c d)

theorem extractLambdaFromInput_eq
    {n : Nat}
    (Q Y : InputVector n)
    (lam : Lambda n)
    (hScale : isScaledInput Y lam Q)
    (hQNZ : ∀ a b c d, valid a b c d → Q (anchorQIndex a b c d) ≠ 0)
    :
    ∀ a b c d, valid a b c d → extractLambdaFromInput Q Y a b c d = lam a b c d := by
  intro a b c d hvalid
  unfold extractLambdaFromInput
  have hscale : Y (anchorQIndex a b c d) = lam a b c d * Q (anchorQIndex a b c d) := by
    exact hScale (anchorQIndex a b c d) hvalid
  rw [hscale]
  have hq : Q (anchorQIndex a b c d) ≠ 0 := hQNZ a b c d hvalid
  simpa [mul_comm] using (mul_div_cancel_left₀ (lam a b c d) hq)

theorem extractLambdaFromInput_nonzero
    {n : Nat}
    (Q Y : InputVector n)
    (lam : Lambda n)
    (hScale : isScaledInput Y lam Q)
    (hQNZ : ∀ a b c d, valid a b c d → Q (anchorQIndex a b c d) ≠ 0)
    (hLamNZ : nonzeroOnValid lam) :
    nonzeroOnValid (extractLambdaFromInput Q Y) := by
  intro a b c d hvalid
  have heq := extractLambdaFromInput_eq Q Y lam hScale hQNZ a b c d hvalid
  rw [heq]
  exact hLamNZ a b c d hvalid

end Question9
