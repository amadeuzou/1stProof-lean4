import Mathlib

namespace Question9

abbrev Idx (n : Nat) := Fin n
abbrev Lambda (n : Nat) := Idx n → Idx n → Idx n → Idx n → ℝ

def valid {n : Nat} (a b c d : Idx n) : Prop :=
  ¬ (a = b ∧ b = c ∧ c = d)

def nonzeroOnValid {n : Nat} (lam : Lambda n) : Prop :=
  ∀ a b c d, valid a b c d → lam a b c d ≠ 0

def swap12Lambda {n : Nat} (lam : Lambda n) : Lambda n :=
  fun a b c d => lam b a c d

def swap13Lambda {n : Nat} (lam : Lambda n) : Lambda n :=
  fun a b c d => lam c b a d

def swap34Lambda {n : Nat} (lam : Lambda n) : Lambda n :=
  fun a b c d => lam a b d c

def separable {n : Nat} (lam : Lambda n) : Prop :=
  ∃ u v w x : Idx n → ℝ,
    (∀ i, u i ≠ 0) ∧ (∀ i, v i ≠ 0) ∧ (∀ i, w i ≠ 0) ∧ (∀ i, x i ≠ 0) ∧
      (∀ a b c d, valid a b c d → lam a b c d = u a * v b * w c * x d)

theorem valid_swap12_iff
    {n : Nat}
    (a b c d : Idx n) :
    valid b a c d ↔ valid a b c d := by
  constructor <;> intro hvalid <;> intro hall
  · apply hvalid
    exact ⟨hall.1.symm, hall.1.trans hall.2.1, hall.2.2⟩
  · apply hvalid
    exact ⟨hall.1.symm, hall.1.trans hall.2.1, hall.2.2⟩

theorem valid_swap13_iff
    {n : Nat}
    (a b c d : Idx n) :
    valid c b a d ↔ valid a b c d := by
  constructor <;> intro hvalid <;> intro hall
  · apply hvalid
    exact ⟨hall.2.1.symm, hall.1.symm, (hall.1.trans hall.2.1).trans hall.2.2⟩
  · apply hvalid
    exact ⟨hall.2.1.symm, hall.1.symm, (hall.1.trans hall.2.1).trans hall.2.2⟩

theorem valid_swap34_iff
    {n : Nat}
    (a b c d : Idx n) :
    valid a b d c ↔ valid a b c d := by
  constructor <;> intro hvalid <;> intro hall
  · apply hvalid
    exact ⟨hall.1, hall.2.1.trans hall.2.2, hall.2.2.symm⟩
  · apply hvalid
    exact ⟨hall.1, hall.2.1.trans hall.2.2, hall.2.2.symm⟩

theorem nonzeroOnValid_swap12
    {n : Nat}
    (lam : Lambda n)
    (hNZ : nonzeroOnValid lam) :
    nonzeroOnValid (swap12Lambda lam) := by
  intro a b c d hvalid
  exact hNZ b a c d ((valid_swap12_iff a b c d).2 hvalid)

theorem nonzeroOnValid_swap13
    {n : Nat}
    (lam : Lambda n)
    (hNZ : nonzeroOnValid lam) :
    nonzeroOnValid (swap13Lambda lam) := by
  intro a b c d hvalid
  exact hNZ c b a d ((valid_swap13_iff a b c d).2 hvalid)

theorem nonzeroOnValid_swap34
    {n : Nat}
    (lam : Lambda n)
    (hNZ : nonzeroOnValid lam) :
    nonzeroOnValid (swap34Lambda lam) := by
  intro a b c d hvalid
  exact hNZ a b d c ((valid_swap34_iff a b c d).2 hvalid)

@[simp] theorem swap12Lambda_swap12
    {n : Nat}
    (lam : Lambda n) :
    swap12Lambda (swap12Lambda lam) = lam := by
  funext a b c d
  rfl

@[simp] theorem swap13Lambda_swap13
    {n : Nat}
    (lam : Lambda n) :
    swap13Lambda (swap13Lambda lam) = lam := by
  funext a b c d
  rfl

@[simp] theorem swap34Lambda_swap34
    {n : Nat}
    (lam : Lambda n) :
    swap34Lambda (swap34Lambda lam) = lam := by
  funext a b c d
  rfl

theorem nonzeroOnValid_swap12_iff
    {n : Nat}
    (lam : Lambda n) :
    nonzeroOnValid (swap12Lambda lam) ↔ nonzeroOnValid lam := by
  constructor
  · intro h
    simpa [swap12Lambda_swap12] using nonzeroOnValid_swap12 (swap12Lambda lam) h
  · intro h
    exact nonzeroOnValid_swap12 lam h

theorem nonzeroOnValid_swap13_iff
    {n : Nat}
    (lam : Lambda n) :
    nonzeroOnValid (swap13Lambda lam) ↔ nonzeroOnValid lam := by
  constructor
  · intro h
    simpa [swap13Lambda_swap13] using nonzeroOnValid_swap13 (swap13Lambda lam) h
  · intro h
    exact nonzeroOnValid_swap13 lam h

theorem nonzeroOnValid_swap34_iff
    {n : Nat}
    (lam : Lambda n) :
    nonzeroOnValid (swap34Lambda lam) ↔ nonzeroOnValid lam := by
  constructor
  · intro h
    simpa [swap34Lambda_swap34] using nonzeroOnValid_swap34 (swap34Lambda lam) h
  · intro h
    exact nonzeroOnValid_swap34 lam h

structure Anchors (n : Nat) where
  a0 : Idx n
  b0 : Idx n
  c0 : Idx n
  d0 : Idx n
  hab : a0 ≠ b0
  hbc : b0 ≠ c0
  hcd : c0 ≠ d0

namespace Anchors

variable {n : Nat} (S : Anchors n)

lemma valid_anchor : valid S.a0 S.b0 S.c0 S.d0 := by
  intro h
  exact S.hab h.1

lemma valid_a_slice (a : Idx n) : valid a S.b0 S.c0 S.d0 := by
  intro h
  exact S.hbc h.2.1

lemma valid_b_slice (b : Idx n) : valid S.a0 b S.c0 S.d0 := by
  intro h
  exact S.hcd h.2.2

lemma valid_c_slice (c : Idx n) : valid S.a0 S.b0 c S.d0 := by
  intro h
  exact S.hab h.1

lemma valid_d_slice (d : Idx n) : valid S.a0 S.b0 S.c0 d := by
  intro h
  exact S.hab h.1

end Anchors

def canonicalAnchors (n : Nat) (hn : 5 ≤ n) : Anchors n where
  a0 := ⟨0, by omega⟩
  b0 := ⟨1, by omega⟩
  c0 := ⟨2, by omega⟩
  d0 := ⟨3, by omega⟩
  hab := by simp
  hbc := by simp
  hcd := by simp

end Question9
