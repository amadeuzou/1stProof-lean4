import Question9.Main

namespace Question9

/-!
`HFamily` packages the three bilinear identity families (`h1`,`h2`,`h3`)
as an explicit finite coordinate map.

This gives a concrete quadratic map on `Lambda n` whose vanishing is
equivalent to `separable` under `nonzeroOnValid`.
-/

noncomputable section

abbrev ValidQuad (n : Nat) :=
  {q : Idx n × Idx n × Idx n × Idx n // valid q.1 q.2.1 q.2.2.1 q.2.2.2}

noncomputable instance instFintypeValidQuad (n : Nat) : Fintype (ValidQuad n) := by
  exact Fintype.ofFinite (ValidQuad n)

namespace ValidQuad

def a {n : Nat} (q : ValidQuad n) : Idx n := q.1.1
def b {n : Nat} (q : ValidQuad n) : Idx n := q.1.2.1
def c {n : Nat} (q : ValidQuad n) : Idx n := q.1.2.2.1
def d {n : Nat} (q : ValidQuad n) : Idx n := q.1.2.2.2

theorem hvalid {n : Nat} (q : ValidQuad n) : valid (a q) (b q) (c q) (d q) := q.2

end ValidQuad

inductive HConditionIndex (n : Nat) where
  | h1 : ValidQuad n → HConditionIndex n
  | h2 : Idx n → Idx n → HConditionIndex n
  | h3 : Idx n → Idx n → HConditionIndex n
deriving DecidableEq

noncomputable instance instFintypeHConditionIndex (n : Nat) : Fintype (HConditionIndex n) := by
  classical
  let e : HConditionIndex n ≃ Sum (ValidQuad n) (Sum (Idx n × Idx n) (Idx n × Idx n)) := {
    toFun := fun idx =>
      match idx with
      | HConditionIndex.h1 q => Sum.inl q
      | HConditionIndex.h2 a b => Sum.inr (Sum.inl (a, b))
      | HConditionIndex.h3 c d => Sum.inr (Sum.inr (c, d))
    invFun := fun x =>
      match x with
      | Sum.inl q => HConditionIndex.h1 q
      | Sum.inr (Sum.inl ab) => HConditionIndex.h2 ab.1 ab.2
      | Sum.inr (Sum.inr cd) => HConditionIndex.h3 cd.1 cd.2
    left_inv := by
      intro idx
      cases idx <;> rfl
    right_inv := by
      intro x
      cases x with
      | inl q => rfl
      | inr s =>
          cases s with
          | inl ab => (cases ab; rfl)
          | inr cd => (cases cd; rfl)
  }
  exact Fintype.ofEquiv
    (Sum (ValidQuad n) (Sum (Idx n × Idx n) (Idx n × Idx n)))
    e.symm

def hConditionResidualWithAnchors
    {n : Nat}
    (S : Anchors n)
    (lam : Lambda n) :
    HConditionIndex n → ℝ
  | .h1 q =>
      lam (ValidQuad.a q) (ValidQuad.b q) (ValidQuad.c q) (ValidQuad.d q) * lam S.a0 S.b0 S.c0 S.d0
        - lam (ValidQuad.a q) (ValidQuad.b q) S.c0 S.d0 * lam S.a0 S.b0 (ValidQuad.c q) (ValidQuad.d q)
  | .h2 a b =>
      lam a b S.c0 S.d0 * lam S.a0 S.b0 S.c0 S.d0
        - lam a S.b0 S.c0 S.d0 * lam S.a0 b S.c0 S.d0
  | .h3 c d =>
      lam S.a0 S.b0 c d * lam S.a0 S.b0 S.c0 S.d0
        - lam S.a0 S.b0 c S.d0 * lam S.a0 S.b0 S.c0 d

theorem hConditionResidual_zero_iff_hConditionSet
    {n : Nat}
    (S : Anchors n)
    (lam : Lambda n) :
    (∀ idx, hConditionResidualWithAnchors S lam idx = 0) ↔ HConditionSet S lam := by
  constructor
  · intro hZero
    refine ⟨?_, ?_, ?_⟩
    · intro a b c d hvalid
      let q : ValidQuad n := ⟨(a, b, c, d), hvalid⟩
      have hz : hConditionResidualWithAnchors S lam (.h1 q) = 0 := hZero (.h1 q)
      exact sub_eq_zero.mp (by simpa [hConditionResidualWithAnchors, q] using hz)
    · intro a b
      have hz : hConditionResidualWithAnchors S lam (.h2 a b) = 0 := hZero (.h2 a b)
      exact sub_eq_zero.mp (by simpa [hConditionResidualWithAnchors] using hz)
    · intro c d
      have hz : hConditionResidualWithAnchors S lam (.h3 c d) = 0 := hZero (.h3 c d)
      exact sub_eq_zero.mp (by simpa [hConditionResidualWithAnchors] using hz)
  · intro hH idx
    cases idx with
    | h1 q =>
        exact sub_eq_zero.mpr (hH.h1 (ValidQuad.a q) (ValidQuad.b q) (ValidQuad.c q) (ValidQuad.d q) (ValidQuad.hvalid q))
    | h2 a b =>
        exact sub_eq_zero.mpr (hH.h2 a b)
    | h3 c d =>
        exact sub_eq_zero.mpr (hH.h3 c d)

theorem hConditionResidual_zero_iff_separable
    {n : Nat}
    (S : Anchors n)
    (lam : Lambda n)
    (hNZ : nonzeroOnValid lam) :
    (∀ idx, hConditionResidualWithAnchors S lam idx = 0) ↔ separable lam := by
  exact (hConditionResidual_zero_iff_hConditionSet S lam).trans
    (hConditionSet_iff_separable S lam hNZ)

noncomputable def hConditionResidualFinWithAnchors
    {n : Nat}
    (S : Anchors n)
    (lam : Lambda n) :
    Fin (Fintype.card (HConditionIndex n)) → ℝ :=
  fun t => hConditionResidualWithAnchors S lam ((Fintype.equivFin (HConditionIndex n)).symm t)

noncomputable def hConditionResidualFin
    (n : Nat)
    (hn : 5 ≤ n)
    (lam : Lambda n) :
    Fin (Fintype.card (HConditionIndex n)) → ℝ :=
  hConditionResidualFinWithAnchors (canonicalAnchors n hn) lam

theorem hConditionResidualFin_zero_iff_separable
    {n : Nat}
    (hn : 5 ≤ n)
    (lam : Lambda n)
    (hNZ : nonzeroOnValid lam) :
    (∀ t, hConditionResidualFin n hn lam t = 0) ↔ separable lam := by
  constructor
  · intro hZero
    have hZero' :
        ∀ idx, hConditionResidualWithAnchors (canonicalAnchors n hn) lam idx = 0 := by
      intro idx
      have hz := hZero ((Fintype.equivFin (HConditionIndex n)) idx)
      simpa [hConditionResidualFin, hConditionResidualFinWithAnchors] using hz
    exact (hConditionResidual_zero_iff_separable (canonicalAnchors n hn) lam hNZ).1 hZero'
  · intro hSep t
    have hZero :
        ∀ idx, hConditionResidualWithAnchors (canonicalAnchors n hn) lam idx = 0 := by
      exact (hConditionResidual_zero_iff_separable (canonicalAnchors n hn) lam hNZ).2 hSep
    have hz := hZero ((Fintype.equivFin (HConditionIndex n)).symm t)
    simpa [hConditionResidualFin, hConditionResidualFinWithAnchors] using hz

theorem concrete_hConditionResidualFin_characterization_of_genericStrong
    {n : Nat}
    (hn : 5 ≤ n)
    (A : CameraMatrices n)
    (Y : InputVector n)
    (lam : Lambda n)
    (hScale : isScaledInput Y lam (QInput A))
    (hGeneric : IsGenericStrong A)
    (hLamNZ : nonzeroOnValid lam) :
    (∀ t, hConditionResidualFin n hn (extractLambdaFromInput (QInput A) Y) t = 0) ↔
      separable (extractLambdaFromInput (QInput A) Y) := by
  have hQNZ : ∀ a b c d, valid a b c d → QInput A (anchorQIndex a b c d) ≠ 0 := by
    exact anchor_nonzero_of_isGeneric A (isGenericStrong_implies_isGeneric A hGeneric)
  have hExtractNZ : nonzeroOnValid (extractLambdaFromInput (QInput A) Y) := by
    exact extractLambdaFromInput_nonzero (QInput A) Y lam hScale hQNZ hLamNZ
  exact hConditionResidualFin_zero_iff_separable hn (extractLambdaFromInput (QInput A) Y) hExtractNZ

def hConditionCoordinateDegree : Nat := 2

theorem hConditionCoordinateDegree_eq : hConditionCoordinateDegree = 2 := rfl

theorem exists_uniform_quadratic_hCondition_map
    (n : Nat)
    (hn : 5 ≤ n) :
    ∃ m : Nat, ∃ F : Lambda n → (Fin m → ℝ),
      (hConditionCoordinateDegree = 2) ∧
      (∀ lam, nonzeroOnValid lam → ((∀ t, F lam t = 0) ↔ separable lam)) := by
  refine ⟨Fintype.card (HConditionIndex n), hConditionResidualFin n hn, hConditionCoordinateDegree_eq, ?_⟩
  intro lam hNZ
  exact hConditionResidualFin_zero_iff_separable hn lam hNZ

end

end Question9
