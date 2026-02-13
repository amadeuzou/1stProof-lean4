import Question9.Geometry

namespace Question9

structure PluckerPattern (n : Nat) where
  p1 : QIndex n
  p2 : QIndex n
  p3 : QIndex n
  p4 : QIndex n
  p5 : QIndex n
  p6 : QIndex n

def pluckerRel {n : Nat} (T : InputVector n) (P : PluckerPattern n) : ℝ :=
  T P.p1 * T P.p2 - T P.p3 * T P.p4 + T P.p5 * T P.p6

def RepeatedFirstTwo {n : Nat} (idx : QIndex n) : Prop :=
  idx.a = idx.b ∧ idx.i = idx.j

def swap12Index {n : Nat} (idx : QIndex n) : QIndex n where
  a := idx.b
  b := idx.a
  c := idx.c
  d := idx.d
  i := idx.j
  j := idx.i
  k := idx.k
  l := idx.l

def swap13Index {n : Nat} (idx : QIndex n) : QIndex n where
  a := idx.c
  b := idx.b
  c := idx.a
  d := idx.d
  i := idx.k
  j := idx.j
  k := idx.i
  l := idx.l

def swap34Index {n : Nat} (idx : QIndex n) : QIndex n where
  a := idx.a
  b := idx.b
  c := idx.d
  d := idx.c
  i := idx.i
  j := idx.j
  k := idx.l
  l := idx.k

theorem validIndex_swap12_iff
    {n : Nat}
    (idx : QIndex n) :
    validIndex (swap12Index idx) ↔ validIndex idx := by
  rcases idx with ⟨a, b, c, d, i, j, k, l⟩
  constructor
  · intro hvalid
    unfold validIndex valid at hvalid ⊢
    intro hall
    apply hvalid
    rcases hall with ⟨hab, hbc, hcd⟩
    refine ⟨hab.symm, ?_, hcd⟩
    exact hab.trans hbc
  · intro hvalid
    unfold validIndex valid at hvalid ⊢
    intro hall
    apply hvalid
    rcases hall with ⟨hba, hac, hcd⟩
    refine ⟨hba.symm, ?_, hcd⟩
    exact hba.trans hac

theorem validIndex_swap13_iff
    {n : Nat}
    (idx : QIndex n) :
    validIndex (swap13Index idx) ↔ validIndex idx := by
  rcases idx with ⟨a, b, c, d, i, j, k, l⟩
  constructor
  · intro hvalid
    unfold validIndex valid at hvalid ⊢
    intro hall
    apply hvalid
    rcases hall with ⟨hab, hbc, hcd⟩
    exact ⟨hbc.symm, hab.symm, (hab.trans hbc).trans hcd⟩
  · intro hvalid
    unfold validIndex valid at hvalid ⊢
    intro hall
    apply hvalid
    rcases hall with ⟨hcb, hba, had⟩
    exact ⟨hba.symm, hcb.symm, (hcb.trans hba).trans had⟩

theorem validIndex_swap34_iff
    {n : Nat}
    (idx : QIndex n) :
    validIndex (swap34Index idx) ↔ validIndex idx := by
  rcases idx with ⟨a, b, c, d, i, j, k, l⟩
  constructor <;> intro hvalid
  · unfold validIndex valid at hvalid ⊢
    intro hall
    apply hvalid
    rcases hall with ⟨hab, hbd, hdc⟩
    exact ⟨hab, hbd.trans hdc, hdc.symm⟩
  · unfold validIndex valid at hvalid ⊢
    intro hall
    apply hvalid
    rcases hall with ⟨hab, hbc, hcd⟩
    exact ⟨hab, hbc.trans hcd, hcd.symm⟩

theorem validIndex_swap12
    {n : Nat}
    (idx : QIndex n)
    (hvalid : validIndex idx) :
    validIndex (swap12Index idx) := by
  exact (validIndex_swap12_iff idx).2 hvalid

theorem validIndex_swap13
    {n : Nat}
    (idx : QIndex n)
    (hvalid : validIndex idx) :
    validIndex (swap13Index idx) := by
  exact (validIndex_swap13_iff idx).2 hvalid

theorem validIndex_swap34
    {n : Nat}
    (idx : QIndex n)
    (hvalid : validIndex idx) :
    validIndex (swap34Index idx) := by
  exact (validIndex_swap34_iff idx).2 hvalid

theorem qInput_swap12
    {n : Nat}
    (A : CameraMatrices n)
    (idx : QIndex n) :
    QInput A (swap12Index idx) = - QInput A idx := by
  rcases idx with ⟨a, b, c, d, i, j, k, l⟩
  simpa [swap12Index, QInput] using Q_entry_swap_first_two A a b c d i j k l

theorem qInput_swap13
    {n : Nat}
    (A : CameraMatrices n)
    (idx : QIndex n) :
    QInput A (swap13Index idx) = - QInput A idx := by
  rcases idx with ⟨a, b, c, d, i, j, k, l⟩
  simpa [swap13Index, QInput] using Q_entry_swap_first_third A a b c d i j k l

theorem qInput_swap34
    {n : Nat}
    (A : CameraMatrices n)
    (idx : QIndex n) :
    QInput A (swap34Index idx) = - QInput A idx := by
  rcases idx with ⟨a, b, c, d, i, j, k, l⟩
  simpa [swap34Index, QInput] using Q_entry_swap_third_fourth A a b c d i j k l

theorem qInput_zero_of_repeatedFirstTwo
    {n : Nat}
    (A : CameraMatrices n)
    (idx : QIndex n)
    (hRep : RepeatedFirstTwo idx) :
    QInput A idx = 0 := by
  rcases idx with ⟨a, b, c, d, i, j, k, l⟩
  rcases hRep with ⟨hab, hij⟩
  cases hab
  cases hij
  simpa [QInput] using Q_entry_zero_of_repeat_first_two A a c d i k l

theorem pluckerRel_qInput_zero_of_repeatedFactors
    {n : Nat}
    (A : CameraMatrices n)
    (P : PluckerPattern n)
    (h1 : RepeatedFirstTwo P.p1)
    (h3 : RepeatedFirstTwo P.p3)
    (h5 : RepeatedFirstTwo P.p5) :
    pluckerRel (QInput A) P = 0 := by
  have hp1 : QInput A P.p1 = 0 := qInput_zero_of_repeatedFirstTwo A P.p1 h1
  have hp3 : QInput A P.p3 = 0 := qInput_zero_of_repeatedFirstTwo A P.p3 h3
  have hp5 : QInput A P.p5 = 0 := qInput_zero_of_repeatedFirstTwo A P.p5 h5
  simp [pluckerRel, hp1, hp3, hp5]

theorem pluckerRel_qInput_zero_of_swap12
    {n : Nat}
    (A : CameraMatrices n)
    (P : PluckerPattern n)
    (h3 : P.p3 = swap12Index P.p1)
    (h4 : P.p4 = swap12Index P.p2)
    (h5 : RepeatedFirstTwo P.p5) :
    pluckerRel (QInput A) P = 0 := by
  have hp3 : QInput A P.p3 = -QInput A P.p1 := by
    simpa [h3] using qInput_swap12 A P.p1
  have hp4 : QInput A P.p4 = -QInput A P.p2 := by
    simpa [h4] using qInput_swap12 A P.p2
  have hp5 : QInput A P.p5 = 0 := qInput_zero_of_repeatedFirstTwo A P.p5 h5
  simp [pluckerRel, hp3, hp4, hp5, mul_assoc, mul_comm, mul_left_comm]

def lamAt {n : Nat} (lam : Lambda n) (idx : QIndex n) : ℝ :=
  lam idx.a idx.b idx.c idx.d

def Swap12CrossAligned {n : Nat} (P : PluckerPattern n) : Prop :=
  P.p2.a = P.p1.b ∧ P.p2.b = P.p1.a ∧
    P.p3 = swap12Index P.p1 ∧ P.p4 = swap12Index P.p2

def Swap13CrossAligned {n : Nat} (P : PluckerPattern n) : Prop :=
  P.p2.a = P.p1.c ∧ P.p2.c = P.p1.a ∧
    P.p3 = swap13Index P.p1 ∧ P.p4 = swap13Index P.p2

def Swap34CrossAligned {n : Nat} (P : PluckerPattern n) : Prop :=
  P.p2.c = P.p1.d ∧ P.p2.d = P.p1.c ∧
    P.p3 = swap34Index P.p1 ∧ P.p4 = swap34Index P.p2

def swap12Pattern {n : Nat} (p1 p2 p5 p6 : QIndex n) : PluckerPattern n where
  p1 := p1
  p2 := p2
  p3 := swap12Index p1
  p4 := swap12Index p2
  p5 := p5
  p6 := p6

theorem swap12Pattern_crossAligned
    {n : Nat}
    (p1 p2 p5 p6 : QIndex n)
    (h2a : p2.a = p1.b)
    (h2b : p2.b = p1.a) :
    Swap12CrossAligned (swap12Pattern p1 p2 p5 p6) := by
  exact ⟨h2a, h2b, rfl, rfl⟩

def swap13Pattern {n : Nat} (p1 p2 p5 p6 : QIndex n) : PluckerPattern n where
  p1 := p1
  p2 := p2
  p3 := swap13Index p1
  p4 := swap13Index p2
  p5 := p5
  p6 := p6

theorem swap13Pattern_crossAligned
    {n : Nat}
    (p1 p2 p5 p6 : QIndex n)
    (h2a : p2.a = p1.c)
    (h2c : p2.c = p1.a) :
    Swap13CrossAligned (swap13Pattern p1 p2 p5 p6) := by
  exact ⟨h2a, h2c, rfl, rfl⟩

def swap34Pattern {n : Nat} (p1 p2 p5 p6 : QIndex n) : PluckerPattern n where
  p1 := p1
  p2 := p2
  p3 := swap34Index p1
  p4 := swap34Index p2
  p5 := p5
  p6 := p6

theorem swap34Pattern_crossAligned
    {n : Nat}
    (p1 p2 p5 p6 : QIndex n)
    (h2c : p2.c = p1.d)
    (h2d : p2.d = p1.c) :
    Swap34CrossAligned (swap34Pattern p1 p2 p5 p6) := by
  exact ⟨h2c, h2d, rfl, rfl⟩

def PluckerBalanced {n : Nat} (lam : Lambda n) (P : PluckerPattern n) : Prop :=
  lamAt lam P.p1 * lamAt lam P.p2 = lamAt lam P.p3 * lamAt lam P.p4 ∧
    lamAt lam P.p1 * lamAt lam P.p2 = lamAt lam P.p5 * lamAt lam P.p6

def PatternValid {n : Nat} (P : PluckerPattern n) : Prop :=
  validIndex P.p1 ∧ validIndex P.p2 ∧ validIndex P.p3 ∧
    validIndex P.p4 ∧ validIndex P.p5 ∧ validIndex P.p6

theorem swap12Pattern_valid
    {n : Nat}
    (p1 p2 p5 p6 : QIndex n)
    (h1 : validIndex p1)
    (h2 : validIndex p2)
    (h5 : validIndex p5)
    (h6 : validIndex p6) :
    PatternValid (swap12Pattern p1 p2 p5 p6) := by
  refine ⟨h1, h2, validIndex_swap12 p1 h1, validIndex_swap12 p2 h2, h5, h6⟩

theorem swap13Pattern_valid
    {n : Nat}
    (p1 p2 p5 p6 : QIndex n)
    (h1 : validIndex p1)
    (h2 : validIndex p2)
    (h5 : validIndex p5)
    (h6 : validIndex p6) :
    PatternValid (swap13Pattern p1 p2 p5 p6) := by
  refine ⟨h1, h2, validIndex_swap13 p1 h1, validIndex_swap13 p2 h2, h5, h6⟩

theorem swap34Pattern_valid
    {n : Nat}
    (p1 p2 p5 p6 : QIndex n)
    (h1 : validIndex p1)
    (h2 : validIndex p2)
    (h5 : validIndex p5)
    (h6 : validIndex p6) :
    PatternValid (swap34Pattern p1 p2 p5 p6) := by
  refine ⟨h1, h2, validIndex_swap34 p1 h1, validIndex_swap34 p2 h2, h5, h6⟩

def repeatedCoreIndex {n : Nat} (S : Anchors n) : QIndex n where
  a := S.a0
  b := S.a0
  c := S.b0
  d := S.c0
  i := rowAnchor
  j := rowAnchor
  k := rowAnchor
  l := rowAnchor

theorem repeatedCoreIndex_valid
    {n : Nat}
    (S : Anchors n) :
    validIndex (repeatedCoreIndex S) := by
  unfold validIndex repeatedCoreIndex valid
  intro h
  exact S.hbc h.2.2

theorem repeatedCoreIndex_repeatedFirstTwo
    {n : Nat}
    (S : Anchors n) :
    RepeatedFirstTwo (repeatedCoreIndex S) := by
  simp [RepeatedFirstTwo, repeatedCoreIndex]

def repeatedPattern {n : Nat} (S : Anchors n) : PluckerPattern n where
  p1 := repeatedCoreIndex S
  p2 := repeatedCoreIndex S
  p3 := repeatedCoreIndex S
  p4 := repeatedCoreIndex S
  p5 := repeatedCoreIndex S
  p6 := repeatedCoreIndex S

def ModeAligned {n : Nat} (P : PluckerPattern n) : Prop :=
  P.p1.a = P.p3.a ∧ P.p1.a = P.p5.a ∧ P.p2.a = P.p4.a ∧ P.p2.a = P.p6.a ∧
    P.p1.b = P.p3.b ∧ P.p1.b = P.p5.b ∧ P.p2.b = P.p4.b ∧ P.p2.b = P.p6.b ∧
    P.p1.c = P.p3.c ∧ P.p1.c = P.p5.c ∧ P.p2.c = P.p4.c ∧ P.p2.c = P.p6.c ∧
    P.p1.d = P.p3.d ∧ P.p1.d = P.p5.d ∧ P.p2.d = P.p4.d ∧ P.p2.d = P.p6.d

theorem repeatedPattern_valid
    {n : Nat}
    (S : Anchors n) :
    PatternValid (repeatedPattern S) := by
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩ <;> simpa [repeatedPattern] using repeatedCoreIndex_valid S

theorem repeatedPattern_modeAligned
    {n : Nat}
    (S : Anchors n) :
    ModeAligned (repeatedPattern S) := by
  simp [ModeAligned, repeatedPattern]

theorem repeatedPattern_rep1
    {n : Nat}
    (S : Anchors n) :
    RepeatedFirstTwo (repeatedPattern S).p1 := by
  exact repeatedCoreIndex_repeatedFirstTwo S

theorem repeatedPattern_rep3
    {n : Nat}
    (S : Anchors n) :
    RepeatedFirstTwo (repeatedPattern S).p3 := by
  exact repeatedCoreIndex_repeatedFirstTwo S

theorem repeatedPattern_rep5
    {n : Nat}
    (S : Anchors n) :
    RepeatedFirstTwo (repeatedPattern S).p5 := by
  exact repeatedCoreIndex_repeatedFirstTwo S

theorem swap12_pairBalanced_of_separable
    {n : Nat}
    (lam : Lambda n)
    (P : PluckerPattern n)
    (hsep : separable lam)
    (hValid : PatternValid P)
    (hCross : Swap12CrossAligned P) :
    lamAt lam P.p1 * lamAt lam P.p2 = lamAt lam P.p3 * lamAt lam P.p4 := by
  rcases hsep with ⟨u, v, w, x, hu, hv, hw, hx, hform⟩
  rcases hValid with ⟨hv1, hv2, hv3, hv4, hv5, hv6⟩
  rcases hCross with ⟨h2a, h2b, h3, h4⟩
  have hp1 : lamAt lam P.p1 = u P.p1.a * v P.p1.b * w P.p1.c * x P.p1.d := by
    exact hform P.p1.a P.p1.b P.p1.c P.p1.d hv1
  have hp2 : lamAt lam P.p2 = u P.p2.a * v P.p2.b * w P.p2.c * x P.p2.d := by
    exact hform P.p2.a P.p2.b P.p2.c P.p2.d hv2
  have hp3 : lamAt lam P.p3 = u P.p1.b * v P.p1.a * w P.p1.c * x P.p1.d := by
    have htmp : lamAt lam P.p3 = u P.p3.a * v P.p3.b * w P.p3.c * x P.p3.d := by
      exact hform P.p3.a P.p3.b P.p3.c P.p3.d hv3
    simpa [lamAt, h3, swap12Index] using htmp
  have hp4 : lamAt lam P.p4 = u P.p2.b * v P.p2.a * w P.p2.c * x P.p2.d := by
    have htmp : lamAt lam P.p4 = u P.p4.a * v P.p4.b * w P.p4.c * x P.p4.d := by
      exact hform P.p4.a P.p4.b P.p4.c P.p4.d hv4
    simpa [lamAt, h4, swap12Index] using htmp
  simp [hp1, hp2, hp3, hp4, h2a, h2b, mul_assoc, mul_left_comm, mul_comm]

theorem swap13_pairBalanced_of_separable
    {n : Nat}
    (lam : Lambda n)
    (P : PluckerPattern n)
    (hsep : separable lam)
    (hValid : PatternValid P)
    (hCross : Swap13CrossAligned P) :
    lamAt lam P.p1 * lamAt lam P.p2 = lamAt lam P.p3 * lamAt lam P.p4 := by
  rcases hsep with ⟨u, v, w, x, hu, hv, hw, hx, hform⟩
  rcases hValid with ⟨hv1, hv2, hv3, hv4, hv5, hv6⟩
  rcases hCross with ⟨h2a, h2c, h3, h4⟩
  have hp1 : lamAt lam P.p1 = u P.p1.a * v P.p1.b * w P.p1.c * x P.p1.d := by
    exact hform P.p1.a P.p1.b P.p1.c P.p1.d hv1
  have hp2 : lamAt lam P.p2 = u P.p2.a * v P.p2.b * w P.p2.c * x P.p2.d := by
    exact hform P.p2.a P.p2.b P.p2.c P.p2.d hv2
  have hp3 : lamAt lam P.p3 = u P.p1.c * v P.p1.b * w P.p1.a * x P.p1.d := by
    have htmp : lamAt lam P.p3 = u P.p3.a * v P.p3.b * w P.p3.c * x P.p3.d := by
      exact hform P.p3.a P.p3.b P.p3.c P.p3.d hv3
    simpa [lamAt, h3, swap13Index] using htmp
  have hp4 : lamAt lam P.p4 = u P.p2.c * v P.p2.b * w P.p2.a * x P.p2.d := by
    have htmp : lamAt lam P.p4 = u P.p4.a * v P.p4.b * w P.p4.c * x P.p4.d := by
      exact hform P.p4.a P.p4.b P.p4.c P.p4.d hv4
    simpa [lamAt, h4, swap13Index] using htmp
  simp [hp1, hp2, hp3, hp4, h2a, h2c, mul_assoc, mul_left_comm, mul_comm]

theorem swap34_pairBalanced_of_separable
    {n : Nat}
    (lam : Lambda n)
    (P : PluckerPattern n)
    (hsep : separable lam)
    (hValid : PatternValid P)
    (hCross : Swap34CrossAligned P) :
    lamAt lam P.p1 * lamAt lam P.p2 = lamAt lam P.p3 * lamAt lam P.p4 := by
  rcases hsep with ⟨u, v, w, x, hu, hv, hw, hx, hform⟩
  rcases hValid with ⟨hv1, hv2, hv3, hv4, hv5, hv6⟩
  rcases hCross with ⟨h2c, h2d, h3, h4⟩
  have hp1 : lamAt lam P.p1 = u P.p1.a * v P.p1.b * w P.p1.c * x P.p1.d := by
    exact hform P.p1.a P.p1.b P.p1.c P.p1.d hv1
  have hp2 : lamAt lam P.p2 = u P.p2.a * v P.p2.b * w P.p2.c * x P.p2.d := by
    exact hform P.p2.a P.p2.b P.p2.c P.p2.d hv2
  have hp3 : lamAt lam P.p3 = u P.p1.a * v P.p1.b * w P.p1.d * x P.p1.c := by
    have htmp : lamAt lam P.p3 = u P.p3.a * v P.p3.b * w P.p3.c * x P.p3.d := by
      exact hform P.p3.a P.p3.b P.p3.c P.p3.d hv3
    simpa [lamAt, h3, swap34Index] using htmp
  have hp4 : lamAt lam P.p4 = u P.p2.a * v P.p2.b * w P.p2.d * x P.p2.c := by
    have htmp : lamAt lam P.p4 = u P.p4.a * v P.p4.b * w P.p4.c * x P.p4.d := by
      exact hform P.p4.a P.p4.b P.p4.c P.p4.d hv4
    simpa [lamAt, h4, swap34Index] using htmp
  simp [hp1, hp2, hp3, hp4, h2c, h2d, mul_assoc, mul_left_comm, mul_comm]

theorem balanced_of_separable
    {n : Nat}
    (lam : Lambda n)
    (P : PluckerPattern n)
    (hsep : separable lam)
    (hValid : PatternValid P)
    (hAlign : ModeAligned P) :
    PluckerBalanced lam P := by
  rcases hsep with ⟨u, v, w, x, hu, hv, hw, hx, hform⟩
  rcases hValid with ⟨hv1, hv2, hv3, hv4, hv5, hv6⟩
  rcases hAlign with
    ⟨ha13, ha15, ha24, ha26, hb13, hb15, hb24, hb26,
      hc13, hc15, hc24, hc26, hd13, hd15, hd24, hd26⟩
  have hp1 : lamAt lam P.p1 = u P.p1.a * v P.p1.b * w P.p1.c * x P.p1.d := by
    exact hform P.p1.a P.p1.b P.p1.c P.p1.d hv1
  have hp2 : lamAt lam P.p2 = u P.p2.a * v P.p2.b * w P.p2.c * x P.p2.d := by
    exact hform P.p2.a P.p2.b P.p2.c P.p2.d hv2
  have hp3 : lamAt lam P.p3 = u P.p3.a * v P.p3.b * w P.p3.c * x P.p3.d := by
    exact hform P.p3.a P.p3.b P.p3.c P.p3.d hv3
  have hp4 : lamAt lam P.p4 = u P.p4.a * v P.p4.b * w P.p4.c * x P.p4.d := by
    exact hform P.p4.a P.p4.b P.p4.c P.p4.d hv4
  have hp5 : lamAt lam P.p5 = u P.p5.a * v P.p5.b * w P.p5.c * x P.p5.d := by
    exact hform P.p5.a P.p5.b P.p5.c P.p5.d hv5
  have hp6 : lamAt lam P.p6 = u P.p6.a * v P.p6.b * w P.p6.c * x P.p6.d := by
    exact hform P.p6.a P.p6.b P.p6.c P.p6.d hv6
  constructor
  · simp [hp1, hp2, hp3, hp4, ha13, ha24, hb13, hb24, hc13, hc24, hd13, hd24]
  · simp [hp1, hp2, hp5, hp6, ha15, ha26, hb15, hb26, hc15, hc26, hd15, hd26]

theorem pluckerRel_scale_of_balanced
    {n : Nat}
    (lam : Lambda n)
    (T : InputVector n)
    (P : PluckerPattern n)
    (hBal : PluckerBalanced lam P)
    (hBase : pluckerRel T P = 0) :
    pluckerRel (scaleInput lam T) P = 0 := by
  rcases hBal with ⟨h34, h56⟩
  have hscale :
      pluckerRel (scaleInput lam T) P =
        (lamAt lam P.p1 * lamAt lam P.p2) * (T P.p1 * T P.p2)
          - (lamAt lam P.p3 * lamAt lam P.p4) * (T P.p3 * T P.p4)
          + (lamAt lam P.p5 * lamAt lam P.p6) * (T P.p5 * T P.p6) := by
    simp [pluckerRel, scaleInput, lamAt, mul_assoc, mul_left_comm, mul_comm]
  rw [hscale, h34.symm, h56.symm]
  have hbase' : T P.p1 * T P.p2 - T P.p3 * T P.p4 + T P.p5 * T P.p6 = 0 := by
    simpa [pluckerRel] using hBase
  have hfactor :
      (lamAt lam P.p1 * lamAt lam P.p2) * (T P.p1 * T P.p2)
        - (lamAt lam P.p1 * lamAt lam P.p2) * (T P.p3 * T P.p4)
        + (lamAt lam P.p1 * lamAt lam P.p2) * (T P.p5 * T P.p6)
      =
      (lamAt lam P.p1 * lamAt lam P.p2) *
        (T P.p1 * T P.p2 - T P.p3 * T P.p4 + T P.p5 * T P.p6) := by
    ring
  rw [hfactor, hbase']
  ring

def pluckerMap {n m : Nat} (patterns : Fin m → PluckerPattern n) (T : InputVector n) : Fin m → ℝ :=
  fun t => pluckerRel T (patterns t)

def pluckerCoordinateDegree : Nat := 2

theorem pluckerCoordinateDegree_eq : pluckerCoordinateDegree = 2 := rfl

theorem plucker_degree_independent_of_n : pluckerCoordinateDegree = 2 := rfl

theorem plucker_map_independent_of_A {n m : Nat} (patterns : Fin m → PluckerPattern n) :
    ∃ F : InputVector n → (Fin m → ℝ), ∀ T, F T = pluckerMap patterns T := by
  refine ⟨pluckerMap patterns, ?_⟩
  intro T
  rfl

theorem plucker_forward_of_separable_for_family
    {n m : Nat}
    (patterns : Fin m → PluckerPattern n)
    (lam : Lambda n)
    (T : InputVector n)
    (hsep : separable lam)
    (hValid : ∀ t, PatternValid (patterns t))
    (hAlign : ∀ t, ModeAligned (patterns t))
    (hBaseZero : ∀ t, pluckerRel T (patterns t) = 0) :
    ∀ t, pluckerRel (scaleInput lam T) (patterns t) = 0 := by
  intro t
  have hBal : PluckerBalanced lam (patterns t) :=
    balanced_of_separable lam (patterns t) hsep (hValid t) (hAlign t)
  exact pluckerRel_scale_of_balanced lam T (patterns t) hBal (hBaseZero t)

theorem plucker_forward_of_separable_for_repeated_family
    {n m : Nat}
    (A : CameraMatrices n)
    (patterns : Fin m → PluckerPattern n)
    (lam : Lambda n)
    (hsep : separable lam)
    (hValid : ∀ t, PatternValid (patterns t))
    (hAlign : ∀ t, ModeAligned (patterns t))
    (hRep1 : ∀ t, RepeatedFirstTwo (patterns t).p1)
    (hRep3 : ∀ t, RepeatedFirstTwo (patterns t).p3)
    (hRep5 : ∀ t, RepeatedFirstTwo (patterns t).p5) :
    ∀ t, pluckerRel (scaleInput lam (QInput A)) (patterns t) = 0 := by
  apply plucker_forward_of_separable_for_family patterns lam (QInput A) hsep hValid hAlign
  intro t
  exact pluckerRel_qInput_zero_of_repeatedFactors A (patterns t) (hRep1 t) (hRep3 t) (hRep5 t)

theorem plucker_forward_of_separable_for_swap12_pattern
    {n : Nat}
    (A : CameraMatrices n)
    (lam : Lambda n)
    (P : PluckerPattern n)
    (hSep : separable lam)
    (hValid : PatternValid P)
    (hCross : Swap12CrossAligned P)
    (hRep5 : RepeatedFirstTwo P.p5) :
    pluckerRel (scaleInput lam (QInput A)) P = 0 := by
  rcases hCross with ⟨h2a, h2b, h3, h4⟩
  have hLamBal : lamAt lam P.p1 * lamAt lam P.p2 = lamAt lam P.p3 * lamAt lam P.p4 := by
    exact swap12_pairBalanced_of_separable lam P hSep hValid ⟨h2a, h2b, h3, h4⟩
  have hQ3 : QInput A P.p3 = -QInput A P.p1 := by
    simpa [h3] using qInput_swap12 A P.p1
  have hQ4 : QInput A P.p4 = -QInput A P.p2 := by
    simpa [h4] using qInput_swap12 A P.p2
  have hQ5 : QInput A P.p5 = 0 := qInput_zero_of_repeatedFirstTwo A P.p5 hRep5
  have hscale :
      pluckerRel (scaleInput lam (QInput A)) P =
        (lamAt lam P.p1 * lamAt lam P.p2) * (QInput A P.p1 * QInput A P.p2)
          - (lamAt lam P.p3 * lamAt lam P.p4) * (QInput A P.p3 * QInput A P.p4)
          + (lamAt lam P.p5 * lamAt lam P.p6) * (QInput A P.p5 * QInput A P.p6) := by
    simp [pluckerRel, scaleInput, lamAt, mul_assoc, mul_left_comm, mul_comm]
  rw [hscale, hLamBal, hQ3, hQ4, hQ5]
  ring

theorem plucker_forward_of_separable_for_swap13_pattern
    {n : Nat}
    (A : CameraMatrices n)
    (lam : Lambda n)
    (P : PluckerPattern n)
    (hSep : separable lam)
    (hValid : PatternValid P)
    (hCross : Swap13CrossAligned P)
    (hRep5 : RepeatedFirstTwo P.p5) :
    pluckerRel (scaleInput lam (QInput A)) P = 0 := by
  rcases hCross with ⟨h2a, h2c, h3, h4⟩
  have hLamBal : lamAt lam P.p1 * lamAt lam P.p2 = lamAt lam P.p3 * lamAt lam P.p4 := by
    exact swap13_pairBalanced_of_separable lam P hSep hValid ⟨h2a, h2c, h3, h4⟩
  have hQ3 : QInput A P.p3 = -QInput A P.p1 := by
    simpa [h3] using qInput_swap13 A P.p1
  have hQ4 : QInput A P.p4 = -QInput A P.p2 := by
    simpa [h4] using qInput_swap13 A P.p2
  have hQ5 : QInput A P.p5 = 0 := qInput_zero_of_repeatedFirstTwo A P.p5 hRep5
  have hscale :
      pluckerRel (scaleInput lam (QInput A)) P =
        (lamAt lam P.p1 * lamAt lam P.p2) * (QInput A P.p1 * QInput A P.p2)
          - (lamAt lam P.p3 * lamAt lam P.p4) * (QInput A P.p3 * QInput A P.p4)
          + (lamAt lam P.p5 * lamAt lam P.p6) * (QInput A P.p5 * QInput A P.p6) := by
    simp [pluckerRel, scaleInput, lamAt, mul_assoc, mul_left_comm, mul_comm]
  rw [hscale, hLamBal, hQ3, hQ4, hQ5]
  ring

theorem plucker_forward_of_separable_for_swap34_pattern
    {n : Nat}
    (A : CameraMatrices n)
    (lam : Lambda n)
    (P : PluckerPattern n)
    (hSep : separable lam)
    (hValid : PatternValid P)
    (hCross : Swap34CrossAligned P)
    (hRep5 : RepeatedFirstTwo P.p5) :
    pluckerRel (scaleInput lam (QInput A)) P = 0 := by
  rcases hCross with ⟨h2c, h2d, h3, h4⟩
  have hLamBal : lamAt lam P.p1 * lamAt lam P.p2 = lamAt lam P.p3 * lamAt lam P.p4 := by
    exact swap34_pairBalanced_of_separable lam P hSep hValid ⟨h2c, h2d, h3, h4⟩
  have hQ3 : QInput A P.p3 = -QInput A P.p1 := by
    simpa [h3] using qInput_swap34 A P.p1
  have hQ4 : QInput A P.p4 = -QInput A P.p2 := by
    simpa [h4] using qInput_swap34 A P.p2
  have hQ5 : QInput A P.p5 = 0 := qInput_zero_of_repeatedFirstTwo A P.p5 hRep5
  have hscale :
      pluckerRel (scaleInput lam (QInput A)) P =
        (lamAt lam P.p1 * lamAt lam P.p2) * (QInput A P.p1 * QInput A P.p2)
          - (lamAt lam P.p3 * lamAt lam P.p4) * (QInput A P.p3 * QInput A P.p4)
          + (lamAt lam P.p5 * lamAt lam P.p6) * (QInput A P.p5 * QInput A P.p6) := by
    simp [pluckerRel, scaleInput, lamAt, mul_assoc, mul_left_comm, mul_comm]
  rw [hscale, hLamBal, hQ3, hQ4, hQ5]
  ring

theorem lambda_pairBalance_of_zero
    {n : Nat}
    (A : CameraMatrices n)
    (lam : Lambda n)
    (P : PluckerPattern n)
    (hZero : pluckerRel (scaleInput lam (QInput A)) P = 0)
    (hQpair :
      QInput A P.p3 * QInput A P.p4 =
        QInput A P.p1 * QInput A P.p2)
    (hQ5 : QInput A P.p5 = 0)
    (hQnz : QInput A P.p1 * QInput A P.p2 ≠ 0) :
    lamAt lam P.p1 * lamAt lam P.p2 = lamAt lam P.p3 * lamAt lam P.p4 := by
  have hzero' :
      (lamAt lam P.p1 * lamAt lam P.p2) * (QInput A P.p1 * QInput A P.p2)
        - (lamAt lam P.p3 * lamAt lam P.p4) * (QInput A P.p3 * QInput A P.p4) = 0 := by
    simpa [pluckerRel, scaleInput, lamAt, hQ5, mul_assoc, mul_left_comm, mul_comm] using hZero
  rw [hQpair] at hzero'
  have hmul :
      (lamAt lam P.p1 * lamAt lam P.p2 - lamAt lam P.p3 * lamAt lam P.p4) *
        (QInput A P.p1 * QInput A P.p2) = 0 := by
    nlinarith [hzero']
  have hdiff :
      lamAt lam P.p1 * lamAt lam P.p2 - lamAt lam P.p3 * lamAt lam P.p4 = 0 := by
    exact (mul_eq_zero.mp hmul).resolve_right hQnz
  exact sub_eq_zero.mp hdiff

theorem lambda_pairBalance_of_swap12_zero
    {n : Nat}
    (A : CameraMatrices n)
    (lam : Lambda n)
    (P : PluckerPattern n)
    (hZero : pluckerRel (scaleInput lam (QInput A)) P = 0)
    (h3 : P.p3 = swap12Index P.p1)
    (h4 : P.p4 = swap12Index P.p2)
    (hRep5 : RepeatedFirstTwo P.p5)
    (hQnz : QInput A P.p1 * QInput A P.p2 ≠ 0) :
    lamAt lam P.p1 * lamAt lam P.p2 = lamAt lam P.p3 * lamAt lam P.p4 := by
  have hQ3 : QInput A P.p3 = -QInput A P.p1 := by
    simpa [h3] using qInput_swap12 A P.p1
  have hQ4 : QInput A P.p4 = -QInput A P.p2 := by
    simpa [h4] using qInput_swap12 A P.p2
  have hQ5 : QInput A P.p5 = 0 := qInput_zero_of_repeatedFirstTwo A P.p5 hRep5
  have hQpair :
      QInput A P.p3 * QInput A P.p4 =
        QInput A P.p1 * QInput A P.p2 := by
    rw [hQ3, hQ4]
    ring
  exact lambda_pairBalance_of_zero A lam P hZero hQpair hQ5 hQnz

theorem lambda_pairBalance_of_swap13_zero
    {n : Nat}
    (A : CameraMatrices n)
    (lam : Lambda n)
    (P : PluckerPattern n)
    (hZero : pluckerRel (scaleInput lam (QInput A)) P = 0)
    (h3 : P.p3 = swap13Index P.p1)
    (h4 : P.p4 = swap13Index P.p2)
    (hRep5 : RepeatedFirstTwo P.p5)
    (hQnz : QInput A P.p1 * QInput A P.p2 ≠ 0) :
    lamAt lam P.p1 * lamAt lam P.p2 = lamAt lam P.p3 * lamAt lam P.p4 := by
  have hQ3 : QInput A P.p3 = -QInput A P.p1 := by
    simpa [h3] using qInput_swap13 A P.p1
  have hQ4 : QInput A P.p4 = -QInput A P.p2 := by
    simpa [h4] using qInput_swap13 A P.p2
  have hQ5 : QInput A P.p5 = 0 := qInput_zero_of_repeatedFirstTwo A P.p5 hRep5
  have hQpair :
      QInput A P.p3 * QInput A P.p4 =
        QInput A P.p1 * QInput A P.p2 := by
    rw [hQ3, hQ4]
    ring
  exact lambda_pairBalance_of_zero A lam P hZero hQpair hQ5 hQnz

theorem lambda_pairBalance_of_swap34_zero
    {n : Nat}
    (A : CameraMatrices n)
    (lam : Lambda n)
    (P : PluckerPattern n)
    (hZero : pluckerRel (scaleInput lam (QInput A)) P = 0)
    (h3 : P.p3 = swap34Index P.p1)
    (h4 : P.p4 = swap34Index P.p2)
    (hRep5 : RepeatedFirstTwo P.p5)
    (hQnz : QInput A P.p1 * QInput A P.p2 ≠ 0) :
    lamAt lam P.p1 * lamAt lam P.p2 = lamAt lam P.p3 * lamAt lam P.p4 := by
  have hQ3 : QInput A P.p3 = -QInput A P.p1 := by
    simpa [h3] using qInput_swap34 A P.p1
  have hQ4 : QInput A P.p4 = -QInput A P.p2 := by
    simpa [h4] using qInput_swap34 A P.p2
  have hQ5 : QInput A P.p5 = 0 := qInput_zero_of_repeatedFirstTwo A P.p5 hRep5
  have hQpair :
      QInput A P.p3 * QInput A P.p4 =
        QInput A P.p1 * QInput A P.p2 := by
    rw [hQ3, hQ4]
    ring
  exact lambda_pairBalance_of_zero A lam P hZero hQpair hQ5 hQnz

theorem plucker_zero_iff_lambda_pairBalance_of_swap12
    {n : Nat}
    (A : CameraMatrices n)
    (lam : Lambda n)
    (P : PluckerPattern n)
    (h3 : P.p3 = swap12Index P.p1)
    (h4 : P.p4 = swap12Index P.p2)
    (hRep5 : RepeatedFirstTwo P.p5)
    (hQnz : QInput A P.p1 * QInput A P.p2 ≠ 0) :
    pluckerRel (scaleInput lam (QInput A)) P = 0 ↔
      lamAt lam P.p1 * lamAt lam P.p2 = lamAt lam P.p3 * lamAt lam P.p4 := by
  constructor
  · intro hZero
    exact lambda_pairBalance_of_swap12_zero A lam P hZero h3 h4 hRep5 hQnz
  · intro hLamBal
    have hQ3 : QInput A P.p3 = -QInput A P.p1 := by
      simpa [h3] using qInput_swap12 A P.p1
    have hQ4 : QInput A P.p4 = -QInput A P.p2 := by
      simpa [h4] using qInput_swap12 A P.p2
    have hQ5 : QInput A P.p5 = 0 := qInput_zero_of_repeatedFirstTwo A P.p5 hRep5
    have hscale :
        pluckerRel (scaleInput lam (QInput A)) P =
          (lamAt lam P.p1 * lamAt lam P.p2) * (QInput A P.p1 * QInput A P.p2)
            - (lamAt lam P.p3 * lamAt lam P.p4) * (QInput A P.p3 * QInput A P.p4)
            + (lamAt lam P.p5 * lamAt lam P.p6) * (QInput A P.p5 * QInput A P.p6) := by
      simp [pluckerRel, scaleInput, lamAt, mul_assoc, mul_left_comm, mul_comm]
    rw [hscale, hLamBal, hQ3, hQ4, hQ5]
    ring

theorem plucker_zero_iff_lambda_pairBalance_of_swap13
    {n : Nat}
    (A : CameraMatrices n)
    (lam : Lambda n)
    (P : PluckerPattern n)
    (h3 : P.p3 = swap13Index P.p1)
    (h4 : P.p4 = swap13Index P.p2)
    (hRep5 : RepeatedFirstTwo P.p5)
    (hQnz : QInput A P.p1 * QInput A P.p2 ≠ 0) :
    pluckerRel (scaleInput lam (QInput A)) P = 0 ↔
      lamAt lam P.p1 * lamAt lam P.p2 = lamAt lam P.p3 * lamAt lam P.p4 := by
  constructor
  · intro hZero
    exact lambda_pairBalance_of_swap13_zero A lam P hZero h3 h4 hRep5 hQnz
  · intro hLamBal
    have hQ3 : QInput A P.p3 = -QInput A P.p1 := by
      simpa [h3] using qInput_swap13 A P.p1
    have hQ4 : QInput A P.p4 = -QInput A P.p2 := by
      simpa [h4] using qInput_swap13 A P.p2
    have hQ5 : QInput A P.p5 = 0 := qInput_zero_of_repeatedFirstTwo A P.p5 hRep5
    have hscale :
        pluckerRel (scaleInput lam (QInput A)) P =
          (lamAt lam P.p1 * lamAt lam P.p2) * (QInput A P.p1 * QInput A P.p2)
            - (lamAt lam P.p3 * lamAt lam P.p4) * (QInput A P.p3 * QInput A P.p4)
            + (lamAt lam P.p5 * lamAt lam P.p6) * (QInput A P.p5 * QInput A P.p6) := by
      simp [pluckerRel, scaleInput, lamAt, mul_assoc, mul_left_comm, mul_comm]
    rw [hscale, hLamBal, hQ3, hQ4, hQ5]
    ring

theorem plucker_zero_iff_lambda_pairBalance_of_swap34
    {n : Nat}
    (A : CameraMatrices n)
    (lam : Lambda n)
    (P : PluckerPattern n)
    (h3 : P.p3 = swap34Index P.p1)
    (h4 : P.p4 = swap34Index P.p2)
    (hRep5 : RepeatedFirstTwo P.p5)
    (hQnz : QInput A P.p1 * QInput A P.p2 ≠ 0) :
    pluckerRel (scaleInput lam (QInput A)) P = 0 ↔
      lamAt lam P.p1 * lamAt lam P.p2 = lamAt lam P.p3 * lamAt lam P.p4 := by
  constructor
  · intro hZero
    exact lambda_pairBalance_of_swap34_zero A lam P hZero h3 h4 hRep5 hQnz
  · intro hLamBal
    have hQ3 : QInput A P.p3 = -QInput A P.p1 := by
      simpa [h3] using qInput_swap34 A P.p1
    have hQ4 : QInput A P.p4 = -QInput A P.p2 := by
      simpa [h4] using qInput_swap34 A P.p2
    have hQ5 : QInput A P.p5 = 0 := qInput_zero_of_repeatedFirstTwo A P.p5 hRep5
    have hscale :
        pluckerRel (scaleInput lam (QInput A)) P =
          (lamAt lam P.p1 * lamAt lam P.p2) * (QInput A P.p1 * QInput A P.p2)
            - (lamAt lam P.p3 * lamAt lam P.p4) * (QInput A P.p3 * QInput A P.p4)
            + (lamAt lam P.p5 * lamAt lam P.p6) * (QInput A P.p5 * QInput A P.p6) := by
      simp [pluckerRel, scaleInput, lamAt, mul_assoc, mul_left_comm, mul_comm]
    rw [hscale, hLamBal, hQ3, hQ4, hQ5]
    ring

theorem plucker_forward_of_separable_for_swap12_family
    {n m : Nat}
    (A : CameraMatrices n)
    (patterns : Fin m → PluckerPattern n)
    (lam : Lambda n)
    (hSep : separable lam)
    (hValid : ∀ t, PatternValid (patterns t))
    (hCross : ∀ t, Swap12CrossAligned (patterns t))
    (hRep5 : ∀ t, RepeatedFirstTwo (patterns t).p5) :
    ∀ t, pluckerRel (scaleInput lam (QInput A)) (patterns t) = 0 := by
  intro t
  exact plucker_forward_of_separable_for_swap12_pattern A lam (patterns t) hSep
    (hValid t) (hCross t) (hRep5 t)

theorem plucker_forward_of_separable_for_swap13_family
    {n m : Nat}
    (A : CameraMatrices n)
    (patterns : Fin m → PluckerPattern n)
    (lam : Lambda n)
    (hSep : separable lam)
    (hValid : ∀ t, PatternValid (patterns t))
    (hCross : ∀ t, Swap13CrossAligned (patterns t))
    (hRep5 : ∀ t, RepeatedFirstTwo (patterns t).p5) :
    ∀ t, pluckerRel (scaleInput lam (QInput A)) (patterns t) = 0 := by
  intro t
  exact plucker_forward_of_separable_for_swap13_pattern A lam (patterns t) hSep
    (hValid t) (hCross t) (hRep5 t)

theorem plucker_forward_of_separable_for_swap34_family
    {n m : Nat}
    (A : CameraMatrices n)
    (patterns : Fin m → PluckerPattern n)
    (lam : Lambda n)
    (hSep : separable lam)
    (hValid : ∀ t, PatternValid (patterns t))
    (hCross : ∀ t, Swap34CrossAligned (patterns t))
    (hRep5 : ∀ t, RepeatedFirstTwo (patterns t).p5) :
    ∀ t, pluckerRel (scaleInput lam (QInput A)) (patterns t) = 0 := by
  intro t
  exact plucker_forward_of_separable_for_swap34_pattern A lam (patterns t) hSep
    (hValid t) (hCross t) (hRep5 t)

end Question9
