import Mathlib.Topology.Covering
import Mathlib.GroupTheory.OrderOfElement

set_option autoImplicit false

universe u v w

namespace Question7

/-- `Γ` has an element of exact order `2`. -/
def HasTwoTorsion (Γ : Type u) [Group Γ] : Prop :=
  ∃ γ : Γ, orderOf γ = 2

/--
Topological fixed-point input used in the final obstruction:
every involutive self-homeomorphism has a fixed point.
-/
def HasInvolutiveHomeomorphFixedPointProperty (E : Type v) [TopologicalSpace E] : Prop :=
  ∀ g : E ≃ₜ E, Function.Involutive g → ∃ x : E, g x = x

/--
Typeclass packaging the fixed-point input (e.g. from Smith/Lefschetz theory)
used by the `Question7` obstruction argument.
-/
class InvolutionFixedPointInput (E : Type v) [TopologicalSpace E] : Prop where
  hasFixedPoint : HasInvolutiveHomeomorphFixedPointProperty E

/--
Abstract marker for spaces whose universal cover is `ℚ`-acyclic.
This is intentionally lightweight here; concrete homology-level formalization can
refine this class later.
-/
class IsQAcyclic (E : Type v) [TopologicalSpace E] : Prop where
  /--
  Acyclic spaces are connected in degree `0`, modeled here by connectedness.
  -/
  connected : ConnectedSpace E
  /--
  Finite odd-cardinality fixed-point consequence for involutive homeomorphisms.
  This is a reusable interface-level consequence expected from Smith/Lefschetz inputs.
  -/
  oddFinite_involution_has_fixedPoint :
    ∀ [Fintype E] [DecidableEq E], Odd (Fintype.card E) →
      HasInvolutiveHomeomorphFixedPointProperty E

/--
Bridge assumption from `ℚ`-acyclic input to the involutive fixed-point property
needed by the obstruction proof.
-/
class QAcyclicInvolutionFixedPointBridge (E : Type v) [TopologicalSpace E] [IsQAcyclic E] : Prop where
  hasFixedPoint : HasInvolutiveHomeomorphFixedPointProperty E

instance (E : Type v) [TopologicalSpace E] [IsQAcyclic E] : ConnectedSpace E :=
  IsQAcyclic.connected (E := E)

instance (E : Type v) [TopologicalSpace E] [IsQAcyclic E]
    [Fintype E] [DecidableEq E] [Fact (Odd (Fintype.card E))] :
    QAcyclicInvolutionFixedPointBridge E where
  hasFixedPoint := IsQAcyclic.oddFinite_involution_has_fixedPoint (E := E) (Fact.out)

instance (E : Type v) [TopologicalSpace E] [IsQAcyclic E]
    [QAcyclicInvolutionFixedPointBridge E] :
    InvolutionFixedPointInput E where
  hasFixedPoint := QAcyclicInvolutionFixedPointBridge.hasFixedPoint (E := E)

/-- A deck transformation candidate for a map `p : E → X`. -/
structure DeckTransformation {E : Type v} {X : Type w}
    [TopologicalSpace E] [TopologicalSpace X] (p : E → X) where
  toHomeomorph : E ≃ₜ E
  comm : p ∘ toHomeomorph = p

namespace DeckTransformation

variable {E : Type v} {X : Type w}
variable [TopologicalSpace E] [TopologicalSpace X] {p : E → X}

instance : CoeFun (DeckTransformation p) (fun _ => E → E) where
  coe g := g.toHomeomorph

@[simp] theorem comm_apply (g : DeckTransformation p) (x : E) : p (g x) = p x := by
  exact congrArg (fun h => h x) g.comm

def refl (p : E → X) : DeckTransformation p where
  toHomeomorph := Homeomorph.refl E
  comm := rfl

@[simp] theorem refl_apply (p : E → X) (x : E) : (refl p) x = x := rfl

def comp (g h : DeckTransformation p) : DeckTransformation p where
  toHomeomorph := g.toHomeomorph.trans h.toHomeomorph
  comm := by
    funext x
    exact (h.comm_apply (g x)).trans (g.comm_apply x)

instance : One (DeckTransformation p) where
  one := refl p

instance : Mul (DeckTransformation p) where
  mul := comp

@[simp] theorem one_eq_refl : (1 : DeckTransformation p) = refl p := rfl

@[simp] theorem one_apply (x : E) : (1 : DeckTransformation p) x = x := rfl

@[simp] theorem mul_toHomeomorph (g h : DeckTransformation p) :
    (g * h).toHomeomorph = g.toHomeomorph.trans h.toHomeomorph := rfl

@[simp] theorem mul_apply (g h : DeckTransformation p) (x : E) :
    (g * h) x = h (g x) := rfl

instance : Monoid (DeckTransformation p) where
  one := 1
  mul := (· * ·)
  one_mul := by
    intro g
    cases g
    rfl
  mul_one := by
    intro g
    cases g
    rfl
  mul_assoc := by
    intro a b c
    cases a
    cases b
    cases c
    rfl

@[ext] theorem ext {g h : DeckTransformation p}
    (hHomeo : g.toHomeomorph = h.toHomeomorph) : g = h := by
  cases g
  cases h
  cases hHomeo
  rfl

end DeckTransformation

end Question7
