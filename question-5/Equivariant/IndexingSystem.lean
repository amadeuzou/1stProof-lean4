import Mathlib.Algebra.Group.Subgroup.Defs
import Mathlib.Data.Int.Basic

namespace Equivariant

universe u

variable {G : Type u} [Group G]

/-- Incomplete transfer/indexing relation on the subgroup lattice of `G`. -/
structure IncompleteTransferSystem (G : Type u) [Group G] where
  transfer : Subgroup G → Subgroup G → Prop
  transfer_refl : ∀ H, transfer H H
  transfer_trans : ∀ {H K L}, transfer H K → transfer K L → transfer H L
  transfer_subgroup : ∀ {H K}, transfer H K → H ≤ K

/-- Dimension threshold depending on transfer system, subgroup and slice level. -/
abbrev DimensionFunction (G : Type u) [Group G] :=
  IncompleteTransferSystem G → Subgroup G → ℤ → ℤ

/-- Monotonicity contract for a dimension function along admissible transfers. -/
structure DimensionFunctionSpec (d : DimensionFunction G) : Prop where
  transfer_mono : ∀ {O H K n}, O.transfer H K → d O H n ≤ d O K n

/-- `N∞` operad interface via associated incomplete transfer system. -/
structure NInfinityOperad (G : Type u) [Group G] where
  transferSystem : IncompleteTransferSystem G

/--
Indexing system packaged on top of an incomplete transfer system with
explicit closure requirements.
-/
structure IndexingSystem (G : Type u) [Group G] where
  toTransferSystem : IncompleteTransferSystem G
  closed_downward :
    ∀ {H K L : Subgroup G}, toTransferSystem.transfer H K → L ≤ H →
      toTransferSystem.transfer L K
  closed_upward :
    ∀ {H K L : Subgroup G}, toTransferSystem.transfer H K → K ≤ L →
      toTransferSystem.transfer H L

end Equivariant
