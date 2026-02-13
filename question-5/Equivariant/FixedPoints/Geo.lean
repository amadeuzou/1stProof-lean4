import Equivariant.Slice.Generators

namespace Equivariant

universe u v

variable {G : Type u} [Group G]

/-- Abstract geometric fixed-point data. -/
structure GeoFixedPointsData (C : SpectrumLike G) where
  PlainObj : Type v
  phi : Subgroup G → C.Obj → PlainObj
  isConnected : Subgroup G → PlainObj → ℤ → Prop

/--
Geometric fixed-point criterion at level `n`.
Threshold `d O H n` depends on the incomplete transfer system `O`.
-/
def GeometricFixedPointCondition (C : SpectrumLike G) (geo : GeoFixedPointsData C)
    (O : IncompleteTransferSystem G) (d : DimensionFunction G)
    (n : ℤ) (X : C.Obj) : Prop :=
  ∀ H, geo.isConnected H (geo.phi H X) (d O H n)

/--
Closure package: geometric fixed-point criterion holds for generators and
is preserved by localizing operations.
-/
structure FixedPointClosureAxioms (C : SpectrumLike G) (O : IncompleteTransferSystem G)
    (geo : GeoFixedPointsData C) (d : DimensionFunction G) : Prop where
  generators :
    ∀ {n : ℤ} {c : SliceCellData G},
      c ∈ OSliceCells C O d n →
        GeometricFixedPointCondition C geo O d n
          (C.sliceCellObj c.fromSubgroup c.toSubgroup c.degree)
  zero :
    ∀ {n : ℤ},
      GeometricFixedPointCondition C geo O d n C.zero
  susp :
    ∀ {n : ℤ} {X : C.Obj},
      GeometricFixedPointCondition C geo O d n X →
        GeometricFixedPointCondition C geo O d n (C.susp X)
  cofiber :
    ∀ {n : ℤ} {X Y : C.Obj},
      GeometricFixedPointCondition C geo O d n X →
      GeometricFixedPointCondition C geo O d n Y →
        GeometricFixedPointCondition C geo O d n (C.cofiber X Y)
  colim :
    ∀ {n : ℤ} {ι : Type v} (F : ι → C.Obj),
      (∀ i, GeometricFixedPointCondition C geo O d n (F i)) →
        GeometricFixedPointCondition C geo O d n (C.colim F)

end Equivariant
