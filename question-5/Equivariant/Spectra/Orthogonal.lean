import Equivariant.IndexingSystem

namespace Equivariant

universe u v w

variable {G : Type u} [Group G]

/--
Objects of the equivariant indexing category `J_G`:
finite-dimensional real `G`-representations (abstract interface layer).
-/
structure JGObject (G : Type u) [Group G] where
  rep : Type v
  finDim : ℕ
  act : G → rep → rep
  act_one : ∀ x, act 1 x = x
  act_mul : ∀ g h x, act (g * h) x = act g (act h x)

/-- Morphisms of `J_G`: abstract linear isometric embeddings. -/
structure JGMorphism (G : Type u) [Group G] (V W : JGObject G) where
  toFun : V.rep → W.rep
  equivariant : ∀ g x, toFun (V.act g x) = W.act g (toFun x)

namespace JGMorphism

def id (G : Type u) [Group G] (V : JGObject G) : JGMorphism G V V :=
  ⟨fun x => x, by intro g x; rfl⟩

def comp (G : Type u) [Group G] {U V W : JGObject G}
    (f : JGMorphism G U V) (g : JGMorphism G V W) : JGMorphism G U W :=
  ⟨g.toFun ∘ f.toFun, by
    intro h x
    change g.toFun (f.toFun (U.act h x)) = W.act h (g.toFun (f.toFun x))
    rw [f.equivariant, g.equivariant]⟩

end JGMorphism

/--
Orthogonal `G`-spectrum interface:
`space V` is the `G`-space at representation `V`,
with functoriality and structure maps.
-/
structure OrthogonalGSpectrum (G : Type u) [Group G] where
  space : JGObject G → Type w
  gAction : ∀ V, G → space V → space V
  gAction_one : ∀ V x, gAction V 1 x = x
  gAction_mul : ∀ V g h x, gAction V (g * h) x = gAction V g (gAction V h x)
  map : ∀ {V W}, JGMorphism G V W → space V → space W
  map_equivariant :
    ∀ {V W} (f : JGMorphism G V W) (g : G) (x : space V),
      map f (gAction V g x) = gAction W g (map f x)
  map_id : ∀ V x, map (JGMorphism.id G V) x = x
  map_comp : ∀ {U V W} (f : JGMorphism G U V) (g : JGMorphism G V W) (x : space U),
      map (JGMorphism.comp G f g) x = map g (map f x)
  unitObj : JGObject G
  directSum : JGObject G → JGObject G → JGObject G
  directSum_assoc :
    ∀ U V W, directSum (directSum U V) W = directSum U (directSum V W)
  directSum_left_unit : ∀ V, directSum unitObj V = V
  directSum_right_unit : ∀ V, directSum V unitObj = V
  sumMap :
    ∀ {V W W' : JGObject G},
      JGMorphism G W W' → JGMorphism G (directSum V W) (directSum V W')
  sumMap_id :
    ∀ (V W : JGObject G),
      sumMap (V := V) (W := W) (W' := W) (JGMorphism.id G W) =
        JGMorphism.id G (directSum V W)
  sumMap_comp :
    ∀ {V W W' W'' : JGObject G}
      (f : JGMorphism G W W') (g : JGMorphism G W' W''),
      sumMap (V := V) (W := W) (W' := W'') (JGMorphism.comp G f g) =
        JGMorphism.comp G (sumMap (V := V) (W := W) (W' := W') f)
          (sumMap (V := V) (W := W') (W' := W'') g)
  sigma : ∀ V W, space W → space (directSum V W)
  sigma_naturality :
    ∀ {V W W' : JGObject G} (f : JGMorphism G W W') (x : space W),
      map (sumMap (V := V) (W := W) (W' := W') f) (sigma V W x) =
        sigma V W' (map f x)

/-- Morphisms of orthogonal `G`-spectra. -/
structure SpectrumHom (G : Type u) [Group G]
    (X Y : OrthogonalGSpectrum G) where
  app : ∀ V, X.space V → Y.space V
  equivariant : ∀ V g x, app V (X.gAction V g x) = Y.gAction V g (app V x)
  naturality : ∀ {V W} (f : JGMorphism G V W) (x : X.space V),
      app W (X.map f x) = Y.map f (app V x)

namespace SpectrumHom

def id (G : Type u) [Group G] (X : OrthogonalGSpectrum G) : SpectrumHom G X X :=
  { app := fun _ x => x
    equivariant := by intro V g x; rfl
    naturality := by intro V W f x; rfl }

def comp (G : Type u) [Group G]
    {X Y Z : OrthogonalGSpectrum G}
    (f : SpectrumHom G X Y) (g : SpectrumHom G Y Z) : SpectrumHom G X Z :=
  { app := fun V x => g.app V (f.app V x)
    equivariant := by
      intro V h x
      rw [f.equivariant, g.equivariant]
    naturality := by
      intro V W h x
      calc
        g.app W (f.app W (X.map h x))
            = g.app W (Y.map h (f.app V x)) := by
                rw [f.naturality h x]
        _ = Z.map h (g.app V (f.app V x)) := by
              rw [g.naturality h (f.app V x)] }

end SpectrumHom

namespace OrthogonalGSpectrum

variable {X : OrthogonalGSpectrum G}

@[simp] theorem gAction_one_apply (V : JGObject G) (x : X.space V) :
    X.gAction V 1 x = x :=
  X.gAction_one V x

theorem gAction_mul_apply (V : JGObject G) (g h : G) (x : X.space V) :
    X.gAction V (g * h) x = X.gAction V g (X.gAction V h x) :=
  X.gAction_mul V g h x

@[simp] theorem map_id_apply (V : JGObject G) (x : X.space V) :
    X.map (JGMorphism.id G V) x = x :=
  X.map_id V x

theorem map_comp_apply {U V W : JGObject G}
    (f : JGMorphism G U V) (g : JGMorphism G V W) (x : X.space U) :
    X.map (JGMorphism.comp G f g) x = X.map g (X.map f x) :=
  X.map_comp f g x

theorem map_equivariant_apply {V W : JGObject G}
    (f : JGMorphism G V W) (g : G) (x : X.space V) :
    X.map f (X.gAction V g x) = X.gAction W g (X.map f x) :=
  X.map_equivariant f g x

theorem directSum_assoc_eq (U V W : JGObject G) :
    X.directSum (X.directSum U V) W = X.directSum U (X.directSum V W) :=
  X.directSum_assoc U V W

@[simp] theorem directSum_left_unit_eq (V : JGObject G) :
    X.directSum X.unitObj V = V :=
  X.directSum_left_unit V

@[simp] theorem directSum_right_unit_eq (V : JGObject G) :
    X.directSum V X.unitObj = V :=
  X.directSum_right_unit V

@[simp] theorem map_sumMap_id_apply (V W : JGObject G)
    (x : X.space (X.directSum V W)) :
    X.map (X.sumMap (V := V) (W := W) (W' := W) (JGMorphism.id G W)) x = x := by
  simp [X.sumMap_id V W]

theorem map_sumMap_comp_apply {V W W' W'' : JGObject G}
    (f : JGMorphism G W W') (g : JGMorphism G W' W'')
    (x : X.space (X.directSum V W)) :
    X.map (X.sumMap (V := V) (W := W) (W' := W'') (JGMorphism.comp G f g)) x =
      X.map (X.sumMap (V := V) (W := W') (W' := W'') g)
        (X.map (X.sumMap (V := V) (W := W) (W' := W') f) x) := by
  calc
    X.map (X.sumMap (V := V) (W := W) (W' := W'') (JGMorphism.comp G f g)) x
        = X.map
            (JGMorphism.comp G
              (X.sumMap (V := V) (W := W) (W' := W') f)
              (X.sumMap (V := V) (W := W') (W' := W'') g)) x := by
              simp [X.sumMap_comp f g]
    _ = X.map (X.sumMap (V := V) (W := W') (W' := W'') g)
          (X.map (X.sumMap (V := V) (W := W) (W' := W') f) x) := by
            simpa using X.map_comp
              (X.sumMap (V := V) (W := W) (W' := W') f)
              (X.sumMap (V := V) (W := W') (W' := W'') g) x

theorem sigma_naturality_apply {V W W' : JGObject G}
    (f : JGMorphism G W W') (x : X.space W) :
    X.map (X.sumMap (V := V) (W := W) (W' := W') f) (X.sigma V W x) =
      X.sigma V W' (X.map f x) :=
  X.sigma_naturality f x

/--
Minimal regression constructor:
constant `PUnit` orthogonal spectrum for any chosen `J_G` monoidal data.
-/
def punitSpectrum
    (unitObj : JGObject G)
    (directSum : JGObject G → JGObject G → JGObject G)
    (directSum_assoc :
      ∀ U V W, directSum (directSum U V) W = directSum U (directSum V W))
    (directSum_left_unit : ∀ V, directSum unitObj V = V)
    (directSum_right_unit : ∀ V, directSum V unitObj = V)
    (sumMap :
      ∀ {V W W' : JGObject G},
        JGMorphism G W W' → JGMorphism G (directSum V W) (directSum V W'))
    (sumMap_id :
      ∀ (V W : JGObject G),
        sumMap (V := V) (W := W) (W' := W) (JGMorphism.id G W) =
          JGMorphism.id G (directSum V W))
    (sumMap_comp :
      ∀ {V W W' W'' : JGObject G}
        (f : JGMorphism G W W') (g : JGMorphism G W' W''),
        sumMap (V := V) (W := W) (W' := W'') (JGMorphism.comp G f g) =
          JGMorphism.comp G (sumMap (V := V) (W := W) (W' := W') f)
            (sumMap (V := V) (W := W') (W' := W'') g)) :
    OrthogonalGSpectrum G where
  space := fun _ => PUnit
  gAction := fun _ _ _ => PUnit.unit
  gAction_one := by intro V x; cases x; rfl
  gAction_mul := by intro V g h x; cases x; rfl
  map := fun {_ _} _ _ => PUnit.unit
  map_equivariant := by intro V W f g x; cases x; rfl
  map_id := by intro V x; cases x; rfl
  map_comp := by intro U V W f g x; cases x; rfl
  unitObj := unitObj
  directSum := directSum
  directSum_assoc := directSum_assoc
  directSum_left_unit := directSum_left_unit
  directSum_right_unit := directSum_right_unit
  sumMap := @sumMap
  sumMap_id := sumMap_id
  sumMap_comp := @sumMap_comp
  sigma := fun _ _ _ => PUnit.unit
  sigma_naturality := by intro V W W' f x; cases x; rfl

end OrthogonalGSpectrum

namespace SpectrumHom

@[simp] theorem id_app (X : OrthogonalGSpectrum G) (V : JGObject G) (x : X.space V) :
    (SpectrumHom.id G X).app V x = x :=
  rfl

@[simp] theorem comp_app {X Y Z : OrthogonalGSpectrum G}
    (f : SpectrumHom G X Y) (g : SpectrumHom G Y Z) (V : JGObject G) (x : X.space V) :
    (SpectrumHom.comp G f g).app V x = g.app V (f.app V x) :=
  rfl

theorem comp_equivariant_apply {X Y Z : OrthogonalGSpectrum G}
    (f : SpectrumHom G X Y) (g : SpectrumHom G Y Z)
    (V : JGObject G) (h : G) (x : X.space V) :
    (SpectrumHom.comp G f g).app V (X.gAction V h x) =
      Z.gAction V h ((SpectrumHom.comp G f g).app V x) :=
  (SpectrumHom.comp G f g).equivariant V h x

end SpectrumHom

/--
Stable homotopy data package:
homotopy groups `π_n^H` and functorial maps induced by spectrum morphisms.
-/
structure StableHomotopyData (G : Type u) [Group G] where
  pi : Subgroup G → ℤ → OrthogonalGSpectrum G → Type w
  piMap : ∀ {X Y : OrthogonalGSpectrum G},
    SpectrumHom G X Y → ∀ H n, pi H n X → pi H n Y

/-- A morphism is a stable equivalence if it induces bijections on all `π_n^H`. -/
def StableEquivalence (D : StableHomotopyData G)
    {X Y : OrthogonalGSpectrum G} (f : SpectrumHom G X Y) : Prop :=
  ∀ H n, Function.Bijective (D.piMap f H n)

/-- Coherence axioms for induced maps on homotopy groups. -/
structure StableHomotopyAxioms (D : StableHomotopyData G) : Prop where
  piMap_id :
    ∀ (X : OrthogonalGSpectrum G) (H : Subgroup G) (n : ℤ),
      D.piMap (SpectrumHom.id G X) H n = id
  piMap_comp :
    ∀ {X Y Z : OrthogonalGSpectrum G}
      (f : SpectrumHom G X Y) (g : SpectrumHom G Y Z)
      (H : Subgroup G) (n : ℤ),
      D.piMap (SpectrumHom.comp G f g) H n =
      (D.piMap g H n) ∘ (D.piMap f H n)

theorem stableEquivalence_id (D : StableHomotopyData G) (hD : StableHomotopyAxioms D)
    (X : OrthogonalGSpectrum G) :
    StableEquivalence D (SpectrumHom.id G X) := by
  intro H n
  simpa [hD.piMap_id X H n] using (Function.bijective_id : Function.Bijective (id))

theorem stableEquivalence_comp (D : StableHomotopyData G) (hD : StableHomotopyAxioms D)
    {X Y Z : OrthogonalGSpectrum G}
    {f : SpectrumHom G X Y} {g : SpectrumHom G Y Z}
    (hf : StableEquivalence D f) (hg : StableEquivalence D g) :
    StableEquivalence D (SpectrumHom.comp G f g) := by
  intro H n
  rw [hD.piMap_comp f g H n]
  exact Function.Bijective.comp (hg H n) (hf H n)

/--
Abstract `Ω`-spectrum condition: each structure map is bijective at the interface level.
In concrete models, this is replaced by weak equivalence of adjoint structure maps.
-/
structure OmegaSpectrum (X : OrthogonalGSpectrum G) : Prop where
  omega_bijective : ∀ V W, Function.Bijective (X.sigma V W)
  sigma_equivariant :
    ∀ V W g x,
      X.sigma V W (X.gAction W g x) =
        X.gAction (X.directSum V W) g (X.sigma V W x)

theorem punitSpectrum_omega
    (unitObj : JGObject G)
    (directSum : JGObject G → JGObject G → JGObject G)
    (directSum_assoc :
      ∀ U V W, directSum (directSum U V) W = directSum U (directSum V W))
    (directSum_left_unit : ∀ V, directSum unitObj V = V)
    (directSum_right_unit : ∀ V, directSum V unitObj = V)
    (sumMap :
      ∀ {V W W' : JGObject G},
        JGMorphism G W W' → JGMorphism G (directSum V W) (directSum V W'))
    (sumMap_id :
      ∀ (V W : JGObject G),
        sumMap (V := V) (W := W) (W' := W) (JGMorphism.id G W) =
          JGMorphism.id G (directSum V W))
    (sumMap_comp :
      ∀ {V W W' W'' : JGObject G}
        (f : JGMorphism G W W') (g : JGMorphism G W' W''),
        sumMap (V := V) (W := W) (W' := W'') (JGMorphism.comp G f g) =
          JGMorphism.comp G (sumMap (V := V) (W := W) (W' := W') f)
            (sumMap (V := V) (W := W') (W' := W'') g)) :
    OmegaSpectrum
      (OrthogonalGSpectrum.punitSpectrum (G := G) unitObj directSum directSum_assoc
        directSum_left_unit directSum_right_unit sumMap sumMap_id sumMap_comp) := by
  refine
    { omega_bijective := ?_
      sigma_equivariant := ?_ }
  · intro V W
    constructor
    · intro x y h
      cases x
      cases y
      rfl
    · intro y
      refine ⟨PUnit.unit, ?_⟩
      cases y
      rfl
  · intro V W g x
    cases x
    rfl

/--
Stable model structure interface for orthogonal `G`-spectra.
This captures fibrant/cofibrant classes and weak equivalences together with
their relation to stable equivalences.
-/
structure StableModelStructure (D : StableHomotopyData G) where
  fibrant : OrthogonalGSpectrum G → Prop
  cofibrant : OrthogonalGSpectrum G → Prop
  fibrant_iff_omega : ∀ X, fibrant X ↔ OmegaSpectrum X
  weakEquivalence : ∀ {X Y}, SpectrumHom G X Y → Prop
  weakEquivalence_iff_stable :
    ∀ {X Y} (f : SpectrumHom G X Y), weakEquivalence f ↔ StableEquivalence D f
  weakEquivalence_id :
    ∀ X, weakEquivalence (SpectrumHom.id G X)
  weakEquivalence_comp :
    ∀ {X Y Z} (f : SpectrumHom G X Y) (g : SpectrumHom G Y Z),
      weakEquivalence f → weakEquivalence g → weakEquivalence (SpectrumHom.comp G f g)

theorem fibrant_of_omega (D : StableHomotopyData G) (M : StableModelStructure D)
    {X : OrthogonalGSpectrum G} (hOmega : OmegaSpectrum X) :
    M.fibrant X := by
  exact (M.fibrant_iff_omega X).2 hOmega

theorem omega_of_fibrant (D : StableHomotopyData G) (M : StableModelStructure D)
    {X : OrthogonalGSpectrum G} (hFib : M.fibrant X) :
    OmegaSpectrum X := by
  exact (M.fibrant_iff_omega X).1 hFib

theorem weakEquivalence_of_stableEquivalence
    (D : StableHomotopyData G) (M : StableModelStructure D)
    {X Y : OrthogonalGSpectrum G} {f : SpectrumHom G X Y}
    (hf : StableEquivalence D f) :
    M.weakEquivalence f := by
  exact (M.weakEquivalence_iff_stable f).2 hf

theorem stableEquivalence_of_weakEquivalence
    (D : StableHomotopyData G) (M : StableModelStructure D)
    {X Y : OrthogonalGSpectrum G} {f : SpectrumHom G X Y}
    (hf : M.weakEquivalence f) :
    StableEquivalence D f := by
  exact (M.weakEquivalence_iff_stable f).1 hf

theorem weakEquivalence_comp_of_stable
    (D : StableHomotopyData G) (hD : StableHomotopyAxioms D) (M : StableModelStructure D)
    {X Y Z : OrthogonalGSpectrum G}
    {f : SpectrumHom G X Y} {g : SpectrumHom G Y Z}
    (hf : StableEquivalence D f) (hg : StableEquivalence D g) :
    M.weakEquivalence (SpectrumHom.comp G f g) := by
  have hcomp : StableEquivalence D (SpectrumHom.comp G f g) :=
    stableEquivalence_comp D hD hf hg
  exact weakEquivalence_of_stableEquivalence D M hcomp

theorem punitSpectrum_stableEquivalence_id
    (D : StableHomotopyData G) (hD : StableHomotopyAxioms D)
    (unitObj : JGObject G)
    (directSum : JGObject G → JGObject G → JGObject G)
    (directSum_assoc :
      ∀ U V W, directSum (directSum U V) W = directSum U (directSum V W))
    (directSum_left_unit : ∀ V, directSum unitObj V = V)
    (directSum_right_unit : ∀ V, directSum V unitObj = V)
    (sumMap :
      ∀ {V W W' : JGObject G},
        JGMorphism G W W' → JGMorphism G (directSum V W) (directSum V W'))
    (sumMap_id :
      ∀ (V W : JGObject G),
        sumMap (V := V) (W := W) (W' := W) (JGMorphism.id G W) =
          JGMorphism.id G (directSum V W))
    (sumMap_comp :
      ∀ {V W W' W'' : JGObject G}
        (f : JGMorphism G W W') (g : JGMorphism G W' W''),
        sumMap (V := V) (W := W) (W' := W'') (JGMorphism.comp G f g) =
          JGMorphism.comp G (sumMap (V := V) (W := W) (W' := W') f)
            (sumMap (V := V) (W := W') (W' := W'') g)) :
    StableEquivalence D
      (SpectrumHom.id G
        (OrthogonalGSpectrum.punitSpectrum (G := G) unitObj directSum directSum_assoc
          directSum_left_unit directSum_right_unit sumMap sumMap_id sumMap_comp)) := by
  exact stableEquivalence_id D hD _

theorem punitSpectrum_weakEquivalence_id
    (D : StableHomotopyData G) (M : StableModelStructure D)
    (unitObj : JGObject G)
    (directSum : JGObject G → JGObject G → JGObject G)
    (directSum_assoc :
      ∀ U V W, directSum (directSum U V) W = directSum U (directSum V W))
    (directSum_left_unit : ∀ V, directSum unitObj V = V)
    (directSum_right_unit : ∀ V, directSum V unitObj = V)
    (sumMap :
      ∀ {V W W' : JGObject G},
        JGMorphism G W W' → JGMorphism G (directSum V W) (directSum V W'))
    (sumMap_id :
      ∀ (V W : JGObject G),
        sumMap (V := V) (W := W) (W' := W) (JGMorphism.id G W) =
          JGMorphism.id G (directSum V W))
    (sumMap_comp :
      ∀ {V W W' W'' : JGObject G}
        (f : JGMorphism G W W') (g : JGMorphism G W' W''),
        sumMap (V := V) (W := W) (W' := W'') (JGMorphism.comp G f g) =
          JGMorphism.comp G (sumMap (V := V) (W := W) (W' := W') f)
            (sumMap (V := V) (W := W') (W' := W'') g)) :
    M.weakEquivalence
      (SpectrumHom.id G
        (OrthogonalGSpectrum.punitSpectrum (G := G) unitObj directSum directSum_assoc
          directSum_left_unit directSum_right_unit sumMap sumMap_id sumMap_comp)) := by
  exact M.weakEquivalence_id _

end Equivariant
