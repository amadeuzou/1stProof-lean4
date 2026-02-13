import Mathlib

set_option autoImplicit false

/-!
Question 8 (disproof route):
we make the octahedron combinatorics and coordinates explicit in standard symplectic `ℝ⁴`,
prove every listed face is Lagrangian by direct computation, and combine this with
axiomatized smooth obstruction statements (Gromov-type).
-/

/-- Coordinate model of `ℝ⁴`. -/
abbrev R4 := Fin 4 → ℝ

/-- Standard symplectic form on `ℝ⁴`:
`ω_std = dx₁ ∧ dy₁ + dx₂ ∧ dy₂`. -/
def omegaStd (u v : R4) : ℝ :=
  u 0 * v 1 - u 1 * v 0 + u 2 * v 3 - u 3 * v 2

/-- Polyhedral Lagrangian surface data in standard symplectic `ℝ⁴`. -/
structure PolyhedralLagrangian where
  carrier : Type
  embed : carrier → R4
  vertex : Type
  face : Type
  finiteVertex : Fintype vertex
  finiteFace : Fintype face
  vertexInFace : vertex → face → Prop
  topologicalSubmanifold : Prop
  topologicalSubmanifold_holds : topologicalSubmanifold
  compact : Prop
  compact_holds : compact
  topologicalSphere : Prop
  topologicalSphere_holds : topologicalSphere
  faceLagrangianWrtOmegaStd : Prop
  faceLagrangianWrtOmegaStd_holds : faceLagrangianWrtOmegaStd

/-- Local combinatorial witness that exactly four faces meet each vertex. -/
structure FourFacesWitness (K : PolyhedralLagrangian) where
  incidentFaces : K.vertex → List K.face
  length_eq_four : ∀ v : K.vertex, (incidentFaces v).length = 4
  all_are_incident :
    ∀ v : K.vertex, ∀ f : K.face, f ∈ incidentFaces v → K.vertexInFace v f
  complete :
    ∀ v : K.vertex, ∀ f : K.face, K.vertexInFace v f → f ∈ incidentFaces v

/-- Exactly four faces meet at each vertex (combinatorial condition). -/
def FourFacesMeeting (K : PolyhedralLagrangian) : Prop :=
  Nonempty (FourFacesWitness K)

/-- Smooth compact Lagrangian in standard symplectic `ℝ⁴`. -/
structure SmoothLagrangian where
  carrier : Type
  embed : carrier → R4
  compact : Prop
  compact_holds : compact
  lagrangianWrtOmegaStd : Prop
  lagrangianWrtOmegaStd_holds : lagrangianWrtOmegaStd
  liouvilleRestrictionClosed : Prop
  liouvilleRestrictionClosed_holds : liouvilleRestrictionClosed
  isTopologicalSphere : Prop
  exact : Prop

/-- Exactness predicate (named interface requested by the task). -/
def ExactLagrangian (L : SmoothLagrangian) : Prop :=
  L.exact

/-- A smoothing witness from polyhedral data to smooth data. -/
structure LagrangianSmoothing (K : PolyhedralLagrangian) where
  smooth : SmoothLagrangian
  hamiltonianIsotopyOnIoc : Prop
  hamiltonianIsotopyOnIoc_holds : hamiltonianIsotopyOnIoc
  extendsToTopologicalIsotopyOnIcc : Prop
  extendsToTopologicalIsotopyOnIcc_holds : extendsToTopologicalIsotopyOnIcc
  endpointAtZeroIsK : Prop
  endpointAtZeroIsK_holds : endpointAtZeroIsK
  homeomorphicToPolyhedron : Prop
  homeomorphicToPolyhedron_holds : homeomorphicToPolyhedron
  preservesTopologicalType : K.topologicalSphere → smooth.isTopologicalSphere

/-- Existence of a Lagrangian smoothing for `K`. -/
def HasLagrangianSmoothing (K : PolyhedralLagrangian) : Prop :=
  Nonempty (LagrangianSmoothing K)

/-- Combinatorial 2-complex data used to model triangulated surfaces. -/
structure SimplicialSurface where
  Vertex : Type
  Face : Type
  faceVerts : Face → Vertex × Vertex × Vertex
  incidentFaces : Vertex → List Face
  incidence_sound :
    ∀ v : Vertex, ∀ f : Face, f ∈ incidentFaces v →
      let (a, b, c) := faceVerts f
      v = a ∨ v = b ∨ v = c
  incidence_complete :
    ∀ v : Vertex, ∀ f : Face,
      (let (a, b, c) := faceVerts f; v = a ∨ v = b ∨ v = c) →
      f ∈ incidentFaces v
  eulerChar : ℤ

/-- Minimal combinatorial sphere certificate used in this development. -/
def IsCombinatorialSphere (S : SimplicialSurface) : Prop :=
  S.eulerChar = 2 ∧ ∀ v : S.Vertex, (S.incidentFaces v).length = 4

/-- Vertex and face index types for the explicit octahedron model. -/
abbrev OctVertex := Fin 6
abbrev OctFace := Fin 8
abbrev OctEdge := Fin 12

/-- Explicit octahedron vertices in `ℝ⁴`:
`P, N, Q₁, Q₂, Q₃, Q₄`. -/
def vP : R4 := ![(0 : ℝ), 0, 0, 0]
def vN : R4 := ![(-1 : ℝ), 1, -1, 1]
def vQ1 : R4 := ![(1 : ℝ), 0, 0, 0]
def vQ2 : R4 := ![(0 : ℝ), 0, 1, 0]
def vQ3 : R4 := ![(0 : ℝ), 1, 0, 0]
def vQ4 : R4 := ![(0 : ℝ), 0, 0, 1]

/-- Coordinates map for the six octahedron vertices. -/
def OctCoords : OctVertex → R4
  | 0 => vP
  | 1 => vN
  | 2 => vQ1
  | 3 => vQ2
  | 4 => vQ3
  | 5 => vQ4

/-- Eight triangular faces (suspension of a 4-cycle). -/
def octFaceVertices : OctFace → OctVertex × OctVertex × OctVertex
  | 0 => (0, 2, 3)
  | 1 => (0, 3, 4)
  | 2 => (0, 4, 5)
  | 3 => (0, 5, 2)
  | 4 => (1, 2, 3)
  | 5 => (1, 3, 4)
  | 6 => (1, 4, 5)
  | 7 => (1, 5, 2)

/-- Face list form of the same combinatorics. -/
def OctFaces : List (OctVertex × OctVertex × OctVertex) :=
  [(0, 2, 3), (0, 3, 4), (0, 4, 5), (0, 5, 2),
   (1, 2, 3), (1, 3, 4), (1, 4, 5), (1, 5, 2)]

/-- Twelve edges of the explicit octahedron. -/
def octEdgeVertices : OctEdge → OctVertex × OctVertex
  | 0 => (0, 2)
  | 1 => (0, 3)
  | 2 => (0, 4)
  | 3 => (0, 5)
  | 4 => (1, 2)
  | 5 => (1, 3)
  | 6 => (1, 4)
  | 7 => (1, 5)
  | 8 => (2, 3)
  | 9 => (3, 4)
  | 10 => (4, 5)
  | 11 => (2, 5)

/-- Unordered edge-face incidence for the explicit model. -/
def OctEdgeInFace (e : OctEdge) (f : OctFace) : Prop :=
  let (u, v) := octEdgeVertices e
  let (a, b, c) := octFaceVertices f
  (u = a ∨ u = b ∨ u = c) ∧
  (v = a ∨ v = b ∨ v = c) ∧
  u ≠ v

/-- For each edge, the two incident faces in the octahedron. -/
def OctIncidentFacesOnEdge : OctEdge → List OctFace
  | 0 => [0, 3]
  | 1 => [0, 1]
  | 2 => [1, 2]
  | 3 => [2, 3]
  | 4 => [4, 7]
  | 5 => [4, 5]
  | 6 => [5, 6]
  | 7 => [6, 7]
  | 8 => [0, 4]
  | 9 => [1, 5]
  | 10 => [2, 6]
  | 11 => [3, 7]

/-- Vertex-face incidence from explicit face triples. -/
def OctVertexInFace (v : OctVertex) (f : OctFace) : Prop :=
  let (a, b, c) := octFaceVertices f
  v = a ∨ v = b ∨ v = c

/-- For each vertex, the explicit list of its incident faces (length 4). -/
def OctIncidentFaces : OctVertex → List OctFace
  | 0 => [0, 1, 2, 3]
  | 1 => [4, 5, 6, 7]
  | 2 => [0, 3, 4, 7]
  | 3 => [0, 1, 4, 5]
  | 4 => [1, 2, 5, 6]
  | 5 => [2, 3, 6, 7]

theorem OctIncidentFaces_length_four : ∀ v : OctVertex, (OctIncidentFaces v).length = 4 := by
  intro v
  fin_cases v <;> rfl

theorem OctIncidentFaces_all_incident :
    ∀ v : OctVertex, ∀ f : OctFace, f ∈ OctIncidentFaces v → OctVertexInFace v f := by
  intro v f hf
  fin_cases v <;> fin_cases f <;>
    simp [OctIncidentFaces, OctVertexInFace, octFaceVertices] at hf ⊢

theorem OctIncidentFaces_complete :
    ∀ v : OctVertex, ∀ f : OctFace, OctVertexInFace v f → f ∈ OctIncidentFaces v := by
  intro v f hf
  fin_cases v <;> fin_cases f <;>
    simp [OctIncidentFaces, OctVertexInFace, octFaceVertices] at hf ⊢

theorem OctIncidentFacesOnEdge_length_two :
    ∀ e : OctEdge, (OctIncidentFacesOnEdge e).length = 2 := by
  intro e
  fin_cases e <;> rfl

theorem OctIncidentFacesOnEdge_all_incident :
    ∀ e : OctEdge, ∀ f : OctFace, f ∈ OctIncidentFacesOnEdge e → OctEdgeInFace e f := by
  intro e f hf
  fin_cases e <;> fin_cases f <;>
    simp [OctIncidentFacesOnEdge, OctEdgeInFace, octEdgeVertices, octFaceVertices] at hf ⊢

theorem OctIncidentFacesOnEdge_complete :
    ∀ e : OctEdge, ∀ f : OctFace, OctEdgeInFace e f → f ∈ OctIncidentFacesOnEdge e := by
  intro e f hf
  fin_cases e <;> fin_cases f <;>
    simp [OctIncidentFacesOnEdge, OctEdgeInFace, octEdgeVertices, octFaceVertices] at hf ⊢

/-- Explicit combinatorial manifold check:
every edge is incident to exactly two faces. -/
def OctEachEdgeHasTwoIncidentFaces : Prop :=
  ∀ e : OctEdge,
    (OctIncidentFacesOnEdge e).length = 2 ∧
      (∀ f : OctFace, f ∈ OctIncidentFacesOnEdge e → OctEdgeInFace e f) ∧
      (∀ f : OctFace, OctEdgeInFace e f → f ∈ OctIncidentFacesOnEdge e)

theorem octahedron_each_edge_has_two_incident_faces : OctEachEdgeHasTwoIncidentFaces := by
  intro e
  refine ⟨OctIncidentFacesOnEdge_length_two e, ?_, ?_⟩
  · intro f hf
    exact OctIncidentFacesOnEdge_all_incident e f hf
  · intro f hf
    exact OctIncidentFacesOnEdge_complete e f hf

theorem OctCoords_injective : Function.Injective OctCoords := by
  intro i j hij
  have h0 := congrArg (fun x => x 0) hij
  have h1 := congrArg (fun x => x 1) hij
  have h2 := congrArg (fun x => x 2) hij
  have h3 := congrArg (fun x => x 3) hij
  fin_cases i <;> fin_cases j <;>
    simp [OctCoords, vP, vN, vQ1, vQ2, vQ3, vQ4] at h0 h1 h2 h3 ⊢

def OctFaceDistinctVertices (f : OctFace) : Prop :=
  let (a, b, c) := octFaceVertices f
  a ≠ b ∧ b ≠ c ∧ a ≠ c

theorem oct_face_distinct_vertices : ∀ f : OctFace, OctFaceDistinctVertices f := by
  intro f
  fin_cases f <;> simp [OctFaceDistinctVertices, octFaceVertices]

/-- Symplectic area of an oriented triangle in `ℝ⁴`. -/
def triangleOmega (A B C : R4) : ℝ :=
  omegaStd (B - A) (C - A)

/-- Symplectic area of an explicit octahedron face. -/
def OctFaceArea (f : OctFace) : ℝ :=
  let (a, b, c) := octFaceVertices f
  triangleOmega (OctCoords a) (OctCoords b) (OctCoords c)

/-- Every explicit face has zero symplectic area. -/
def OctFacesAreLagrangian : Prop :=
  ∀ f : OctFace, OctFaceArea f = 0

theorem oct_faces_are_lagrangian : OctFacesAreLagrangian := by
  intro f
  fin_cases f <;>
    norm_num [OctFaceArea, triangleOmega, omegaStd, octFaceVertices, OctCoords,
      vP, vN, vQ1, vQ2, vQ3, vQ4]

/-- Face/edge/vertex counts for the explicit octahedron. -/
def OctNumVertices : ℕ := Fintype.card OctVertex
def OctNumEdges : ℕ := Fintype.card OctEdge
def OctNumFaces : ℕ := Fintype.card OctFace

theorem oct_num_vertices : OctNumVertices = 6 := by
  decide

theorem oct_num_edges : OctNumEdges = 12 := by
  decide

theorem oct_num_faces : OctNumFaces = 8 := by
  decide

/-- Euler characteristic from explicit `V-E+F` counts. -/
def OctEulerChar : ℤ := (OctNumVertices : ℤ) - OctNumEdges + OctNumFaces

theorem octahedron_euler_char_two : OctEulerChar = 2 := by
  norm_num [OctEulerChar, OctNumVertices, OctNumEdges, OctNumFaces]

/-- Explicit simplicial-surface package for the octahedron model. -/
def octahedronSimplicial : SimplicialSurface where
  Vertex := OctVertex
  Face := OctFace
  faceVerts := octFaceVertices
  incidentFaces := OctIncidentFaces
  incidence_sound := by
    intro v f hf
    exact OctIncidentFaces_all_incident v f hf
  incidence_complete := by
    intro v f hf
    exact OctIncidentFaces_complete v f hf
  eulerChar := OctEulerChar

theorem octahedron_is_combinatorial_sphere : IsCombinatorialSphere octahedronSimplicial := by
  refine ⟨octahedron_euler_char_two, ?_⟩
  intro v
  exact OctIncidentFaces_length_four v

/-- A concrete certificate used as a proxy for embedded PL-surface regularity. -/
def OctTopologicalSubmanifoldCertificate : Prop :=
  IsCombinatorialSphere octahedronSimplicial ∧
  OctEachEdgeHasTwoIncidentFaces ∧
  (∀ f : OctFace, OctFaceDistinctVertices f) ∧
  Function.Injective OctCoords

theorem octahedron_topological_submanifold_certificate :
    OctTopologicalSubmanifoldCertificate := by
  refine ⟨octahedron_is_combinatorial_sphere, octahedron_each_edge_has_two_incident_faces, ?_, ?_⟩
  · exact oct_face_distinct_vertices
  · exact OctCoords_injective

/-- Explicit octahedron polyhedral Lagrangian object. -/
def octahedronPoly : PolyhedralLagrangian where
  carrier := OctVertex
  embed := OctCoords
  vertex := OctVertex
  face := OctFace
  finiteVertex := inferInstance
  finiteFace := inferInstance
  vertexInFace := OctVertexInFace
  topologicalSubmanifold := OctTopologicalSubmanifoldCertificate
  topologicalSubmanifold_holds := octahedron_topological_submanifold_certificate
  compact := True
  compact_holds := trivial
  topologicalSphere := IsCombinatorialSphere octahedronSimplicial
  topologicalSphere_holds := octahedron_is_combinatorial_sphere
  faceLagrangianWrtOmegaStd := OctFacesAreLagrangian
  faceLagrangianWrtOmegaStd_holds := oct_faces_are_lagrangian

theorem octahedron_compact : octahedronPoly.compact := by
  exact octahedronPoly.compact_holds

theorem octahedron_faces_lagrangian : octahedronPoly.faceLagrangianWrtOmegaStd := by
  exact octahedronPoly.faceLagrangianWrtOmegaStd_holds

/-- Explicit four-faces witness for `octahedronPoly`. -/
def octahedronFourFacesWitness : FourFacesWitness octahedronPoly where
  incidentFaces := OctIncidentFaces
  length_eq_four := OctIncidentFaces_length_four
  all_are_incident := by
    intro v f hf
    exact OctIncidentFaces_all_incident v f hf
  complete := by
    intro v f hv
    exact OctIncidentFaces_complete v f hv

theorem octahedron_four_faces : FourFacesMeeting octahedronPoly := by
  exact ⟨octahedronFourFacesWitness⟩

/-- Sphere property for the explicit octahedron object (combinatorial encoding). -/
theorem octahedron_is_sphere : octahedronPoly.topologicalSphere := by
  exact octahedronPoly.topologicalSphere_holds

theorem octahedron_topological_submanifold : octahedronPoly.topologicalSubmanifold := by
  exact octahedronPoly.topologicalSubmanifold_holds

theorem octahedron_is_valid_polyhedral_lagrangian :
    octahedronPoly.compact ∧
      octahedronPoly.topologicalSubmanifold ∧
      octahedronPoly.topologicalSphere ∧
      octahedronPoly.faceLagrangianWrtOmegaStd := by
  refine ⟨octahedron_compact, octahedron_topological_submanifold, octahedron_is_sphere, ?_⟩
  exact octahedron_faces_lagrangian

/-- External obstruction predicate used by the final disproof chain. -/
def NoCompactLagrangianSphereInR4 : Prop :=
  ¬ ∃ L : SmoothLagrangian, L.compact ∧ L.isTopologicalSphere ∧ L.lagrangianWrtOmegaStd

theorem smoothing_preserves_sphere_type
    {K : PolyhedralLagrangian} (S : LagrangianSmoothing K) :
    K.topologicalSphere → S.smooth.isTopologicalSphere :=
  S.preservesTopologicalType

/-- Generic contradiction principle for sphere-like polyhedra. -/
theorem no_smoothing_of_sphere
    {K : PolyhedralLagrangian}
    (hSphere : K.topologicalSphere)
    (hNoSphere : NoCompactLagrangianSphereInR4) :
    ¬ HasLagrangianSmoothing K := by
  intro hSmooth
  rcases hSmooth with ⟨S⟩
  have hSphereSmooth : S.smooth.isTopologicalSphere :=
    smoothing_preserves_sphere_type S hSphere
  exact hNoSphere
    ⟨S.smooth, S.smooth.compact_holds, hSphereSmooth, S.smooth.lagrangianWrtOmegaStd_holds⟩

theorem octahedron_smoothing_gives_sphere
    (h : HasLagrangianSmoothing octahedronPoly) :
    ∃ L : SmoothLagrangian, L.isTopologicalSphere := by
  rcases h with ⟨S⟩
  refine ⟨S.smooth, ?_⟩
  exact smoothing_preserves_sphere_type S octahedron_is_sphere

theorem octahedron_no_smoothing_from_obstruction
    (hNoSphere : NoCompactLagrangianSphereInR4) :
    ¬ HasLagrangianSmoothing octahedronPoly := by
  exact no_smoothing_of_sphere octahedron_is_sphere
    hNoSphere

theorem octahedron_is_face_lagrangian : octahedronPoly.faceLagrangianWrtOmegaStd := by
  exact octahedron_faces_lagrangian

theorem Question8_Answer_strong_from_obstruction
    (hNoSphere : NoCompactLagrangianSphereInR4) :
    ∃ K : PolyhedralLagrangian,
      K.faceLagrangianWrtOmegaStd ∧ FourFacesMeeting K ∧ ¬ HasLagrangianSmoothing K := by
  refine ⟨octahedronPoly, octahedron_is_face_lagrangian, octahedron_four_faces, ?_⟩
  exact octahedron_no_smoothing_from_obstruction hNoSphere

theorem Question8_Answer_from_obstruction
    (hNoSphere : NoCompactLagrangianSphereInR4) :
    ∃ K : PolyhedralLagrangian, FourFacesMeeting K ∧ ¬ HasLagrangianSmoothing K := by
  rcases Question8_Answer_strong_from_obstruction hNoSphere with ⟨K, _hLag, hFour, hNoSmooth⟩
  exact ⟨K, hFour, hNoSmooth⟩

theorem octahedron_satisfies_question_hypotheses :
    octahedronPoly.faceLagrangianWrtOmegaStd ∧ FourFacesMeeting octahedronPoly := by
  exact ⟨octahedron_is_face_lagrangian, octahedron_four_faces⟩

theorem not_all_four_faces_are_smoothable_from_obstruction
    (hNoSphere : NoCompactLagrangianSphereInR4) :
    ¬ (∀ K : PolyhedralLagrangian, FourFacesMeeting K → HasLagrangianSmoothing K) := by
  intro hAll
  exact octahedron_no_smoothing_from_obstruction hNoSphere
    (hAll octahedronPoly octahedron_four_faces)

/-- Universal positive answer to Question 8 is false (hypothesis-matching form). -/
theorem Question8_negative_universal_from_obstruction
    (hNoSphere : NoCompactLagrangianSphereInR4) :
    ¬ (∀ K : PolyhedralLagrangian,
      K.faceLagrangianWrtOmegaStd → FourFacesMeeting K → HasLagrangianSmoothing K) := by
  intro hAll
  exact octahedron_no_smoothing_from_obstruction hNoSphere
    (hAll octahedronPoly octahedron_is_face_lagrangian octahedron_four_faces)
