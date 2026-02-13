# Lean4 Formalization Notes for Question 8 (English)

## 1. Current result
This version proves the negative form:

`∃ K, FourFacesMeeting K ∧ ¬ HasLagrangianSmoothing K`.

The octahedron-like counterexample is now explicitly constructed (coordinates + faces + incidence), not postulated by a single existence axiom.

## 2. Explicit construction
Core file: `Question8/Core.lean`

- Vertex coordinates: `OctCoords : Fin 6 → R4` (all 6 vertices are explicit).
- Face list: `octFaceVertices : Fin 8 → (Fin 6 × Fin 6 × Fin 6)` and `OctFaces`.
- `PolyhedralLagrangian` now includes `finiteVertex`/`finiteFace` and `topologicalSubmanifold`,
  aligning with the statement “finite polyhedral complex + topological submanifold”.
- Added combinatorial layer:
  - `SimplicialSurface`
  - `IsCombinatorialSphere`
  - `octahedronSimplicial`
  - `octahedron_is_combinatorial_sphere`
- `LagrangianSmoothing` now includes
  `hamiltonianIsotopyOnIoc`, `extendsToTopologicalIsotopyOnIcc`, and `endpointAtZeroIsK`
  to mirror the smoothing semantics in the problem statement.
- Four-faces condition:
  - `FourFacesWitness` (per-vertex incident-face list, length=4, complete w.r.t. `vertexInFace`)
  - explicit witness `octahedronFourFacesWitness`
  - derived theorem `octahedron_four_faces`.
- Combinatorial manifold strengthening:
  - `octEdgeVertices : Fin 12 → (Fin 6 × Fin 6)` gives all 12 edges explicitly;
  - `OctIncidentFacesOnEdge` with theorem `octahedron_each_edge_has_two_incident_faces` proves each edge has exactly two incident faces;
  - `OctFaceDistinctVertices` + `oct_face_distinct_vertices` prove each triangular face has three distinct vertices;
  - `OctCoords_injective` proves injectivity of the vertex embedding.
- Face-Lagrangian property:
  - `OctFaceArea` computes symplectic area per face
  - `oct_faces_are_lagrangian` proves all 8 face areas are zero.
- Euler characteristic is now derived from explicit counts:
  - `OctNumVertices = 6`, `OctNumEdges = 12`, `OctNumFaces = 8`;
  - `OctEulerChar := V - E + F`, with proof `octahedron_euler_char_two : OctEulerChar = 2`.
- `topologicalSubmanifold` is no longer a single placeholder condition; it is backed by
  `OctTopologicalSubmanifoldCertificate` (combinatorial sphere + two-faces-per-edge + face nondegeneracy + injective coordinates).

## 3. Main contradiction chain
1. Introduce the external obstruction predicate `NoCompactLagrangianSphereInR4`:
   “there is no compact smooth Lagrangian sphere in standard symplectic `ℝ⁴`”.
   In the core development it is passed as an explicit hypothesis parameter, not as a global axiom.
2. `smoothing_preserves_sphere_type`: any smoothing preserves the sphere-type encoding.
3. `no_smoothing_of_sphere`: combine preserved sphere type + compactness + Lagrangian to contradict the Gromov obstruction directly.
4. Instantiate for explicit `octahedronPoly` in parameterized form:
   `octahedron_no_smoothing_from_obstruction`.
5. Add parameterized versions:
   `octahedron_no_smoothing_from_obstruction`,
   `Question8_Answer_strong_from_obstruction`,
   `Question8_Answer_from_obstruction`.
6. In `Question8/ExternalGromov.lean`, provide citation-interface versions
   (`Question8_Answer`, `Question8_negative_universal`) that explicitly take
   `hNoSphere : NoCompactLagrangianSphereInR4`.
7. Add a hypothesis-matching universal negation result:
   `Question8_negative_universal`, i.e.
   `¬ (∀ K, K.faceLagrangianWrtOmegaStd → FourFacesMeeting K → HasLagrangianSmoothing K)`.

## 4. Formal Status
- `Question8.lean`, `Question8/Core.lean`, and `Question8/ExternalGromov.lean` currently contain no `axiom`.
- The external mathematical input is represented as an explicit parameter:
  `hNoSphere : NoCompactLagrangianSphereInR4`.
- Octahedron existence/coordinate/incidence axioms were removed.

`Question8/Core.lean` is axiom-free with respect to this obstruction; top-level
`Question8.lean` is now only an entry module importing `Question8.Core` and
`Question8.ExternalGromov`.

## 5. Verification
- `lake build` passes.
- No `sorry`/`admit` tactic in `Question8.lean`, `Question8/Core.lean`, or `Question8/ExternalGromov.lean`.
- Added `scripts/verify_formal_status.sh` for one-shot checks:
  build + axiom/sorry scan + geometric sanity script.
- Added script `scripts/verify_octa_lagrangian.py`:
  - checks zero symplectic area on all 8 faces;
  - checks each vertex has exactly 4 incident faces;
  - current run returns `PASS`.

## 6. Remaining Gap to Paper-Level Completeness
- The only remaining black-box input is the hypothesis parameter
  `NoCompactLagrangianSphereInR4` (the Gromov obstruction).
- For full internal Lean completeness, this external theorem itself must be formalized.
- For paper-grade completeness, the manuscript must include a citation-grade bridge:
  precise statement, hypotheses, and reduction chain to the `ℝ⁴` instance used here.
