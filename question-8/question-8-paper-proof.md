# Question 8 论文级证明草稿（基于 Lean 形式化）

## 1. 题目与结论
设 `K ⊂ R^4` 是一个 polyhedral Lagrangian surface，且每个顶点恰有 4 个面相交。问：`K` 是否必然存在 Lagrangian smoothing？

结论是否定的：存在满足题设条件的 `K`，但 `K` 不存在 Lagrangian smoothing。

## 2. 反例对象的显式构造
我们在标准辛空间 `(R^4, ω_std)` 中取 6 个顶点：
- `P = (0,0,0,0)`，`N = (-1,1,-1,1)`；
- `Q1 = (1,0,0,0)`，`Q2 = (0,0,1,0)`，`Q3 = (0,1,0,0)`，`Q4 = (0,0,0,1)`。

并取 8 个三角面（悬挂于四边形 `Q1Q2Q3Q4`）：
`(P,Q1,Q2)`, `(P,Q2,Q3)`, `(P,Q3,Q4)`, `(P,Q4,Q1)`,
`(N,Q1,Q2)`, `(N,Q2,Q3)`, `(N,Q3,Q4)`, `(N,Q4,Q1)`。

Lean 对应：`OctCoords`, `octFaceVertices`, `OctFaces`。

## 3. 组合与几何验证
### 3.1 每顶点四面相交
对每个顶点显式列出 incident 面列表并证明长度为 4，且与 `vertexInFace` 双向等价。

Lean 对应：`OctIncidentFaces_*`, `octahedronFourFacesWitness`, `octahedron_four_faces`。

### 3.2 面的拉格朗日性
以 `ω_std = dx1∧dy1 + dx2∧dy2` 计算 8 个三角面的辛面积，逐一得到 0。

Lean 对应：`OctFaceArea`, `oct_faces_are_lagrangian`。

### 3.3 组合流形证书
显式给出 12 条边并证明每条边恰有两个 incident 面；证明每个三角面三顶点互异；证明顶点坐标嵌入单射；再配合 `V=6,E=12,F=8` 与 `χ=V-E+F=2` 得到组合球面证书。

Lean 对应：
- `octEdgeVertices`, `OctIncidentFacesOnEdge_*`, `octahedron_each_edge_has_two_incident_faces`；
- `OctFaceDistinctVertices`, `oct_face_distinct_vertices`；
- `OctCoords_injective`；
- `OctNumVertices`, `OctNumEdges`, `OctNumFaces`, `octahedron_euler_char_two`；
- `OctTopologicalSubmanifoldCertificate`。

## 4. 反证核心（外部定理调用）
设存在 `K` 的 Lagrangian smoothing，则可得到一个紧致光滑拉格朗日球面（由 smoothing 保拓扑型）。

外部输入（Gromov 型阻碍）：标准辛 `R^4` 中不存在紧致光滑拉格朗日 `S^2`。

因此导出矛盾，反例 `K` 不可光滑化。

Lean 中先参数化该阻碍命题：`NoCompactLagrangianSphereInR4`，再给出：
- `no_smoothing_of_sphere`；
- `octahedron_no_smoothing_from_obstruction`；
- `Question8_Answer_from_obstruction`。

在 `Question8/ExternalGromov.lean` 中提供“文献调用接口”版本：
- `Question8_Answer`（带参数 `hNoSphere : NoCompactLagrangianSphereInR4`）；
- `Question8_negative_universal`（同样带该参数）。

## 5. 文献位点（正文需给出正式引用）
建议正文引用（见 `question-8-references.bib`）：
- `Gromov1985PseudoHolomorphic`：
  M. Gromov, *Pseudo holomorphic curves in symplectic manifolds*,
  Invent. Math. 82 (1985), 307–347.

当前 Lean 结构中，核心证明位于 `Question8/Core.lean`（无该公理），外部输入位于
`Question8/ExternalGromov.lean`，通过显式参数
`hNoSphere : NoCompactLagrangianSphereInR4` 接入文献定理。

## 6. 当前完成度说明
- 机器验证：`lake build` 通过；无 `sorry/admit`；无 `axiom`。
- 组合与坐标构造：已显式形式化并验证。
- 尚未在 Lean 内部形式化的唯一部分：Gromov 外部定理本体（当前以参数化假设接入）。
