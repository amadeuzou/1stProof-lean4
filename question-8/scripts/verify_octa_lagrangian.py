#!/usr/bin/env python3
"""Verify the explicit octahedron data used in Question8.lean.

Checks:
1) Symplectic area omega(B-A, C-A) is zero for all 8 faces.
2) Each vertex is incident to exactly 4 faces.
"""

from collections import defaultdict

# Vertex order matches Question8.lean: P, N, Q1, Q2, Q3, Q4
V = {
    0: (0, 0, 0, 0),
    1: (-1, 1, -1, 1),
    2: (1, 0, 0, 0),
    3: (0, 0, 1, 0),
    4: (0, 1, 0, 0),
    5: (0, 0, 0, 1),
}

# Face list matches Question8.lean
FACES = [
    (0, 2, 3),
    (0, 3, 4),
    (0, 4, 5),
    (0, 5, 2),
    (1, 2, 3),
    (1, 3, 4),
    (1, 4, 5),
    (1, 5, 2),
]


def sub(a, b):
    return tuple(x - y for x, y in zip(a, b))


def omega(u, v):
    return u[0] * v[1] - u[1] * v[0] + u[2] * v[3] - u[3] * v[2]


def face_area(face):
    a, b, c = face
    A, B, C = V[a], V[b], V[c]
    return omega(sub(B, A), sub(C, A))


def main() -> int:
    ok = True

    print("Face symplectic areas:")
    for i, face in enumerate(FACES):
        area = face_area(face)
        print(f"  face {i}: {face}, omega-area = {area}")
        if area != 0:
            ok = False

    incid = defaultdict(list)
    for i, (a, b, c) in enumerate(FACES):
        incid[a].append(i)
        incid[b].append(i)
        incid[c].append(i)

    print("\nVertex incidence:")
    for v in sorted(V):
        faces = incid[v]
        print(f"  vertex {v}: incident faces = {faces} (count={len(faces)})")
        if len(faces) != 4:
            ok = False

    print("\nResult:", "PASS" if ok else "FAIL")
    return 0 if ok else 1


if __name__ == "__main__":
    raise SystemExit(main())
