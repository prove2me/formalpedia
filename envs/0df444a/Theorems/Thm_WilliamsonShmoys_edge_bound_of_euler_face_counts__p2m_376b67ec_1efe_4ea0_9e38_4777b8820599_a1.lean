-- Prove2me | Theorems.Thm_WilliamsonShmoys_edge_bound_of_euler_face_counts__p2m_376b67ec_1efe_4ea0_9e38_4777b8820599_a1
-- name    : WilliamsonShmoys.edge_bound_of_euler_face_counts__p2m_376b67ec_1efe_4ea0_9e38_4777b8820599_a1
-- status  : Proved
-- author  : @Eyal1990
-- created : 2026-10-31T21:07:54.130475+00:00
-- url     : https://prove2.me/theorems/1443ab7b-9904-4ee6-b12c-9983246273ed
-- title:
--   Edge bound from Euler face counts
-- statement:
--   If natural-number vertex, edge, and face counts satisfy Euler’s equation, each face contributes at least three boundary incidences, and there are at least three vertices, then the edge count is at most three times the vertex count minus six.
-- source:
--   David P. Williamson and David B. Shmoys, The Design of Approximation Algorithms, Cambridge University Press, 2011, author electronic manuscript, Section 10.2, proof of Theorem 10.11, pp. 270-272. https://doi.org/10.1017/CBO9780511921735. Bounded tree-width of the pieces: Robertson–Seymour (planar graphs of radius r have tree-width at most 3r+1) / Bodlaender (k-outerplanar graphs have tree-width at most 3k-1).

import Mathlib

theorem WilliamsonShmoys.edge_bound_of_euler_face_counts__p2m_376b67ec_1efe_4ea0_9e38_4777b8820599_a1
    (n m f : ℕ)
    (hEuler : n + f = m + 2)
    (hfaces : 3 * f ≤ 2 * m)
    (hn : 3 ≤ n) :
    m ≤ 3 * n - 6 := by sorry
