-- Prove2me | Theorems.Thm_WilliamsonShmoys_edge_bound_from_face_count__p2m_de817531_bd94_404e_8018_af6b440cc187_a1
-- name    : WilliamsonShmoys.edge_bound_from_face_count__p2m_de817531_bd94_404e_8018_af6b440cc187_a1
-- status  : Proved
-- author  : @Eyal1990
-- created : 2026-10-30T10:09:56.739863+00:00
-- url     : https://prove2.me/theorems/b68598a6-7cdd-421b-9b82-652edb91dcaf
-- title:
--   Edge bound from Euler and face boundary counts
-- statement:
--   For natural numbers satisfying Euler's relation, twice-edge boundary incidence count, and a minimum of three incidences per face, the edge count is at most three times the vertex count minus six.
-- source:
--   David P. Williamson and David B. Shmoys, The Design of Approximation Algorithms, Cambridge University Press, 2011, author electronic manuscript, Section 10.2, proof of Theorem 10.11, pp. 270-272. https://doi.org/10.1017/CBO9780511921735. Bounded tree-width of the pieces: Robertson–Seymour (planar graphs of radius r have tree-width at most 3r+1) / Bodlaender (k-outerplanar graphs have tree-width at most 3k-1).

import Mathlib

theorem WilliamsonShmoys.edge_bound_from_face_count__p2m_de817531_bd94_404e_8018_af6b440cc187_a1 (n e F B : Nat) (hCard : 3 ≤ n) (hEuler : n + F = e + 2) (hDarts : B = 2 * e) (hBoundary : 3 * F ≤ B) : e ≤ 3 * n - 6 := by sorry
