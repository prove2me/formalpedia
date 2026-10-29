-- Prove2me | Theorems.Thm_WilliamsonShmoys_euler_face_degree_edge_bound__p2m_1292968f_ac05_4a25_979d_3851b390bd91_a1
-- name    : WilliamsonShmoys.euler_face_degree_edge_bound__p2m_1292968f_ac05_4a25_979d_3851b390bd91_a1
-- status  : Proved
-- author  : @Eyal1990
-- created : 2026-10-28T20:42:36.176913+00:00
-- url     : https://prove2.me/theorems/35a2477d-2eba-4efd-a826-c18ccdb0d601
-- title:
--   Euler face-degree arithmetic implies the planar edge bound
-- statement:
--   The Euler relation and the lower bound of three on each face boundary imply that the edge count is at most three times the vertex count minus six.
-- source:
--   David P. Williamson and David B. Shmoys, The Design of Approximation Algorithms, Cambridge University Press, 2011, author electronic manuscript, Section 10.2, proof of Theorem 10.11, pp. 270-272. https://doi.org/10.1017/CBO9780511921735. Bounded tree-width of the pieces: Robertson–Seymour (planar graphs of radius r have tree-width at most 3r+1) / Bodlaender (k-outerplanar graphs have tree-width at most 3k-1).

import Mathlib

theorem WilliamsonShmoys.euler_face_degree_edge_bound__p2m_1292968f_ac05_4a25_979d_3851b390bd91_a1
    (n m e s : ℕ)
    (hEuler : n + m = e + 2)
    (hSum : s = 2 * e)
    (hFaces : 3 * m ≤ s) :
    e + 6 ≤ 3 * n := by sorry
