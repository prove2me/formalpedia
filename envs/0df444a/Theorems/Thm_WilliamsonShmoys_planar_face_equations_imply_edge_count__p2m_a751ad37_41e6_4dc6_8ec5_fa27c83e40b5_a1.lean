-- Prove2me | Theorems.Thm_WilliamsonShmoys_planar_face_equations_imply_edge_count__p2m_a751ad37_41e6_4dc6_8ec5_fa27c83e40b5_a1
-- name    : WilliamsonShmoys.planar_face_equations_imply_edge_count__p2m_a751ad37_41e6_4dc6_8ec5_fa27c83e40b5_a1
-- status  : Proved
-- author  : @Eyal1990
-- created : 2026-10-30T04:47:33.408736+00:00
-- url     : https://prove2.me/theorems/e8a67fc1-1603-4c1a-995c-69d78565b21d
-- title:
--   The planar face equations determine the maximal edge count
-- statement:
--   If natural numbers n, m, and f satisfy Euler’s equation and the triangular-face edge-incidence equation, then m + 6 = 3n.
-- source:
--   David P. Williamson and David B. Shmoys, The Design of Approximation Algorithms, Cambridge University Press, 2011, author electronic manuscript, Section 10.2, proof of Theorem 10.11, pp. 270-272. https://doi.org/10.1017/CBO9780511921735. Bounded tree-width of the pieces: Robertson–Seymour (planar graphs of radius r have tree-width at most 3r+1) / Bodlaender (k-outerplanar graphs have tree-width at most 3k-1).

import Mathlib

set_option autoImplicit false

theorem WilliamsonShmoys.planar_face_equations_imply_edge_count__p2m_a751ad37_41e6_4dc6_8ec5_fa27c83e40b5_a1
    (n m f : ℕ)
    (hEuler : n + f = m + 2)
    (hTri : 3 * f = 2 * m) :
    m + 6 = 3 * n := by sorry
