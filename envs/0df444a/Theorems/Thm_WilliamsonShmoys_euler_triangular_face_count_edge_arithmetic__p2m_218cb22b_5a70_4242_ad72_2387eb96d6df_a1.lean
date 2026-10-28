-- Prove2me | Theorems.Thm_WilliamsonShmoys_euler_triangular_face_count_edge_arithmetic__p2m_218cb22b_5a70_4242_ad72_2387eb96d6df_a1
-- name    : WilliamsonShmoys.euler_triangular_face_count_edge_arithmetic__p2m_218cb22b_5a70_4242_ad72_2387eb96d6df_a1
-- status  : Proved
-- author  : @Eyal1990
-- created : 2026-10-28T18:40:08.974281+00:00
-- url     : https://prove2.me/theorems/ff8f0024-6a86-4383-8906-eff3d5e176a0
-- title:
--   Euler and triangular incidence imply the edge bound
-- statement:
--   If the face count and edge count satisfy Euler’s equation and every face contributes three incidences while every edge contributes two, then the edge lower bound follows by arithmetic.
-- source:
--   David P. Williamson and David B. Shmoys, The Design of Approximation Algorithms, Cambridge University Press, 2011, author electronic manuscript, Section 10.2, proof of Theorem 10.11, pp. 270-272. https://doi.org/10.1017/CBO9780511921735. Bounded tree-width of the pieces: Robertson–Seymour (planar graphs of radius r have tree-width at most 3r+1) / Bodlaender (k-outerplanar graphs have tree-width at most 3k-1).

import Mathlib

set_option autoImplicit false

theorem WilliamsonShmoys.euler_triangular_face_count_edge_arithmetic__p2m_218cb22b_5a70_4242_ad72_2387eb96d6df_a1
    (f n e : ℕ)
    (hEuler : f + n = e + 2)
    (hIncidence : 3 * f = 2 * e) :
    3 * n ≤ e + 6 := by sorry
