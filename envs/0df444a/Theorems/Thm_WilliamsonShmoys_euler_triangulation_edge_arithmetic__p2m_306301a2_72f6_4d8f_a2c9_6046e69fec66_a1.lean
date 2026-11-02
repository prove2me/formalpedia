-- Prove2me | Theorems.Thm_WilliamsonShmoys_euler_triangulation_edge_arithmetic__p2m_306301a2_72f6_4d8f_a2c9_6046e69fec66_a1
-- name    : WilliamsonShmoys.euler_triangulation_edge_arithmetic__p2m_306301a2_72f6_4d8f_a2c9_6046e69fec66_a1
-- status  : Proved
-- author  : @Eyal1990
-- created : 2026-11-01T12:59:59.365871+00:00
-- url     : https://prove2.me/theorems/7238cbb0-11db-4c95-aa62-cf2dce972fda
-- title:
--   Edge bound from Euler and triangular-face counts
-- statement:
--   For natural numbers n, e, and f, Euler’s equation and the triangular-face incidence equation imply the planar edge bound. The proof is integer algebra; the lower bound on n records the target’s boundary hypothesis.
-- source:
--   David P. Williamson and David B. Shmoys, The Design of Approximation Algorithms, Cambridge University Press, 2011, author electronic manuscript, Section 10.2, proof of Theorem 10.11, pp. 270-272. https://doi.org/10.1017/CBO9780511921735. Bounded tree-width of the pieces: Robertson–Seymour (planar graphs of radius r have tree-width at most 3r+1) / Bodlaender (k-outerplanar graphs have tree-width at most 3k-1).

import Mathlib

theorem WilliamsonShmoys.euler_triangulation_edge_arithmetic__p2m_306301a2_72f6_4d8f_a2c9_6046e69fec66_a1
    (n e f : ℕ)
    (hn : 3 <= n)
    (hEuler : (n : ℤ) - (e : ℤ) + (f : ℤ) = 2)
    (htri : 3 * f = 2 * e) :
    e + 6 <= 3 * n := by sorry
