-- Prove2me | Theorems.Thm_WilliamsonShmoys_triangulated_counts_lower_bound__p2m_36795df0_a9ab_414e_b2f3_447339417680_a3
-- name    : WilliamsonShmoys.triangulated_counts_lower_bound__p2m_36795df0_a9ab_414e_b2f3_447339417680_a3
-- status  : Proved
-- author  : @Eyal1990
-- created : 2026-11-01T02:00:06.248782+00:00
-- url     : https://prove2.me/theorems/5500ba90-1597-49fe-86b1-ac22e4cb69d9
-- title:
--   Triangulated Euler counts imply the edge lower bound
-- statement:
--   For natural numbers n, m, and f, if n is at least three, n + f = m + 2, and 3f = 2m, then m is at least 3n − 6.
-- source:
--   David P. Williamson and David B. Shmoys, The Design of Approximation Algorithms, Cambridge University Press, 2011, author electronic manuscript, Section 10.2, proof of Theorem 10.11, pp. 270-272. https://doi.org/10.1017/CBO9780511921735. Bounded tree-width of the pieces: Robertson–Seymour (planar graphs of radius r have tree-width at most 3r+1) / Bodlaender (k-outerplanar graphs have tree-width at most 3k-1).

import Mathlib
set_option autoImplicit false

theorem WilliamsonShmoys.triangulated_counts_lower_bound__p2m_36795df0_a9ab_414e_b2f3_447339417680_a3 (n m : ℕ) (hn : 3 ≤ n) (f : ℕ) (hEuler : n + f = m + 2) (htri : 3 * f = 2 * m) : 3 * n - 6 ≤ m := by sorry
