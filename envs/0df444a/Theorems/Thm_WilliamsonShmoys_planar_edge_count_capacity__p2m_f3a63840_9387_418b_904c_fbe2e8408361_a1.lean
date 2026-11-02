-- Prove2me | Theorems.Thm_WilliamsonShmoys_planar_edge_count_capacity__p2m_f3a63840_9387_418b_904c_fbe2e8408361_a1
-- name    : WilliamsonShmoys.planar_edge_count_capacity__p2m_f3a63840_9387_418b_904c_fbe2e8408361_a1
-- status  : Proved
-- author  : @Eyal1990
-- created : 2026-11-01T17:18:40.837633+00:00
-- url     : https://prove2.me/theorems/b2688200-28db-4a6c-a0d3-104a9c6e1818
-- title:
--   The planar target count fits within the complete graph
-- statement:
--   For n≥3, the target edge count 3n−6 is at most the number n(n−1)/2 of unordered pairs of distinct vertices.
-- source:
--   David P. Williamson and David B. Shmoys, The Design of Approximation Algorithms, Cambridge University Press, 2011, author electronic manuscript, Section 10.2, proof of Theorem 10.11, pp. 270-272. https://doi.org/10.1017/CBO9780511921735. Bounded tree-width of the pieces: Robertson–Seymour (planar graphs of radius r have tree-width at most 3r+1) / Bodlaender (k-outerplanar graphs have tree-width at most 3k-1).

import Mathlib

set_option autoImplicit false

theorem WilliamsonShmoys.planar_edge_count_capacity__p2m_f3a63840_9387_418b_904c_fbe2e8408361_a1
    (n : Nat) (hn : 3 ≤ n) :
    3 * n - 6 ≤ n * (n - 1) / 2 := by sorry
