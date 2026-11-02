-- Prove2me | Theorems.Thm_WilliamsonShmoys_euler_face_data_implies_edge_bound__p2m_844ee2d0_ef82_4c36_8373_ea0ee656ba91_a2
-- name    : WilliamsonShmoys.euler_face_data_implies_edge_bound__p2m_844ee2d0_ef82_4c36_8373_ea0ee656ba91_a2
-- status  : Proved
-- author  : @Eyal1990
-- created : 2026-11-01T13:02:58.886318+00:00
-- url     : https://prove2.me/theorems/6e58aed5-929b-46ae-8df7-e70862c68cc0
-- title:
--   Euler and face data imply the edge bound
-- statement:
--   If n is at least three, m ≤ M, n + f = M + 2, and 3f ≤ 2M, then m + 6 ≤ 3n.
-- source:
--   David P. Williamson and David B. Shmoys, The Design of Approximation Algorithms, Cambridge University Press, 2011, author electronic manuscript, Section 10.2, proof of Theorem 10.11, pp. 270-272. https://doi.org/10.1017/CBO9780511921735. Bounded tree-width of the pieces: Robertson–Seymour (planar graphs of radius r have tree-width at most 3r+1) / Bodlaender (k-outerplanar graphs have tree-width at most 3k-1).

import Mathlib

set_option autoImplicit false

theorem WilliamsonShmoys.euler_face_data_implies_edge_bound__p2m_844ee2d0_ef82_4c36_8373_ea0ee656ba91_a2
    (n m M f : ℕ) (hn : 3 ≤ n) (hm : m ≤ M)
    (heuler : n + f = M + 2) (hfaces : 3 * f ≤ 2 * M) :
    m + 6 ≤ 3 * n := by sorry
