-- Prove2me | Theorems.Thm_WilliamsonShmoys_planar_euler_edge_arithmetic__p2m_00ee0ef8_811a_4a39_b8c0_1ed175b9b4ef_a1
-- name    : WilliamsonShmoys.planar_euler_edge_arithmetic__p2m_00ee0ef8_811a_4a39_b8c0_1ed175b9b4ef_a1
-- status  : Proved
-- author  : @Eyal1990
-- created : 2026-11-01T07:16:00.567062+00:00
-- url     : https://prove2.me/theorems/a072d2e4-c72b-4ace-978a-1806f973256b
-- title:
--   Euler face-count inequalities imply the planar edge bound
-- statement:
--   If the Euler equation holds for vertex, edge, and face counts and the total face-boundary length is at most twice the edge count, then the edge count is at most `3n − 6`. The hypothesis `n ≥ 3` is preserved; this child is a direct natural-number arithmetic step.
-- source:
--   David P. Williamson and David B. Shmoys, The Design of Approximation Algorithms, Cambridge University Press, 2011, author electronic manuscript, Section 10.2, proof of Theorem 10.11, pp. 270-272. https://doi.org/10.1017/CBO9780511921735. Bounded tree-width of the pieces: Robertson–Seymour (planar graphs of radius r have tree-width at most 3r+1) / Bodlaender (k-outerplanar graphs have tree-width at most 3k-1).

import Mathlib

set_option autoImplicit false

theorem WilliamsonShmoys.planar_euler_edge_arithmetic__p2m_00ee0ef8_811a_4a39_b8c0_1ed175b9b4ef_a1
    (n m f : ℕ)
    (hn : 3 ≤ n)
    (heuler : n + f = m + 2)
    (hboundary : 3 * f ≤ 2 * m) :
    m + 6 ≤ 3 * n := by sorry
