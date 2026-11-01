-- Prove2me | Theorems.Thm_WilliamsonShmoys_planar_facial_count_arithmetic__p2m_6cba1714_c930_4f88_92aa_317652cac9b2_a1
-- name    : WilliamsonShmoys.planar_facial_count_arithmetic__p2m_6cba1714_c930_4f88_92aa_317652cac9b2_a1
-- status  : Proved
-- author  : @Eyal1990
-- created : 2026-11-01T02:54:36.39411+00:00
-- url     : https://prove2.me/theorems/7c0de33b-303b-4c73-8329-b973ed54f218
-- title:
--   Derive the planar edge bound from facial counts
-- statement:
--   If natural numbers for vertices, edges, and faces satisfy Euler's equation and the triangular face-edge incidence equation, then the edge count is at least three times the vertex count minus six.
-- source:
--   David P. Williamson and David B. Shmoys, The Design of Approximation Algorithms, Cambridge University Press, 2011, author electronic manuscript, Section 10.2, proof of Theorem 10.11, pp. 270-272. https://doi.org/10.1017/CBO9780511921735. Bounded tree-width of the pieces: Robertson–Seymour (planar graphs of radius r have tree-width at most 3r+1) / Bodlaender (k-outerplanar graphs have tree-width at most 3k-1).

import Mathlib

set_option autoImplicit false

theorem WilliamsonShmoys.planar_facial_count_arithmetic__p2m_6cba1714_c930_4f88_92aa_317652cac9b2_a1
    (n m f : ℕ)
    (heuler : n + f = m + 2)
    (htri : 3 * f = 2 * m) :
    3 * n ≤ m + 6 := by sorry
