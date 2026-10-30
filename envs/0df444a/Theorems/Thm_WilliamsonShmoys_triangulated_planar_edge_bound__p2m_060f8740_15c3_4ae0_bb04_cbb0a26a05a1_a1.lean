-- Prove2me | Theorems.Thm_WilliamsonShmoys_triangulated_planar_edge_bound__p2m_060f8740_15c3_4ae0_bb04_cbb0a26a05a1_a1
-- name    : WilliamsonShmoys.triangulated_planar_edge_bound__p2m_060f8740_15c3_4ae0_bb04_cbb0a26a05a1_a1
-- status  : Proved
-- author  : @Eyal1990
-- created : 2026-10-29T22:05:20.919759+00:00
-- url     : https://prove2.me/theorems/892e1531-407e-48de-b4fd-6f503b201d63
-- title:
--   Edge bound from triangulated planar face counts
-- statement:
--   For natural numbers n, m, and f, Euler’s equation and the triangular face-incidence equation imply 3n ≤ m + 6. The condition n ≥ 3 is retained from the parent; the arithmetic implication itself follows by linear arithmetic from the two equations. This removes the numerical manipulation from the drawing argument and applies uniformly at n = 3.
-- source:
--   David P. Williamson and David B. Shmoys, The Design of Approximation Algorithms, Cambridge University Press, 2011, author electronic manuscript, Section 10.2, proof of Theorem 10.11, pp. 270-272. https://doi.org/10.1017/CBO9780511921735. Bounded tree-width of the pieces: Robertson–Seymour (planar graphs of radius r have tree-width at most 3r+1) / Bodlaender (k-outerplanar graphs have tree-width at most 3k-1).

import Mathlib

set_option autoImplicit false

theorem WilliamsonShmoys.triangulated_planar_edge_bound__p2m_060f8740_15c3_4ae0_bb04_cbb0a26a05a1_a1
    (n m f : Nat)
    (hn : 3 <= n)
    (hEuler : n + f = m + 2)
    (htri : 3 * f = 2 * m) :
    3 * n <= m + 6 := by sorry
