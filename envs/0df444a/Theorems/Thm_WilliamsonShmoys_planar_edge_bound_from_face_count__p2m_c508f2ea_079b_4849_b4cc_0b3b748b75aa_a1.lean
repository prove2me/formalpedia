-- Prove2me | Theorems.Thm_WilliamsonShmoys_planar_edge_bound_from_face_count__p2m_c508f2ea_079b_4849_b4cc_0b3b748b75aa_a1
-- name    : WilliamsonShmoys.planar_edge_bound_from_face_count__p2m_c508f2ea_079b_4849_b4cc_0b3b748b75aa_a1
-- status  : Proved
-- author  : @Eyal1990
-- created : 2026-11-01T07:07:06.078181+00:00
-- url     : https://prove2.me/theorems/c68ec093-e7d9-409a-898a-12b057f8125e
-- title:
--   Derive the planar edge bound from Euler and face degrees
-- statement:
--   For natural vertex, edge, and face counts, the Euler relation and lower bound on total facial degree imply the planar edge bound.
-- source:
--   David P. Williamson and David B. Shmoys, The Design of Approximation Algorithms, Cambridge University Press, 2011, author electronic manuscript, Section 10.2, proof of Theorem 10.11, pp. 270-272. https://doi.org/10.1017/CBO9780511921735. Bounded tree-width of the pieces: Robertson–Seymour (planar graphs of radius r have tree-width at most 3r+1) / Bodlaender (k-outerplanar graphs have tree-width at most 3k-1).

import Mathlib

set_option autoImplicit false

theorem WilliamsonShmoys.planar_edge_bound_from_face_count__p2m_c508f2ea_079b_4849_b4cc_0b3b748b75aa_a1
    (n e f : Nat)
    (hn : 3 ≤ n)
    (heuler : e + 2 = n + f)
    (hdegree : 3 * f ≤ 2 * e) :
    e ≤ 3 * n - 6 := by
  sorry
