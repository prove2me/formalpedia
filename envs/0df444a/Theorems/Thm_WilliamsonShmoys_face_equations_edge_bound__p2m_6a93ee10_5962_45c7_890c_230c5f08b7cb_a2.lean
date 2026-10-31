-- Prove2me | Theorems.Thm_WilliamsonShmoys_face_equations_edge_bound__p2m_6a93ee10_5962_45c7_890c_230c5f08b7cb_a2
-- name    : WilliamsonShmoys.face_equations_edge_bound__p2m_6a93ee10_5962_45c7_890c_230c5f08b7cb_a2
-- status  : Open
-- author  : @Eyal1990
-- created : 2026-10-30T06:06:31.645761+00:00
-- url     : https://prove2.me/theorems/36ed464b-6556-46f6-9ade-a2de29705f3b
-- title:
--   The Euler and face-incidence equations imply the planar edge bound
-- statement:
--   For natural numbers n, m, f with n at least three, Euler’s equation and the triangular-face edge-incidence equation imply the edge lower bound (in fact, equality). This is a standalone arithmetic step, provable by linear arithmetic after handling natural subtraction using n ≥ 3.
-- source:
--   David P. Williamson and David B. Shmoys, The Design of Approximation Algorithms, Cambridge University Press, 2011, author electronic manuscript, Section 10.2, proof of Theorem 10.11, pp. 270-272. https://doi.org/10.1017/CBO9780511921735. Bounded tree-width of the pieces: Robertson–Seymour (planar graphs of radius r have tree-width at most 3r+1) / Bodlaender (k-outerplanar graphs have tree-width at most 3k-1).

import Mathlib

set_option autoImplicit false

theorem WilliamsonShmoys.face_equations_edge_bound__p2m_6a93ee10_5962_45c7_890c_230c5f08b7cb_a2
    (n m f : Nat)
    (hn : 3 <= n)
    (hEuler : n + f = m + 2)
    (hIncidence : 3 * f = 2 * m) :
    3 * n - 6 <= m := by sorry
