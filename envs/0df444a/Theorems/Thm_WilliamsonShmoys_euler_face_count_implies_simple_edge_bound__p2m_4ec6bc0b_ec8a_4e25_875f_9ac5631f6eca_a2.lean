-- Prove2me | Theorems.Thm_WilliamsonShmoys_euler_face_count_implies_simple_edge_bound__p2m_4ec6bc0b_ec8a_4e25_875f_9ac5631f6eca_a2
-- name    : WilliamsonShmoys.euler_face_count_implies_simple_edge_bound__p2m_4ec6bc0b_ec8a_4e25_875f_9ac5631f6eca_a2
-- status  : Proved
-- author  : @Eyal1990
-- created : 2026-10-31T22:03:24.706729+00:00
-- url     : https://prove2.me/theorems/b313ead8-bea6-43da-a93f-3edde09476dd
-- title:
--   Euler face counts imply the simple planar edge bound
-- statement:
--   For natural numbers n, f, and e, Euler’s relation, a total face-boundary length of twice the edge count, and a lower bound of three on every face length imply e + 6 ≤ 3n. Sum the pointwise length inequalities to obtain 3f ≤ 2e, then combine this with n + f = e + 2 by linear arithmetic.
-- source:
--   David P. Williamson and David B. Shmoys, The Design of Approximation Algorithms, Cambridge University Press, 2011, author electronic manuscript, Section 10.2, proof of Theorem 10.11, pp. 270-272. https://doi.org/10.1017/CBO9780511921735. Bounded tree-width of the pieces: Robertson–Seymour (planar graphs of radius r have tree-width at most 3r+1) / Bodlaender (k-outerplanar graphs have tree-width at most 3k-1).

import Mathlib

set_option autoImplicit false

theorem WilliamsonShmoys.euler_face_count_implies_simple_edge_bound__p2m_4ec6bc0b_ec8a_4e25_875f_9ac5631f6eca_a2
    (n f e : ℕ) (length : Fin f → ℕ)
    (hEuler : n + f = e + 2)
    (hIncidence : 2 * e = ∑ i, length i)
    (hLength : ∀ i, 3 ≤ length i) :
    e + 6 ≤ 3 * n := by sorry
