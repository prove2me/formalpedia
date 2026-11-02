-- Prove2me | Theorems.Thm_WilliamsonShmoys_nat_euler_face_incidence_edge_bound__p2m_41a70d26_a66a_4916_a2c6_308943ffd553_a1
-- name    : WilliamsonShmoys.nat_euler_face_incidence_edge_bound__p2m_41a70d26_a66a_4916_a2c6_308943ffd553_a1
-- status  : Proved
-- author  : @Eyal1990
-- created : 2026-11-01T07:51:16.328275+00:00
-- url     : https://prove2.me/theorems/4dd04aa3-184e-464d-ba9a-7122e069810e
-- title:
--   Arithmetic edge bound from Euler and face incidences
-- statement:
--   For natural numbers n, m, and f, if n is at least three, n + f = m + 2, and 3f ≤ 2m, then m ≤ 3n − 6. This removes the arithmetic from the parent: combine the equation and incidence inequality to obtain m + 6 ≤ 3n, then convert to the truncated natural subtraction bound. It is independently provable by natural-number arithmetic.
-- source:
--   David P. Williamson and David B. Shmoys, The Design of Approximation Algorithms, Cambridge University Press, 2011, author electronic manuscript, Section 10.2, proof of Theorem 10.11, pp. 270-272. https://doi.org/10.1017/CBO9780511921735. Bounded tree-width of the pieces: Robertson–Seymour (planar graphs of radius r have tree-width at most 3r+1) / Bodlaender (k-outerplanar graphs have tree-width at most 3k-1).

import Mathlib

set_option autoImplicit false

theorem WilliamsonShmoys.nat_euler_face_incidence_edge_bound__p2m_41a70d26_a66a_4916_a2c6_308943ffd553_a1
    (n m f : Nat) (hn : 3 ≤ n)
    (heuler : n + f = m + 2)
    (hinc : 3 * f ≤ 2 * m) :
    m ≤ 3 * n - 6 := by sorry
