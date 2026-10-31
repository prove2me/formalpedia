-- Prove2me | Theorems.Thm_WilliamsonShmoys_edge_bound_from_euler_data__p2m_49196ac4_b46c_446f_b424_262126b1b13c_a2
-- name    : WilliamsonShmoys.edge_bound_from_euler_data__p2m_49196ac4_b46c_446f_b424_262126b1b13c_a2
-- status  : Proved
-- author  : @Eyal1990
-- created : 2026-10-30T10:15:13.619247+00:00
-- url     : https://prove2.me/theorems/5a3eed09-f83c-49ce-a299-8e030eca2e67
-- title:
--   Edge bound from Euler and face data
-- statement:
--   For natural numbers n, m', and f, if n is at least three, n + f = m' + 2, and 3f ≤ 2m', then m' ≤ 3n − 6. The independent proof route is linear arithmetic: substitute the Euler relation into the incidence inequality and use n ≥ 3.
-- source:
--   David P. Williamson and David B. Shmoys, The Design of Approximation Algorithms, Cambridge University Press, 2011, author electronic manuscript, Section 10.2, proof of Theorem 10.11, pp. 270-272. https://doi.org/10.1017/CBO9780511921735. Bounded tree-width of the pieces: Robertson–Seymour (planar graphs of radius r have tree-width at most 3r+1) / Bodlaender (k-outerplanar graphs have tree-width at most 3k-1).

import Mathlib

set_option autoImplicit false

theorem WilliamsonShmoys.edge_bound_from_euler_data__p2m_49196ac4_b46c_446f_b424_262126b1b13c_a2 (n m' f : ℕ) (hn : 3 ≤ n) (hm : n + f = m' + 2) (hf : 3 * f ≤ 2 * m') : m' ≤ 3 * n - 6 := by sorry
