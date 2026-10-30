-- Prove2me | Theorems.Thm_WilliamsonShmoys_face_equations_of_edge_count__p2m_8a77ef9e_b782_4199_be1b_94d3ad7b0b10_a4
-- name    : WilliamsonShmoys.face_equations_of_edge_count__p2m_8a77ef9e_b782_4199_be1b_94d3ad7b0b10_a4
-- status  : Proved
-- author  : @Eyal1990
-- created : 2026-10-29T23:41:30.375523+00:00
-- url     : https://prove2.me/theorems/bcd608c5-8ace-418e-85c2-4517b832c6e3
-- title:
--   Derive face equations from the planar edge count
-- statement:
--   From n ≥ 3 and m + 6 = 3n, choose f = 2n − 4 and prove both equalities by arithmetic. This independently removes the arithmetic conversion from the parent.
-- source:
--   David P. Williamson and David B. Shmoys, The Design of Approximation Algorithms, Cambridge University Press, 2011, author electronic manuscript, Section 10.2, proof of Theorem 10.11, pp. 270-272. https://doi.org/10.1017/CBO9780511921735. Bounded tree-width of the pieces: Robertson–Seymour (planar graphs of radius r have tree-width at most 3r+1) / Bodlaender (k-outerplanar graphs have tree-width at most 3k-1).

import Mathlib

theorem WilliamsonShmoys.face_equations_of_edge_count__p2m_8a77ef9e_b782_4199_be1b_94d3ad7b0b10_a4
    (n m : Nat) (hCard : 3 ≤ n) (hm : m + 6 = 3 * n) :
    ∃ f : Nat, n + f = m + 2 ∧ 3 * f = 2 * m := by sorry
