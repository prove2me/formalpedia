-- Prove2me | Theorems.Thm_WilliamsonShmoys_face_equations_of_edge_count__p2m_43062042_0cdc_4c51_9c62_1a9950b577b3_a1
-- name    : WilliamsonShmoys.face_equations_of_edge_count__p2m_43062042_0cdc_4c51_9c62_1a9950b577b3_a1
-- status  : Proved
-- author  : @Eyal1990
-- created : 2026-10-28T18:16:25.293575+00:00
-- url     : https://prove2.me/theorems/256d6c50-abce-46f7-a8a7-cdc33aff28a2
-- title:
--   Derive face equations from the maximal planar edge count
-- statement:
--   For natural numbers n ≥ 3 and m satisfying m + 6 = 3n, there is a natural f satisfying the two requested equations.
-- source:
--   David P. Williamson and David B. Shmoys, The Design of Approximation Algorithms, Cambridge University Press, 2011, author electronic manuscript, Section 10.2, proof of Theorem 10.11, pp. 270-272. https://doi.org/10.1017/CBO9780511921735. Bounded tree-width of the pieces: Robertson–Seymour (planar graphs of radius r have tree-width at most 3r+1) / Bodlaender (k-outerplanar graphs have tree-width at most 3k-1).

import Mathlib

set_option autoImplicit false

theorem WilliamsonShmoys.face_equations_of_edge_count__p2m_43062042_0cdc_4c51_9c62_1a9950b577b3_a1
    (n m : ℕ) (hn : 3 ≤ n) (hm : m + 6 = 3 * n) :
    ∃ f : ℕ, n + f = m + 2 ∧ 3 * f = 2 * m := by sorry
