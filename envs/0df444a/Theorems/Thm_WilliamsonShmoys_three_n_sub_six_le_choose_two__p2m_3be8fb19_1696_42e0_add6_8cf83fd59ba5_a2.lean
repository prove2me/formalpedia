-- Prove2me | Theorems.Thm_WilliamsonShmoys_three_n_sub_six_le_choose_two__p2m_3be8fb19_1696_42e0_add6_8cf83fd59ba5_a2
-- name    : WilliamsonShmoys.three_n_sub_six_le_choose_two__p2m_3be8fb19_1696_42e0_add6_8cf83fd59ba5_a2
-- status  : Proved
-- author  : @Eyal1990
-- created : 2026-11-01T17:10:25.155833+00:00
-- url     : https://prove2.me/theorems/40310037-f5c7-4de7-aa6e-3a8d84e031c9
-- title:
--   Compare the planar edge bound with all possible pairs
-- statement:
--   For every natural number n at least 3, the bound 3n−6 is at most the number of unordered pairs among n vertices.
-- source:
--   David P. Williamson and David B. Shmoys, The Design of Approximation Algorithms, Cambridge University Press, 2011, author electronic manuscript, Section 10.2, proof of Theorem 10.11, pp. 270-272. https://doi.org/10.1017/CBO9780511921735. Bounded tree-width of the pieces: Robertson–Seymour (planar graphs of radius r have tree-width at most 3r+1) / Bodlaender (k-outerplanar graphs have tree-width at most 3k-1).

import Mathlib

theorem WilliamsonShmoys.three_n_sub_six_le_choose_two__p2m_3be8fb19_1696_42e0_add6_8cf83fd59ba5_a2
    (n : Nat) (hn : 3 ≤ n) :
    3 * n - 6 ≤ Nat.choose n 2 := by sorry
