-- Prove2me | Theorems.Thm_WilliamsonShmoys_euler_list_arithmetic__p2m_e180e171_1461_4456_9297_ea94a0392a1c_a11
-- name    : WilliamsonShmoys_euler_list_arithmetic__p2m_e180e171_1461_4456_9297_ea94a0392a1c_a11
-- status  : Proved
-- author  : @Eyal1990
-- created : 2026-10-29T21:36:11.138674+00:00
-- url     : https://prove2.me/theorems/0d07f6fa-22fb-40c6-956b-6dd2c3b01655
-- title:
--   List construction from Euler and edge bounds
-- statement:
--   For natural numbers n and m satisfying the connected-edge lower bound and simple-planar edge upper bound, there is a list whose length is m−n+2, whose entries sum to twice m, and whose entries are all at least three.
-- source:
--   David P. Williamson and David B. Shmoys, The Design of Approximation Algorithms, Cambridge University Press, 2011, author electronic manuscript, Section 10.2, proof of Theorem 10.11, pp. 270-272. https://doi.org/10.1017/CBO9780511921735. Bounded tree-width of the pieces: Robertson–Seymour (planar graphs of radius r have tree-width at most 3r+1) / Bodlaender (k-outerplanar graphs have tree-width at most 3k-1).

import Mathlib

set_option autoImplicit false

theorem WilliamsonShmoys_euler_list_arithmetic__p2m_e180e171_1461_4456_9297_ea94a0392a1c_a11 (n m : ℕ)
    (hnm : n ≤ m + 1)
    (hmn : m + 6 ≤ 3 * n) :
    ∃ f : ℕ, ∃ lengths : List ℕ,
      f + n = m + 2 ∧
      lengths.length = f ∧
      lengths.sum = 2 * m ∧
      ∀ x ∈ lengths, 3 ≤ x := by sorry
