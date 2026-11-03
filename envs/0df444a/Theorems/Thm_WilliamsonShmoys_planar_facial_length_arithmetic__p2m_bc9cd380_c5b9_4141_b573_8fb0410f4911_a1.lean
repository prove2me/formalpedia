-- Prove2me | Theorems.Thm_WilliamsonShmoys_planar_facial_length_arithmetic__p2m_bc9cd380_c5b9_4141_b573_8fb0410f4911_a1
-- name    : WilliamsonShmoys.planar_facial_length_arithmetic__p2m_bc9cd380_c5b9_4141_b573_8fb0410f4911_a1
-- status  : Proved
-- author  : @Eyal1990
-- created : 2026-10-31T22:21:32.622901+00:00
-- url     : https://prove2.me/theorems/b1ee2c96-5e10-461f-a614-3e0b8c770241
-- title:
--   Distribute total length across the face slots
-- statement:
--   For natural numbers n and m with 3 ≤ n, n ≤ m + 1, and m ≤ 3n − 6, the m + 2 − n slots can be assigned natural lengths, each at least 3, summing to 2m. The lower bound makes the slot count positive, and the upper bound supplies enough total length. An elementary proof gives every slot length 3, then adds the remaining excess to one slot.
-- source:
--   David P. Williamson and David B. Shmoys, The Design of Approximation Algorithms, Cambridge University Press, 2011, author electronic manuscript, Section 10.2, proof of Theorem 10.11, pp. 270-272. https://doi.org/10.1017/CBO9780511921735. Bounded tree-width of the pieces: Robertson–Seymour (planar graphs of radius r have tree-width at most 3r+1) / Bodlaender (k-outerplanar graphs have tree-width at most 3k-1).

import Mathlib

set_option autoImplicit false

open scoped BigOperators

theorem WilliamsonShmoys.planar_facial_length_arithmetic__p2m_bc9cd380_c5b9_4141_b573_8fb0410f4911_a1
    (n m : ℕ) (hn : 3 ≤ n) (hlower : n ≤ m + 1)
    (hupper : m ≤ 3 * n - 6) :
    ∃ (length : Fin (m + 2 - n) → ℕ),
      2 * m = ∑ i, length i ∧ ∀ i, 3 ≤ length i := by sorry
