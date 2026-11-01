-- Prove2me | Theorems.Thm_WilliamsonShmoys_planar_facial_length_arithmetic__p2m_bc9cd380_c5b9_4141_b573_8fb0410f4911_a2
-- name    : WilliamsonShmoys.planar_facial_length_arithmetic__p2m_bc9cd380_c5b9_4141_b573_8fb0410f4911_a2
-- status  : Proved
-- author  : @Eyal1990
-- created : 2026-11-01T01:35:29.9729+00:00
-- url     : https://prove2.me/theorems/e91728de-d753-496a-9125-8e1323d67715
-- title:
--   Distribute total length across the face slots
-- statement:
--   This arithmetic child removes all finite-length construction from the parent. The hypotheses imply m + 2 - n ≥ 1 and 3 * (m + 2 - n) ≤ 2m. Choose one slot, give every slot length 3, and add the excess to the chosen slot. The positivity hypothesis hn and both edge inequalities are retained to account for natural subtraction and the total-length allowance.
-- source:
--   David P. Williamson and David B. Shmoys, The Design of Approximation Algorithms, Cambridge University Press, 2011, author electronic manuscript, Section 10.2, proof of Theorem 10.11, pp. 270-272. https://doi.org/10.1017/CBO9780511921735. Bounded tree-width of the pieces: Robertson–Seymour (planar graphs of radius r have tree-width at most 3r+1) / Bodlaender (k-outerplanar graphs have tree-width at most 3k-1).

import Mathlib

set_option autoImplicit false

open scoped BigOperators

theorem WilliamsonShmoys.planar_facial_length_arithmetic__p2m_bc9cd380_c5b9_4141_b573_8fb0410f4911_a2
    (n m : ℕ) (hn : 3 ≤ n) (hlower : n ≤ m + 1)
    (hupper : m ≤ 3 * n - 6) :
    ∃ (length : Fin (m + 2 - n) → ℕ),
      2 * m = ∑ i, length i ∧ ∀ i, 3 ≤ length i := by sorry
