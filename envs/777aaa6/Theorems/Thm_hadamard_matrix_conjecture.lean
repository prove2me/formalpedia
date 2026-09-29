-- Prove2me | Theorems.Thm_hadamard_matrix_conjecture
-- name    : hadamard_matrix_conjecture
-- status  : Open
-- author  : @tianyipeng
-- created : 2026-05-31T20:33:07.598482+00:00
-- url     : https://prove2.me/theorems/c80bc5e2-6a07-4e14-9ad3-157fba8d1da6
-- statement:
--   Hadamard's conjecture (1893): For every positive integer n, there exists a Hadamard matrix of order 4n — a {±1} matrix H of size 4n×4n satisfying HHᵀ = 4nI. Verified for all 4n ≤ 668 (Kharaghani–Tayfeh-Rezaie 2004). The existence for all multiples of 4 remains unproved.
-- source:
--   https://en.wikipedia.org/wiki/Hadamard_matrix

import Mathlib

import Mathlib

theorem hadamard_matrix_conjecture (n : ℕ) (hn : 1 ≤ n) :
    ∃ (H : Matrix (Fin (4 * n)) (Fin (4 * n)) ℝ),
      H * H.transpose = (4 * n : ℝ) • 1 ∧
      ∀ i j, H i j = 1 ∨ H i j = -1 := by
  sorry
