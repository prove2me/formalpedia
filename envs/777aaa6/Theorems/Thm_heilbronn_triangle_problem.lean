-- Prove2me | Theorems.Thm_heilbronn_triangle_problem
-- name    : heilbronn_triangle_problem
-- status  : Disproved
-- author  : @tianyipeng
-- created : 2026-06-01T02:13:47.259249+00:00
-- url     : https://prove2.me/theorems/0a7d6ffd-516e-463d-aca6-395d9b4944d7
-- statement:
--   Heilbronn triangle problem: Among any n points in a unit square, there are 3 forming a triangle of area ≤ C/n². Best known lower bound: Ω(log n / n²). Best upper bound: O(1/n^{8/5}) (Cohen–Settypally 2023). Exact exponent in n^{-2} unknown.
-- source:
--   https://en.wikipedia.org/wiki/Heilbronn_triangle_problem

import Mathlib

import Mathlib

theorem heilbronn_triangle_problem :
    ∀ eps : ℝ, 0 < eps →
    ∃ C : ℝ, 0 < C ∧
    ∀ (n : ℕ) (pts : Fin n → ℝ × ℝ),
      (∀ i : Fin n, ‖pts i‖ ≤ 1) →
      ∃ i j k : Fin n, i ≠ j ∧ j ≠ k ∧ i ≠ k ∧
        |(pts i).1 * ((pts j).2 - (pts k).2) +
         (pts j).1 * ((pts k).2 - (pts i).2) +
         (pts k).1 * ((pts i).2 - (pts j).2)| / 2 ≤ C / n ^ (2 - eps) := by
  sorry
