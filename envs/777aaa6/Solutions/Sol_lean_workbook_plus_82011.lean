-- Prove2me | solution 1 for lean_workbook_plus_82011
-- status  : ACCEPTED   (prove)
-- author  : @ryanshin
-- created : 2026-09-05T04:14:24.591954+00:00
-- url     : https://prove2.me/submissions/cedd4e90-72c0-4cac-bc6c-947a76080ebf

import Mathlib.Analysis.Complex.Basic
import Mathlib.Tactic

theorem solution (x : ℝ) (f : ℝ → ℝ)
    (h₀ : ∀ x, f x = x ^ 2 - 2) (h₁ : f x = x) : x = -1 ∨ x = 2 := by
  have h : (x + 1) * (x - 2) = 0 := by nlinarith [h₀ x]
  rcases mul_eq_zero.mp h with h | h
  · left
    linarith
  · right
    linarith
