-- Prove2me | solution 1 for lean_workbook_plus_69447
-- status  : ACCEPTED   (prove)
-- author  : @ryanshin
-- created : 2026-09-05T07:42:21.416201+00:00
-- url     : https://prove2.me/submissions/4da55c97-b916-4fa6-b0a8-6ec9df18c816

import Mathlib.Analysis.Complex.Basic

theorem solution (x : ℝ) : 2 * x ^ 2 + 3 * x - 5 = 0 ↔ x = 1 ∨ x = -5 / 2 := by
  constructor
  · intro h
    have h' : (x - 1) * (2 * x + 5) = 0 := by linear_combination h
    rcases mul_eq_zero.mp h' with h1 | h2
    · left; linarith
    · right; linarith
  · rintro (rfl | rfl) <;> norm_num
