-- Prove2me | solution 1 for lean_workbook_plus_37505
-- status  : ACCEPTED   (prove)
-- author  : @ryanshin
-- created : 2026-09-05T19:56:21.494914+00:00
-- url     : https://prove2.me/submissions/1be2b2a0-de15-4f02-97f8-d0d7868b5eab

import Mathlib.Analysis.Complex.Basic

theorem solution (x : ℝ) (hx : 0 < x ∧ x < 1) :
    ∃ a b : ℤ, a > 0 ∧ b > 0 ∧ Int.gcd a b = 1 ∧ |x - a / b| < 1 / b^2 := by
  refine ⟨1, 1, by norm_num, by norm_num, by norm_num, ?_⟩
  simp only [Int.cast_one, div_one, one_pow]
  rw [abs_lt]
  constructor <;> linarith [hx.1, hx.2]
