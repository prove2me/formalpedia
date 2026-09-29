-- Prove2me | solution 1 for lean_workbook_plus_32544
-- status  : ACCEPTED   (prove)
-- author  : @evgeth
-- created : 2026-09-05T11:43:43.713947+00:00
-- url     : https://prove2.me/submissions/fc826cca-6121-4311-b3c9-28041ea4e429

import Mathlib.Analysis.Complex.Basic

set_option autoImplicit false

theorem solution (a b c : ℝ) (hx: a > 0 ∧ b > 0 ∧ c > 0) (hab : a + b > c) (hbc : b + c > a) (hca : a + c > b) : 3 * (b * c + c * a + a * b) ≤ (a + b + c) ^ 2 ∧ (a + b + c) ^ 2 < 4 * (b * c + c * a + a * b) := by
  (intros; constructor <;> nlinarith [sq_nonneg (a), sq_nonneg (b), sq_nonneg (c), sq_nonneg (a - b), sq_nonneg (a - c), sq_nonneg (b - c), sq_nonneg (a + b), sq_nonneg (a + c), sq_nonneg (b + c)])
