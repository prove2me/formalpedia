-- Prove2me | solution 1 for lean_workbook_plus_16733
-- status  : ACCEPTED   (prove)
-- author  : @evgeth
-- created : 2026-09-05T13:21:51.837039+00:00
-- url     : https://prove2.me/submissions/25cbe4f5-ded3-4243-bbc1-ca3f7887d090

import Mathlib.Analysis.Complex.Basic

set_option autoImplicit false

theorem solution (a b c : ℝ) (hx: a > 0 ∧ b > 0 ∧ c > 0) (hab : a + b > c) (hbc : b + c > a) (hca : a + c > b) : a^3 + b^3 + c^3 + 3 * a * b * c ≥ a * b * (a + b) + b * c * (b + c) + c * a * (c + a) := by
  (intros; nlinarith [sq_nonneg (a), sq_nonneg (b), sq_nonneg (c), sq_nonneg (a - b), sq_nonneg (a - c), sq_nonneg (b - c), sq_nonneg (a + b), sq_nonneg (a + c), sq_nonneg (b + c)])
