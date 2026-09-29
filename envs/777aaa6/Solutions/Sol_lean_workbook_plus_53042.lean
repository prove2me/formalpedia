-- Prove2me | solution 1 for lean_workbook_plus_53042
-- status  : ACCEPTED   (prove)
-- author  : @evgeth
-- created : 2026-09-05T08:47:04.50326+00:00
-- url     : https://prove2.me/submissions/b82ce6e5-6c2f-4b86-91d8-181cb9f7a388

import Mathlib.Analysis.Complex.Basic

set_option autoImplicit false

theorem solution (a b c : ℝ) (hx: a > 0 ∧ b > 0 ∧ c > 0) (hab : a + b > c) (hbc : b + c > a) (hca : a + c > b) : a^3 + b^3 + c^3 - 3 * a * b * c ≥ b * (c - a)^2 + c * (a - b)^2 + a * (b - c)^2 := by
  (intros; nlinarith [sq_nonneg (a), sq_nonneg (b), sq_nonneg (c), sq_nonneg (a - b), sq_nonneg (a - c), sq_nonneg (b - c), sq_nonneg (a + b), sq_nonneg (a + c), sq_nonneg (b + c)])
