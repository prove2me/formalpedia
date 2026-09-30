-- Prove2me | solution 2 for lean_workbook_plus_78078
-- status  : ACCEPTED   (prove)
-- author  : @evgeth
-- created : 2026-09-05T04:24:44.350137+00:00
-- url     : https://prove2.me/submissions/8790ef23-f76d-40d2-8826-8f32684bcd18

import Mathlib.Analysis.Complex.Basic

set_option autoImplicit false

theorem solution (a b c : ℝ) (hx: a > 0 ∧ b > 0 ∧ c > 0) (hab : a + b > c) (hbc : b + c > a) (hca : a + c > b) : a^2 + b^2 + c^2 < 2 * (a * b + b * c + c * a) := by
  (intros; nlinarith [sq_nonneg (a), sq_nonneg (b), sq_nonneg (c), sq_nonneg (a - b), sq_nonneg (a - c), sq_nonneg (b - c), sq_nonneg (a + b), sq_nonneg (a + c), sq_nonneg (b + c)])
