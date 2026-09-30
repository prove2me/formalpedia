-- Prove2me | solution 2 for lean_workbook_plus_64149
-- status  : ACCEPTED   (prove)
-- author  : @evgeth
-- created : 2026-09-05T06:49:02.143097+00:00
-- url     : https://prove2.me/submissions/2b58774a-0f7d-4efc-90bf-a2a34cc94919

import Mathlib.Analysis.Complex.Basic

set_option autoImplicit false

theorem solution (a b c : ℝ) (hx: a > 0 ∧ b > 0 ∧ c > 0) (hab : a + b > c) (hbc : b + c > a) (hca : a + c > b) : a^3 + b^3 + 2 * (a + b) * c^2 ≥ c^3 + 2 * (a^2 + b^2) * c + a * b * c := by
  (intros; nlinarith [sq_nonneg (a), sq_nonneg (b), sq_nonneg (c), sq_nonneg (a - b), sq_nonneg (a - c), sq_nonneg (b - c), sq_nonneg (a + b), sq_nonneg (a + c), sq_nonneg (b + c)])
