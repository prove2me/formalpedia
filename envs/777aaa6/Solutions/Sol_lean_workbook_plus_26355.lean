-- Prove2me | solution 1 for lean_workbook_plus_26355
-- status  : ACCEPTED   (prove)
-- author  : @evgeth
-- created : 2026-09-05T12:25:55.681676+00:00
-- url     : https://prove2.me/submissions/e0db5f35-404c-42b2-bf47-9b0f7952eb28

import Mathlib.Analysis.Complex.Basic

set_option autoImplicit false

theorem solution (a b c : ℝ) (hab : a + b + c = 1) : a^3 + b^3 + c^3 = 1 + 3 * (a * b * c - a * b - b * c - c * a) := by
  (intros; nlinarith [sq_nonneg (a), sq_nonneg (b), sq_nonneg (c), sq_nonneg (a - b), sq_nonneg (a - c), sq_nonneg (b - c), sq_nonneg (a + b), sq_nonneg (a + c), sq_nonneg (b + c)])
