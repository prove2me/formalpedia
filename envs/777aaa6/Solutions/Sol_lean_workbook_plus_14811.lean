-- Prove2me | solution 1 for lean_workbook_plus_14811
-- status  : ACCEPTED   (prove)
-- author  : @evgeth
-- created : 2026-09-05T13:31:13.853922+00:00
-- url     : https://prove2.me/submissions/7a514d1e-11c9-41f9-a652-816f80289419

import Mathlib.Analysis.Complex.Basic

set_option autoImplicit false

theorem solution (a b c : ℝ) (h₁ : a + b - c = 5) (h₂ : a - b + c = 7) : a^2 + b^2 + c^2 - 2 * b * c = 37 := by
  (intros; nlinarith [sq_nonneg (a), sq_nonneg (b), sq_nonneg (c), sq_nonneg (a - b), sq_nonneg (a - c), sq_nonneg (b - c), sq_nonneg (a + b), sq_nonneg (a + c), sq_nonneg (b + c)])
