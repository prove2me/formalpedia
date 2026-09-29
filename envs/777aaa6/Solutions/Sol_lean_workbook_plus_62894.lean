-- Prove2me | solution 1 for lean_workbook_plus_62894
-- status  : ACCEPTED   (prove)
-- author  : @evgeth
-- created : 2026-09-05T07:18:10.049654+00:00
-- url     : https://prove2.me/submissions/a9fbd80b-93f5-4184-b5ce-49fc596aa7fa

import Mathlib.Analysis.Complex.Basic

set_option autoImplicit false

theorem solution (a b c : ℝ) : (a^2 + b^2 + 6*c^2)*(1 + 1 + 6) ≥ (a + b + 6*c)^2 := by
  (intros; nlinarith [sq_nonneg (a), sq_nonneg (b), sq_nonneg (c), sq_nonneg (a - b), sq_nonneg (a - c), sq_nonneg (b - c), sq_nonneg (a + b), sq_nonneg (a + c), sq_nonneg (b + c)])
