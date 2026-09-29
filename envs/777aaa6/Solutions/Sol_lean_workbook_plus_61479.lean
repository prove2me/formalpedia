-- Prove2me | solution 1 for lean_workbook_plus_61479
-- status  : ACCEPTED   (prove)
-- author  : @evgeth
-- created : 2026-09-05T07:31:47.971662+00:00
-- url     : https://prove2.me/submissions/ec3443aa-afb2-4639-9c94-24e7c147fafe

import Mathlib.Analysis.Complex.Basic

set_option autoImplicit false

theorem solution (a b : ℝ) : (a+b)^4 ≥ 8*a*b*(a^2+b^2) := by
  (intros; nlinarith [sq_nonneg (a), sq_nonneg (b), sq_nonneg (a - b), sq_nonneg (a + b)])
