-- Prove2me | solution 1 for lean_workbook_plus_32895
-- status  : ACCEPTED   (prove)
-- author  : @evgeth
-- created : 2026-09-05T11:06:00.95054+00:00
-- url     : https://prove2.me/submissions/c23cdbd1-cc06-4f2e-af67-5428b0a969aa

import Mathlib.Analysis.Complex.Basic

set_option autoImplicit false

theorem solution (a b : ℝ) :
  (1 + 1) * (a^2 + b^2) ≥ (a + b)^2 := by
  (intros; nlinarith [sq_nonneg (a), sq_nonneg (b), sq_nonneg (a - b), sq_nonneg (a + b)])
