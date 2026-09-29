-- Prove2me | solution 1 for lean_workbook_plus_28863
-- status  : ACCEPTED   (prove)
-- author  : @evgeth
-- created : 2026-09-05T12:05:03.284636+00:00
-- url     : https://prove2.me/submissions/228e3150-560c-416d-88dd-b9d81a461f8c

import Mathlib.Analysis.Complex.Basic

set_option autoImplicit false

theorem solution (a b c : ℝ) : (a^2+b^2+c^2)*(b^2+c^2+a^2) ≥ (a*b+b*c+c*a)^2 := by
  (intros; nlinarith [sq_nonneg (a), sq_nonneg (b), sq_nonneg (c), sq_nonneg (a - b), sq_nonneg (a - c), sq_nonneg (b - c), sq_nonneg (a + b), sq_nonneg (a + c), sq_nonneg (b + c)])
