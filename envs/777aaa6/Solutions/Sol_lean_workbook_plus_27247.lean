-- Prove2me | solution 1 for lean_workbook_plus_27247
-- status  : ACCEPTED   (prove)
-- author  : @evgeth
-- created : 2026-09-05T12:14:53.631358+00:00
-- url     : https://prove2.me/submissions/f259a619-c1cd-4426-83d8-e09d292d3b64

import Mathlib.Analysis.Complex.Basic

set_option autoImplicit false

theorem solution (a b c : ℝ) (hab : a + b + c = 0) : a ^ 3 + b ^ 3 + c ^ 3 = 3 * a * b * c := by
  (intros; nlinarith [sq_nonneg (a), sq_nonneg (b), sq_nonneg (c), sq_nonneg (a - b), sq_nonneg (a - c), sq_nonneg (b - c), sq_nonneg (a + b), sq_nonneg (a + c), sq_nonneg (b + c)])
