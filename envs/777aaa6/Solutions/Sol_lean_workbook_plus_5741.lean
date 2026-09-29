-- Prove2me | solution 1 for lean_workbook_plus_5741
-- status  : ACCEPTED   (prove)
-- author  : @evgeth
-- created : 2026-09-05T14:07:06.331011+00:00
-- url     : https://prove2.me/submissions/f4c1957b-9a8d-4974-a5a9-35fa781bbc6f

import Mathlib.Analysis.Complex.Basic

set_option autoImplicit false

theorem solution (a b c : ℝ) : 3 * (a * b + a * c + b * c) ≤ (a + b + c) ^ 2 := by
  (intros; nlinarith [sq_nonneg (a), sq_nonneg (b), sq_nonneg (c), sq_nonneg (a - b), sq_nonneg (a - c), sq_nonneg (b - c), sq_nonneg (a + b), sq_nonneg (a + c), sq_nonneg (b + c)])
