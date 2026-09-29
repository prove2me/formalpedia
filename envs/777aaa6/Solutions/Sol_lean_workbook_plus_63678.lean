-- Prove2me | solution 1 for lean_workbook_plus_63678
-- status  : ACCEPTED   (prove)
-- author  : @evgeth
-- created : 2026-09-05T07:07:55.058131+00:00
-- url     : https://prove2.me/submissions/52f32eea-f032-412f-ad8b-55d36ada6b8b

import Mathlib.Analysis.Complex.Basic

set_option autoImplicit false

theorem solution (a b c : ℝ) : 3 * (a ^ 4 + b ^ 4 + c ^ 4) ≥ (a ^ 2 + b ^ 2 + c ^ 2) ^ 2 := by
  (intros; nlinarith [sq_nonneg (a), sq_nonneg (b), sq_nonneg (c), sq_nonneg (a - b), sq_nonneg (a - c), sq_nonneg (b - c), sq_nonneg (a + b), sq_nonneg (a + c), sq_nonneg (b + c)])
