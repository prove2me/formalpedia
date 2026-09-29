-- Prove2me | solution 1 for lean_workbook_plus_78273
-- status  : ACCEPTED   (prove)
-- author  : @evgeth
-- created : 2026-09-05T04:25:22.435606+00:00
-- url     : https://prove2.me/submissions/9b507d51-16d8-4a98-9da6-8ecb5adfd1ed

import Mathlib.Analysis.Complex.Basic

set_option autoImplicit false

theorem solution (a b c : ℝ) :
  (1 + 1 + 1) * (a^2 + b^2 + c^2) ≥ (a + b + c)^2 := by
  (intros; nlinarith [sq_nonneg (a), sq_nonneg (b), sq_nonneg (c), sq_nonneg (a - b), sq_nonneg (a - c), sq_nonneg (b - c), sq_nonneg (a + b), sq_nonneg (a + c), sq_nonneg (b + c)])
