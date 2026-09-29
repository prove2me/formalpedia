-- Prove2me | solution 1 for lean_workbook_plus_35858
-- status  : ACCEPTED   (prove)
-- author  : @evgeth
-- created : 2026-09-05T11:42:57.841821+00:00
-- url     : https://prove2.me/submissions/e33aca42-1541-475a-a71b-4d5f7716f87c

import Mathlib.Analysis.Complex.Basic

set_option autoImplicit false

theorem solution (a b : ℝ) : a^4 + b^4 ≥ (a^2 + b^2)^2 / 2 := by
  (intros; nlinarith [sq_nonneg (a), sq_nonneg (b), sq_nonneg (a - b), sq_nonneg (a + b)])
