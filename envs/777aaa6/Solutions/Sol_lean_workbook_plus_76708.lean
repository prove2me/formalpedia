-- Prove2me | solution 1 for lean_workbook_plus_76708
-- status  : ACCEPTED   (prove)
-- author  : @evgeth
-- created : 2026-09-05T04:27:18.229911+00:00
-- url     : https://prove2.me/submissions/0fac9772-78e7-4864-bd8c-2826d1e9f0e9

import Mathlib.Analysis.Complex.Basic

set_option autoImplicit false

theorem solution (a b : ℝ) : 1/2 * a * b ≤ (a^2 + b^2)/4 := by
  (intros; nlinarith [sq_nonneg (a), sq_nonneg (b), sq_nonneg (a - b), sq_nonneg (a + b)])
