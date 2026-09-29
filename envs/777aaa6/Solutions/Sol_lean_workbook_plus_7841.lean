-- Prove2me | solution 1 for lean_workbook_plus_7841
-- status  : ACCEPTED   (prove)
-- author  : @evgeth
-- created : 2026-09-05T13:56:58.019102+00:00
-- url     : https://prove2.me/submissions/40fe2958-017e-4d20-b20d-b79fa1ed2f2f

import Mathlib.Analysis.Complex.Basic

set_option autoImplicit false

theorem solution (a b : ℝ) : -(a^2 + a * b + b^2)^2 ≤ 0 := by
  (intros; nlinarith [sq_nonneg (a), sq_nonneg (b), sq_nonneg (a - b), sq_nonneg (a + b)])
