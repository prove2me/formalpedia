-- Prove2me | solution 1 for lean_workbook_plus_33318
-- status  : ACCEPTED   (prove)
-- author  : @evgeth
-- created : 2026-09-05T11:06:33.015789+00:00
-- url     : https://prove2.me/submissions/2d728d05-f433-4560-9958-cbc6e10a193c

import Mathlib.Analysis.Complex.Basic

set_option autoImplicit false

theorem solution (a b c : ℝ) : (a^2 + b^2 + c^2)^2 ≥ a^3 * b + b^3 * c + c^3 * a := by
  (intros; nlinarith [sq_nonneg (a), sq_nonneg (b), sq_nonneg (c), sq_nonneg (a - b), sq_nonneg (a - c), sq_nonneg (b - c), sq_nonneg (a + b), sq_nonneg (a + c), sq_nonneg (b + c)])
