-- Prove2me | solution 1 for lean_workbook_plus_43133
-- status  : ACCEPTED   (prove)
-- author  : @evgeth
-- created : 2026-09-05T10:16:13.069161+00:00
-- url     : https://prove2.me/submissions/7d65f2c3-7314-4530-94ca-82c6ac4b472b

import Mathlib.Analysis.Complex.Basic

set_option autoImplicit false

theorem solution (a b c : ℝ) : (a^2 - a * b + b^2) * (b^2 - b * c + c^2) + (b^2 - b * c + c^2) * (c^2 - c * a + a^2) + (c^2 - c * a + a^2) * (a^2 - a * b + b^2) ≥ 1/3 * (a^2 + b^2 + c^2)^2 := by
  (intros; nlinarith [sq_nonneg (a), sq_nonneg (b), sq_nonneg (c), sq_nonneg (a - b), sq_nonneg (a - c), sq_nonneg (b - c), sq_nonneg (a + b), sq_nonneg (a + c), sq_nonneg (b + c)])
