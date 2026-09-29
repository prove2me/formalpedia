-- Prove2me | solution 1 for lean_workbook_plus_58813
-- status  : ACCEPTED   (prove)
-- author  : @evgeth
-- created : 2026-09-05T07:44:29.7948+00:00
-- url     : https://prove2.me/submissions/408e5624-7a55-495a-b3f0-cf8ee8b64768

import Mathlib.Analysis.Complex.Basic

set_option autoImplicit false

theorem solution (a b c : ℝ) : (a^2 + b^2 + c^2 + 5 * b * c + 5 * c * a + 5 * a * b)^2 ≥ 12 * (a + b + c)^2 * (b * c + c * a + a * b) := by
  (intros; nlinarith [sq_nonneg (a), sq_nonneg (b), sq_nonneg (c), sq_nonneg (a - b), sq_nonneg (a - c), sq_nonneg (b - c), sq_nonneg (a + b), sq_nonneg (a + c), sq_nonneg (b + c)])
