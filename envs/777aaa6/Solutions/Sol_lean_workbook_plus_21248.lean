-- Prove2me | solution 1 for lean_workbook_plus_21248
-- status  : ACCEPTED   (prove)
-- author  : @evgeth
-- created : 2026-09-05T12:36:12.555308+00:00
-- url     : https://prove2.me/submissions/7fb0fd12-70a1-4af1-9ac7-7b4f4ef83654

import Mathlib.Analysis.Complex.Basic

set_option autoImplicit false

theorem solution (a b c : ℝ) : a^4 + b^4 + c^4 + a^2 * b^2 + b^2 * c^2 + c^2 * a^2 ≥ a^3 * b + b^3 * c + c^3 * a + a * b^3 + b * c^3 + c * a^3 := by
  (intros; nlinarith [sq_nonneg (a), sq_nonneg (b), sq_nonneg (c), sq_nonneg (a - b), sq_nonneg (a - c), sq_nonneg (b - c), sq_nonneg (a + b), sq_nonneg (a + c), sq_nonneg (b + c)])
