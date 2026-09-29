-- Prove2me | solution 1 for lean_workbook_plus_30885
-- status  : ACCEPTED   (prove)
-- author  : @evgeth
-- created : 2026-09-05T11:54:27.658852+00:00
-- url     : https://prove2.me/submissions/26646464-63d6-4cb5-b788-fce138715362

import Mathlib.Analysis.Complex.Basic

set_option autoImplicit false

theorem solution (a b c : ℝ) : a^2 + b^2 + c^2 + 2 * (a * b + b * c + c * a) ≥ 3 * (a * b + b * c + c * a) := by
  (intros; nlinarith [sq_nonneg (a), sq_nonneg (b), sq_nonneg (c), sq_nonneg (a - b), sq_nonneg (a - c), sq_nonneg (b - c), sq_nonneg (a + b), sq_nonneg (a + c), sq_nonneg (b + c)])
