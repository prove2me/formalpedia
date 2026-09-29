-- Prove2me | solution 1 for lean_workbook_plus_25368
-- status  : ACCEPTED   (prove)
-- author  : @evgeth
-- created : 2026-09-05T12:26:41.664782+00:00
-- url     : https://prove2.me/submissions/d6ab0633-aff4-47ba-b9c4-6a9b1784d872

import Mathlib.Analysis.Complex.Basic

set_option autoImplicit false

theorem solution (a b c : ℝ) : 3 * a ^ 2 + 3 * b ^ 2 + 3 * c ^ 2 ≥ a ^ 2 + b ^ 2 + c ^ 2 + 2 * a * b + 2 * b * c + 2 * c * a := by
  (intros; nlinarith [sq_nonneg (a), sq_nonneg (b), sq_nonneg (c), sq_nonneg (a - b), sq_nonneg (a - c), sq_nonneg (b - c), sq_nonneg (a + b), sq_nonneg (a + c), sq_nonneg (b + c)])
