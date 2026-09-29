-- Prove2me | solution 1 for lean_workbook_plus_34744
-- status  : ACCEPTED   (prove)
-- author  : @evgeth
-- created : 2026-09-05T11:17:06.668162+00:00
-- url     : https://prove2.me/submissions/9e27b578-8ed8-4e69-9535-900731c62896

import Mathlib.Analysis.Complex.Basic

set_option autoImplicit false

theorem solution (a b c : ℝ) : (4 / 3) * (a ^ 4 + b ^ 4 + c ^ 4 - a ^ 2 * b ^ 2 - b ^ 2 * c ^ 2 - c ^ 2 * a ^ 2) + (4 / 3) * (a * b + b * c + c * a - 3) ^ 2 ≥ 0 := by
  (intros; nlinarith [sq_nonneg (a), sq_nonneg (b), sq_nonneg (c), sq_nonneg (a - b), sq_nonneg (a - c), sq_nonneg (b - c), sq_nonneg (a + b), sq_nonneg (a + c), sq_nonneg (b + c)])
