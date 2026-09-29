-- Prove2me | solution 1 for lean_workbook_plus_21536
-- status  : ACCEPTED   (prove)
-- author  : @evgeth
-- created : 2026-09-05T12:45:54.416089+00:00
-- url     : https://prove2.me/submissions/5dc0c0f7-5625-4dc0-b557-e51896f49759

import Mathlib.Analysis.Complex.Basic

set_option autoImplicit false

theorem solution (a b c : ℝ) : 2 * (a ^ 4 + b ^ 4 + c ^ 4) + 5 * (a ^ 2 * b ^ 2 + b ^ 2 * c ^ 2 + c ^ 2 * a ^ 2) - (a * b * (3 * a ^ 2 + 4 * b ^ 2) + b * c * (3 * b ^ 2 + 4 * c ^ 2) + c * a * (3 * c ^ 2 + 4 * a ^ 2)) ≥ 0 := by
  (intros; nlinarith [sq_nonneg (a), sq_nonneg (b), sq_nonneg (c), sq_nonneg (a - b), sq_nonneg (a - c), sq_nonneg (b - c), sq_nonneg (a + b), sq_nonneg (a + c), sq_nonneg (b + c)])
