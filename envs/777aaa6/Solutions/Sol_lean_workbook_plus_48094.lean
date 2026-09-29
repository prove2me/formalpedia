-- Prove2me | solution 1 for lean_workbook_plus_48094
-- status  : ACCEPTED   (prove)
-- author  : @evgeth
-- created : 2026-09-05T09:50:20.443517+00:00
-- url     : https://prove2.me/submissions/f73ff012-6dc8-47ff-9ad2-12f09bac5c8d

import Mathlib.Analysis.Complex.Basic

set_option autoImplicit false

theorem solution (a b c : ℝ) : 3 * (a ^ 4 + b ^ 4 + c ^ 4) + 9 * (a ^ 2 * b ^ 2 + b ^ 2 * c ^ 2 + c ^ 2 * a ^ 2) ≥ 5 * (a ^ 3 * (b + c) + b ^ 3 * (c + a) + c ^ 3 * (a + b)) + 2 * a * b * c * (a + b + c) := by
  (intros; nlinarith [sq_nonneg (a), sq_nonneg (b), sq_nonneg (c), sq_nonneg (a - b), sq_nonneg (a - c), sq_nonneg (b - c), sq_nonneg (a + b), sq_nonneg (a + c), sq_nonneg (b + c)])
