-- Prove2me | solution 1 for lean_workbook_plus_1539
-- status  : ACCEPTED   (prove)
-- author  : @evgeth
-- created : 2026-09-05T14:32:58.583434+00:00
-- url     : https://prove2.me/submissions/b4fbf50f-e014-4734-b266-f2f5f131e634

import Mathlib.Analysis.Complex.Basic

set_option autoImplicit false

theorem solution (a b c : ℝ) (ha : a > 0) (hb : b > 0) (hc : c > 0) : (5 * (a ^ 2 + b ^ 2 + c ^ 2) + 2 * (a * b + b * c + a * c)) / (2 * (a ^ 2 + b ^ 2 + c ^ 2) + (a + b + c) ^ 2) ≤ 9 / 2 := by
  (intros; field_simp; nlinarith [sq_nonneg (a), sq_nonneg (b), sq_nonneg (c), sq_nonneg (a - b), sq_nonneg (a - c), sq_nonneg (b - c), sq_nonneg (a + b), sq_nonneg (a + c), sq_nonneg (b + c)])
