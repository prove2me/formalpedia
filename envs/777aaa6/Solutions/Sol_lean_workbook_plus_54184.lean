-- Prove2me | solution 1 for lean_workbook_plus_54184
-- status  : ACCEPTED   (prove)
-- author  : @evgeth
-- created : 2026-09-05T08:45:07.388946+00:00
-- url     : https://prove2.me/submissions/5c17e28d-9516-4330-8149-c5a1c62338d4

import Mathlib.Analysis.Complex.Basic

set_option autoImplicit false

theorem solution (a b c : ℝ) (ha : 0 < a) (hb : 0 < b) (hc : 0 < c) (habc : a * b * c = 1) (h : a^2 + b^2 + c^2 + 2 * a * b * c = 1) : a * b + b * c + c * a ≤ (a + b + c) / 2 := by
  (intros; nlinarith [sq_nonneg (a), sq_nonneg (b), sq_nonneg (c), sq_nonneg (a - b), sq_nonneg (a - c), sq_nonneg (b - c), sq_nonneg (a + b), sq_nonneg (a + c), sq_nonneg (b + c), mul_pos ha hb, mul_pos ha hc, mul_pos hb hc])
