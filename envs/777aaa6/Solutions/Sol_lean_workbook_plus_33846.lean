-- Prove2me | solution 1 for lean_workbook_plus_33846
-- status  : ACCEPTED   (prove)
-- author  : @evgeth
-- created : 2026-09-05T11:15:40.501178+00:00
-- url     : https://prove2.me/submissions/bed83f73-80df-4b2c-8129-333e836e56f0

import Mathlib.Analysis.Complex.Basic

set_option autoImplicit false

theorem solution (a b c : ℝ) (ha : a > 0) (hb : b > 0) (hc : c > 0) : (a + b) / (3 * a + 2 * b + c) + (b + c) / (3 * b + 2 * c + a) + (c + a) / (3 * c + 2 * a + b) ≤ 1 := by
  (intros; field_simp; nlinarith [sq_nonneg (a), sq_nonneg (b), sq_nonneg (c), sq_nonneg (a - b), sq_nonneg (a - c), sq_nonneg (b - c), sq_nonneg (a + b), sq_nonneg (a + c), sq_nonneg (b + c)])
