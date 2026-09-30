-- Prove2me | solution 2 for lean_workbook_plus_2845
-- status  : ACCEPTED   (prove)
-- author  : @evgeth
-- created : 2026-09-05T14:25:15.977104+00:00
-- url     : https://prove2.me/submissions/17602001-1238-42ac-b623-6936d0c538a8

import Mathlib.Analysis.Complex.Basic

set_option autoImplicit false

theorem solution (a b c : ℝ) (ha : a > 0) (hb : b > 0) (hc : c > 0) : (a + b + c) ^ 2 ≥ 3 * (a * b + b * c + a * c) := by
  (intros; nlinarith [sq_nonneg (a), sq_nonneg (b), sq_nonneg (c), sq_nonneg (a - b), sq_nonneg (a - c), sq_nonneg (b - c), sq_nonneg (a + b), sq_nonneg (a + c), sq_nonneg (b + c)])
