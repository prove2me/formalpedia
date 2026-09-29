-- Prove2me | solution 1 for lean_workbook_plus_68244
-- status  : ACCEPTED   (prove)
-- author  : @evgeth
-- created : 2026-09-05T06:12:55.307371+00:00
-- url     : https://prove2.me/submissions/0a82cac2-9fdc-4c49-84d2-12c0f5b63607

import Mathlib.Analysis.Complex.Basic

set_option autoImplicit false

theorem solution (a b c : ℝ) (ha : a > 0) (hb : b > 0) (hc : c > 0) : a + b + c + 1 / a + 1 / b + 1 / c ≥ a + b + c + 9 / (a + b + c) := by
  (intros; field_simp; nlinarith [sq_nonneg (a), sq_nonneg (b), sq_nonneg (c), sq_nonneg (a - b), sq_nonneg (a - c), sq_nonneg (b - c), sq_nonneg (a + b), sq_nonneg (a + c), sq_nonneg (b + c)])
