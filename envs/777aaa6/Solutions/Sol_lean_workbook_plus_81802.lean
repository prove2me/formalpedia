-- Prove2me | solution 1 for lean_workbook_plus_81802
-- status  : ACCEPTED   (prove)
-- author  : @evgeth
-- created : 2026-09-05T04:01:12.432799+00:00
-- url     : https://prove2.me/submissions/37b496d5-18ac-4f42-8f6d-df2a73532cb8

import Mathlib.Analysis.Complex.Basic

set_option autoImplicit false

theorem solution (a b c : ℝ) (ha : a > 0) (hb : b > 0) (hc : c > 0) : (3 * a + c) / (a + b) + (3 * b + a) / (b + c) + (3 * c + b) / (c + a) ≥ 6 := by
  (intros; field_simp; nlinarith [sq_nonneg (a), sq_nonneg (b), sq_nonneg (c), sq_nonneg (a - b), sq_nonneg (a - c), sq_nonneg (b - c), sq_nonneg (a + b), sq_nonneg (a + c), sq_nonneg (b + c)])
