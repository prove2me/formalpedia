-- Prove2me | solution 1 for lean_workbook_plus_24316
-- status  : ACCEPTED   (prove)
-- author  : @evgeth
-- created : 2026-09-05T12:15:31.829631+00:00
-- url     : https://prove2.me/submissions/e29fc67c-afa8-4ab5-b2c5-6b3152590eb7

import Mathlib.Analysis.Complex.Basic

set_option autoImplicit false

theorem solution (a b c : ℝ) (ha : a > 0) (hb : b > 0) (hc : c > 0) : (1 + 2 * a / (b + c)) * (1 + 2 * b / (c + a)) * (1 + 2 * c / (a + b)) ≥ 2 := by
  (intros; field_simp; nlinarith [sq_nonneg (a), sq_nonneg (b), sq_nonneg (c), sq_nonneg (a - b), sq_nonneg (a - c), sq_nonneg (b - c), sq_nonneg (a + b), sq_nonneg (a + c), sq_nonneg (b + c)])
