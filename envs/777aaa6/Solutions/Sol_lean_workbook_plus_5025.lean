-- Prove2me | solution 1 for lean_workbook_plus_5025
-- status  : ACCEPTED   (prove)
-- author  : @evgeth
-- created : 2026-09-05T14:07:38.055223+00:00
-- url     : https://prove2.me/submissions/a1eae8e4-7d96-4774-b243-1fa464ae236f

import Mathlib.Analysis.Complex.Basic

set_option autoImplicit false

theorem solution (a b c : ℝ) (ha : a > 0) (hb : b > 0) (hc : c > 0) : a / (b + c) + b / (c + a) + c / (a + b) ≥ 3 / 2 := by
  (intros; field_simp; nlinarith [sq_nonneg (a), sq_nonneg (b), sq_nonneg (c), sq_nonneg (a - b), sq_nonneg (a - c), sq_nonneg (b - c), sq_nonneg (a + b), sq_nonneg (a + c), sq_nonneg (b + c)])
