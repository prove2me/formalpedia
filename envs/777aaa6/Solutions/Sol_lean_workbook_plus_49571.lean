-- Prove2me | solution 1 for lean_workbook_plus_49571
-- status  : ACCEPTED   (prove)
-- author  : @evgeth
-- created : 2026-09-05T09:35:59.727502+00:00
-- url     : https://prove2.me/submissions/113efc92-10fe-4730-afb6-846e6f02d416

import Mathlib.Analysis.Complex.Basic

set_option autoImplicit false

theorem solution (a b c : ℝ) (ha : 0 < a) (hb : 0 < b) (hc : 0 < c) (hab : a^2 < b * c) : b^3 + a * c^2 > a * b * (a + c) := by
  (intros; nlinarith [sq_nonneg (a), sq_nonneg (b), sq_nonneg (c), sq_nonneg (a - b), sq_nonneg (a - c), sq_nonneg (b - c), sq_nonneg (a + b), sq_nonneg (a + c), sq_nonneg (b + c), mul_pos ha hb, mul_pos ha hc, mul_pos hb hc])
