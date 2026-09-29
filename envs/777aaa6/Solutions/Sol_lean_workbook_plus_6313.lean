-- Prove2me | solution 1 for lean_workbook_plus_6313
-- status  : ACCEPTED   (prove)
-- author  : @evgeth
-- created : 2026-09-05T13:50:01.382152+00:00
-- url     : https://prove2.me/submissions/b6d97b08-eca0-4cfa-926f-1097a5a222c4

import Mathlib.Analysis.Complex.Basic

set_option autoImplicit false

theorem solution (a b c : ℝ) (ha : 0 < a) (hb : 0 < b) (hc : 0 < c) : a ^ 2 + b ^ 2 + c ^ 2 ≥ a * b + b * c + a * c := by
  (intros; nlinarith [sq_nonneg (a), sq_nonneg (b), sq_nonneg (c), sq_nonneg (a - b), sq_nonneg (a - c), sq_nonneg (b - c), sq_nonneg (a + b), sq_nonneg (a + c), sq_nonneg (b + c), mul_pos ha hb, mul_pos ha hc, mul_pos hb hc])
