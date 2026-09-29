-- Prove2me | solution 1 for lean_workbook_plus_65473
-- status  : ACCEPTED   (prove)
-- author  : @evgeth
-- created : 2026-09-05T07:06:15.059036+00:00
-- url     : https://prove2.me/submissions/1ba434e0-dbee-4d60-9efb-519259d10018

import Mathlib.Analysis.Complex.Basic

set_option autoImplicit false

theorem solution (a b c : ℝ) (ha : 0 < a) (hb : 0 < b) (hc : 0 < c) : a * b * (a + b) + b * c * (b + c) + c * a * (c + a) ≥ 6 * a * b * c := by
  (intros; nlinarith [sq_nonneg (a), sq_nonneg (b), sq_nonneg (c), sq_nonneg (a - b), sq_nonneg (a - c), sq_nonneg (b - c), sq_nonneg (a + b), sq_nonneg (a + c), sq_nonneg (b + c), mul_pos ha hb, mul_pos ha hc, mul_pos hb hc])
