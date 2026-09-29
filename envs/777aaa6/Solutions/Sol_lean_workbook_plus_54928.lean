-- Prove2me | solution 1 for lean_workbook_plus_54928
-- status  : ACCEPTED   (prove)
-- author  : @evgeth
-- created : 2026-09-05T08:02:07.887281+00:00
-- url     : https://prove2.me/submissions/4416a516-a8db-41ea-bb60-9a5415672109

import Mathlib.Analysis.Complex.Basic

set_option autoImplicit false

theorem solution (a b c : ℝ) (ha : 0 < a) (hb : 0 < b) (hc : 0 < c) (habc : a + b + c = 1) (h : 1 = (a + b) * (b + c) * (c + a)) : a * b + b * c + c * a ≥ 3 / 4 := by
  (intros; nlinarith [sq_nonneg (a), sq_nonneg (b), sq_nonneg (c), sq_nonneg (a - b), sq_nonneg (a - c), sq_nonneg (b - c), sq_nonneg (a + b), sq_nonneg (a + c), sq_nonneg (b + c), mul_pos ha hb, mul_pos ha hc, mul_pos hb hc])
