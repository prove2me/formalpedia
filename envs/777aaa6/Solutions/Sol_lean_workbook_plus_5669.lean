-- Prove2me | solution 1 for lean_workbook_plus_5669
-- status  : ACCEPTED   (prove)
-- author  : @evgeth
-- created : 2026-09-05T14:07:17.32989+00:00
-- url     : https://prove2.me/submissions/a731d8e5-82e8-46f8-aa9a-747b38533f90

import Mathlib.Analysis.Complex.Basic

set_option autoImplicit false

theorem solution (a b c : ℝ) (ha : 0 < a) (hb : 0 < b) (hc : 0 < c) (habc : a * b * c = 1) (h : a + b + c = 1 / a + 1 / b + 1 / c) : a * b + b * c + c * a + 1 ≥ 4 * a * b * c := by
  (intros; nlinarith [sq_nonneg (a), sq_nonneg (b), sq_nonneg (c), sq_nonneg (a - b), sq_nonneg (a - c), sq_nonneg (b - c), sq_nonneg (a + b), sq_nonneg (a + c), sq_nonneg (b + c), mul_pos ha hb, mul_pos ha hc, mul_pos hb hc])
