-- Prove2me | solution 1 for lean_workbook_plus_69749
-- status  : ACCEPTED   (prove)
-- author  : @evgeth
-- created : 2026-09-05T06:30:23.447687+00:00
-- url     : https://prove2.me/submissions/5b301c1b-f7cf-463b-a0a5-ae0a6ccb2c77

import Mathlib.Analysis.Complex.Basic

set_option autoImplicit false

theorem solution (a b c : ℝ) (ha : 0 < a) (hb : 0 < b) (hc : 0 < c) (habc : a * b * c = 1) (h : a^2 + b^2 + c^2 = 1) :
  a * b / (c * (a^2 + b^2)) + b * c / (a * (b^2 + c^2)) + c * a / (b * (c^2 + a^2)) ≥ 3 * Real.sqrt 3 / 2 := by
  (intros; nlinarith [sq_nonneg (a), sq_nonneg (b), sq_nonneg (c), sq_nonneg (a - b), sq_nonneg (a - c), sq_nonneg (b - c), sq_nonneg (a + b), sq_nonneg (a + c), sq_nonneg (b + c), mul_pos ha hb, mul_pos ha hc, mul_pos hb hc])
