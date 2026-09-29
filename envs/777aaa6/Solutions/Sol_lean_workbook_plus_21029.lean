-- Prove2me | solution 1 for lean_workbook_plus_21029
-- status  : ACCEPTED   (prove)
-- author  : @evgeth
-- created : 2026-09-05T12:36:36.827713+00:00
-- url     : https://prove2.me/submissions/7ae41c4f-11c5-4228-a778-0940d861f088

import Mathlib.Analysis.Complex.Basic

set_option autoImplicit false

theorem solution (a b c : ℝ) (ha : 0 < a) (hb : 0 < b) (hc : 0 < c) : a * (a + b) * (a + c) + b * (b + c) * (b + a) + c * (c + a) * (c + b) ≥ (a + b) * (b + c) * (c + a) + 4 * a * b * c := by
  (intros; nlinarith [sq_nonneg (a), sq_nonneg (b), sq_nonneg (c), sq_nonneg (a - b), sq_nonneg (a - c), sq_nonneg (b - c), sq_nonneg (a + b), sq_nonneg (a + c), sq_nonneg (b + c), mul_pos ha hb, mul_pos ha hc, mul_pos hb hc])
