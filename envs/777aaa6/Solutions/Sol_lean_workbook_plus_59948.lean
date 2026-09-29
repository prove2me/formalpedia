-- Prove2me | solution 1 for lean_workbook_plus_59948
-- status  : ACCEPTED   (prove)
-- author  : @evgeth
-- created : 2026-09-05T07:33:25.475376+00:00
-- url     : https://prove2.me/submissions/0282b953-c04b-44a5-80f2-652ec2308710

import Mathlib.Analysis.Complex.Basic

set_option autoImplicit false

theorem solution (a b c : ℝ) (ha : 0 < a) (hb : 0 < b) (hc : 0 < c) : (a * b / (a + 3 * b + 2 * c) + b * c / (b + 3 * c + 2 * a) + c * a / (c + 3 * a + 2 * b)) ≤ (a + b + c) / 6 := by
  (intros; field_simp; nlinarith [sq_nonneg (a), sq_nonneg (b), sq_nonneg (c), sq_nonneg (a - b), sq_nonneg (a - c), sq_nonneg (b - c), sq_nonneg (a + b), sq_nonneg (a + c), sq_nonneg (b + c), mul_pos ha hb, mul_pos ha hc, mul_pos hb hc])
