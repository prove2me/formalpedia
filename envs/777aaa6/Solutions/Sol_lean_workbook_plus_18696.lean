-- Prove2me | solution 1 for lean_workbook_plus_18696
-- status  : ACCEPTED   (prove)
-- author  : @evgeth
-- created : 2026-09-05T12:57:14.943785+00:00
-- url     : https://prove2.me/submissions/ea6be830-89d0-4c69-b861-502f262bebb4

import Mathlib.Analysis.Complex.Basic

set_option autoImplicit false

theorem solution (a b c : ℝ) (ha : 0 < a) (hb : 0 < b) (hc : 0 < c) (hab : a * b * c = 1) (h : a^2 + b^2 + c^2 = 1) : 1 / (a^3 + 2 * b * c) + 1 / (b^3 + 2 * c * a) + 1 / (c^3 + 2 * a * b) ≥ 1 := by
  (intros; nlinarith [sq_nonneg (a), sq_nonneg (b), sq_nonneg (c), sq_nonneg (a - b), sq_nonneg (a - c), sq_nonneg (b - c), sq_nonneg (a + b), sq_nonneg (a + c), sq_nonneg (b + c), mul_pos ha hb, mul_pos ha hc, mul_pos hb hc])
