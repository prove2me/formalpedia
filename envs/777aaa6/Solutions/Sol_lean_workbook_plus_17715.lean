-- Prove2me | solution 1 for lean_workbook_plus_17715
-- status  : ACCEPTED   (prove)
-- author  : @evgeth
-- created : 2026-09-05T13:05:54.685632+00:00
-- url     : https://prove2.me/submissions/bccd1149-b625-496e-926e-6beaee4b9271

import Mathlib.Analysis.Complex.Basic

set_option autoImplicit false

theorem solution (a b c : ℝ) (ha : 0 < a) (hb : 0 < b) (hc : 0 < c) : (a - b) / (a + 4 * b + 4 * c) + (b - c) / (4 * a + b + 4 * c) + (c - a) / (4 * a + 4 * b + c) ≥ 0 := by
  (intros; field_simp; nlinarith [sq_nonneg (a), sq_nonneg (b), sq_nonneg (c), sq_nonneg (a - b), sq_nonneg (a - c), sq_nonneg (b - c), sq_nonneg (a + b), sq_nonneg (a + c), sq_nonneg (b + c), mul_pos ha hb, mul_pos ha hc, mul_pos hb hc])
