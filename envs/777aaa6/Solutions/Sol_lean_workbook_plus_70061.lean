-- Prove2me | solution 1 for lean_workbook_plus_70061
-- status  : ACCEPTED   (prove)
-- author  : @evgeth
-- created : 2026-09-05T05:52:58.203513+00:00
-- url     : https://prove2.me/submissions/6cdee465-c9aa-4030-b5fa-6ab758a34961

import Mathlib.Analysis.Complex.Basic

set_option autoImplicit false

theorem solution (a b c : ℝ) (ha : 0 < a) (hb : 0 < b) (hc : 0 < c) (habc : a * b * c = 1) (h : a^2 + b^2 + c^2 = 1) :
  (a + b) / (1 + a * b) + (b + c) / (1 + b * c) + (c + a) / (1 + c * a) ≤ (3 * Real.sqrt 3) / 2 := by
  (intros; nlinarith [sq_nonneg (a), sq_nonneg (b), sq_nonneg (c), sq_nonneg (a - b), sq_nonneg (a - c), sq_nonneg (b - c), sq_nonneg (a + b), sq_nonneg (a + c), sq_nonneg (b + c), mul_pos ha hb, mul_pos ha hc, mul_pos hb hc])
