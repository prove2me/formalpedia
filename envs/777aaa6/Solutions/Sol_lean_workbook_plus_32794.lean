-- Prove2me | solution 1 for lean_workbook_plus_32794
-- status  : ACCEPTED   (prove)
-- author  : @evgeth
-- created : 2026-09-05T11:05:53.074977+00:00
-- url     : https://prove2.me/submissions/1efa1e5d-ccab-4151-bb81-ebf421d71896

import Mathlib.Analysis.Complex.Basic

set_option autoImplicit false

theorem solution (a b c : ℝ) (ha : 0 < a) (hb : 0 < b) (hc : 0 < c) (habc : a * b * c = 1) (hab : a + b + c = 1) : a / (b * b + 1) + b / (c * c + 1) + c / (a * a + 1) ≥ (3 / 4) * (a * Real.sqrt a + b * Real.sqrt b + c * Real.sqrt c) ^ 2 := by
  (intros; nlinarith [sq_nonneg (a), sq_nonneg (b), sq_nonneg (c), sq_nonneg (a - b), sq_nonneg (a - c), sq_nonneg (b - c), sq_nonneg (a + b), sq_nonneg (a + c), sq_nonneg (b + c), mul_pos ha hb, mul_pos ha hc, mul_pos hb hc])
