-- Prove2me | solution 1 for lean_workbook_plus_81488
-- status  : ACCEPTED   (prove)
-- author  : @evgeth
-- created : 2026-09-05T03:37:46.337792+00:00
-- url     : https://prove2.me/submissions/b58afbf8-0977-48b9-bde7-bceecae3db25

import Mathlib.Analysis.Complex.Basic

set_option autoImplicit false

theorem solution (a b c : ℝ) (ha : 0 < a) (hb : 0 < b) (hc : 0 < c) : a / (b + c) + b / (c + a) + c / (a + b) ≥ a / (a + b) + b / (b + c) + c / (c + a) := by
  (intros; field_simp; nlinarith [sq_nonneg (a), sq_nonneg (b), sq_nonneg (c), sq_nonneg (a - b), sq_nonneg (a - c), sq_nonneg (b - c), sq_nonneg (a + b), sq_nonneg (a + c), sq_nonneg (b + c), mul_pos ha hb, mul_pos ha hc, mul_pos hb hc])
