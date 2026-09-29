-- Prove2me | solution 1 for lean_workbook_plus_11995
-- status  : ACCEPTED   (prove)
-- author  : @evgeth
-- created : 2026-09-05T13:49:00.748885+00:00
-- url     : https://prove2.me/submissions/f12b3077-76c0-4430-9efa-5b94a50d9590

import Mathlib.Analysis.Complex.Basic

set_option autoImplicit false

theorem solution (a b c : ℝ) (ha : 0 < a) (hb : 0 < b) (hc : 0 < c) (habc : a + b + c = 1) (h : (a + b) * (b + c) = 4) :
  (2 * a + b) * (a + b) + (b + 2 * c) * (b + c) ≥ 8 + 1 / 2 * (a + 2 * b + c) * (c + a) := by
  (intros; nlinarith [sq_nonneg (a), sq_nonneg (b), sq_nonneg (c), sq_nonneg (a - b), sq_nonneg (a - c), sq_nonneg (b - c), sq_nonneg (a + b), sq_nonneg (a + c), sq_nonneg (b + c), mul_pos ha hb, mul_pos ha hc, mul_pos hb hc])
