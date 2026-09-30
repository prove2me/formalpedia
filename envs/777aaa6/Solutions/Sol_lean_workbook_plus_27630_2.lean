-- Prove2me | solution 2 for lean_workbook_plus_27630
-- status  : ACCEPTED   (prove)
-- author  : @evgeth
-- created : 2026-09-05T12:14:18.092976+00:00
-- url     : https://prove2.me/submissions/2da40516-e92c-4a43-bda4-2ceadd273231

import Mathlib.Analysis.Complex.Basic

set_option autoImplicit false

theorem solution (a b c : ℝ) (ha : 0 < a) (hb : 0 < b) (hc : 0 < c) : (a + b + 1 / 2) * (b + c + 1 / 2) * (c + a + 1 / 2) ≥ (2 * a + 1 / 2) * (2 * b + 1 / 2) * (2 * c + 1 / 2) := by
  (intros; nlinarith [sq_nonneg (a), sq_nonneg (b), sq_nonneg (c), sq_nonneg (a - b), sq_nonneg (a - c), sq_nonneg (b - c), sq_nonneg (a + b), sq_nonneg (a + c), sq_nonneg (b + c), mul_pos ha hb, mul_pos ha hc, mul_pos hb hc])
