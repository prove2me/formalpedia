-- Prove2me | solution 1 for lean_workbook_plus_19413
-- status  : ACCEPTED   (prove)
-- author  : @evgeth
-- created : 2026-09-05T13:04:12.908717+00:00
-- url     : https://prove2.me/submissions/b6b45e5a-4971-479a-a2c6-b84e3fc90e77

import Mathlib.Analysis.Complex.Basic

set_option autoImplicit false

theorem solution (a b c : ℝ) (ha : 0 < a) (hb : 0 < b) (hc : 0 < c) : (a + b + c) * (1 / a + 1 / b + 1 / c) ≥ 3 * (a + b + c) ^ 2 / (a * b + b * c + a * c) := by
  (intros; field_simp; nlinarith [sq_nonneg (a), sq_nonneg (b), sq_nonneg (c), sq_nonneg (a - b), sq_nonneg (a - c), sq_nonneg (b - c), sq_nonneg (a + b), sq_nonneg (a + c), sq_nonneg (b + c), mul_pos ha hb, mul_pos ha hc, mul_pos hb hc])
