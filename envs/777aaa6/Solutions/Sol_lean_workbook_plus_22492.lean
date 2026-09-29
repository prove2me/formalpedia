-- Prove2me | solution 1 for lean_workbook_plus_22492
-- status  : ACCEPTED   (prove)
-- author  : @evgeth
-- created : 2026-09-05T12:44:27.917168+00:00
-- url     : https://prove2.me/submissions/85ea4554-af34-4d49-8a5b-aa7d8ae9fd5d

import Mathlib.Analysis.Complex.Basic

set_option autoImplicit false

theorem solution (a b c : ℝ) (ha : 0 < a) (hb : 0 < b) (hc : 0 < c) : (a + 3 * b) / (c + a) + (b + 3 * a) / (c + b) + 4 * c / (a + b) ≥ 6 := by
  (intros; field_simp; nlinarith [sq_nonneg (a), sq_nonneg (b), sq_nonneg (c), sq_nonneg (a - b), sq_nonneg (a - c), sq_nonneg (b - c), sq_nonneg (a + b), sq_nonneg (a + c), sq_nonneg (b + c), mul_pos ha hb, mul_pos ha hc, mul_pos hb hc])
