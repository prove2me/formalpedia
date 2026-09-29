-- Prove2me | solution 1 for lean_workbook_plus_62153
-- status  : ACCEPTED   (prove)
-- author  : @evgeth
-- created : 2026-09-05T07:19:15.28397+00:00
-- url     : https://prove2.me/submissions/17e0744f-4e2b-45ef-82a4-ddf9bc1aa1c0

import Mathlib.Analysis.Complex.Basic

set_option autoImplicit false

theorem solution (a b c : ℝ) (ha : 0 < a) (hb : 0 < b) (hc : 0 < c) : 2 * (a ^ 3 + b ^ 3 + c ^ 3 + a * b * c) ≥ (a + b) * (b + c) * (c + a) := by
  (intros; nlinarith [sq_nonneg (a), sq_nonneg (b), sq_nonneg (c), sq_nonneg (a - b), sq_nonneg (a - c), sq_nonneg (b - c), sq_nonneg (a + b), sq_nonneg (a + c), sq_nonneg (b + c), mul_pos ha hb, mul_pos ha hc, mul_pos hb hc])
