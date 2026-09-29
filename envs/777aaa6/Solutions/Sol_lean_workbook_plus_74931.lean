-- Prove2me | solution 1 for lean_workbook_plus_74931
-- status  : ACCEPTED   (prove)
-- author  : @evgeth
-- created : 2026-09-05T04:52:46.264348+00:00
-- url     : https://prove2.me/submissions/c3c7f565-0b06-4e06-a48f-8ea828670195

import Mathlib.Analysis.Complex.Basic

set_option autoImplicit false

theorem solution (a b c : ℝ) (ha : 0 < a) (hb : 0 < b) (hc : 0 < c) : (a^2 + b^2 + c^2)^2 ≥ 3 * (a + b + c) * (b + c - a) * (a + c - b) * (a + b - c) := by
  (intros; nlinarith [sq_nonneg (a), sq_nonneg (b), sq_nonneg (c), sq_nonneg (a - b), sq_nonneg (a - c), sq_nonneg (b - c), sq_nonneg (a + b), sq_nonneg (a + c), sq_nonneg (b + c), mul_pos ha hb, mul_pos ha hc, mul_pos hb hc])
