-- Prove2me | solution 2 for lean_workbook_plus_71830
-- status  : ACCEPTED   (prove)
-- author  : @evgeth
-- created : 2026-09-05T05:19:43.351648+00:00
-- url     : https://prove2.me/submissions/ce1943d4-03f1-498c-bf12-426a7a750ca0

import Mathlib.Analysis.Complex.Basic

set_option autoImplicit false

theorem solution (a b c : ℝ) (ha : 0 < a) (hb : 0 < b) (hc : 0 < c) : a * b ^ 3 + a * c ^ 3 + b * c ^ 3 + b * a ^ 3 + c * a ^ 3 + c * b ^ 3 ≤ 2 * (a ^ 4 + b ^ 4 + c ^ 4) := by
  (intros; nlinarith [sq_nonneg (a), sq_nonneg (b), sq_nonneg (c), sq_nonneg (a - b), sq_nonneg (a - c), sq_nonneg (b - c), sq_nonneg (a + b), sq_nonneg (a + c), sq_nonneg (b + c), mul_pos ha hb, mul_pos ha hc, mul_pos hb hc])
