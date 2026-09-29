-- Prove2me | solution 1 for lean_workbook_plus_63657
-- status  : ACCEPTED   (prove)
-- author  : @evgeth
-- created : 2026-09-05T07:08:00.713858+00:00
-- url     : https://prove2.me/submissions/76df0353-578e-4f43-aba7-5fd5ca6e785d

import Mathlib.Analysis.Complex.Basic

set_option autoImplicit false

theorem solution (a b c : ℝ) (ha : 0 < a) (hb : 0 < b) (hc : 0 < c)(habc : a * b * c = 1) : a^2 + b^2 + c^2 + a * b * c = 4 → a + b + c ≤ 3 := by
  (intros; nlinarith [sq_nonneg (a), sq_nonneg (b), sq_nonneg (c), sq_nonneg (a - b), sq_nonneg (a - c), sq_nonneg (b - c), sq_nonneg (a + b), sq_nonneg (a + c), sq_nonneg (b + c), mul_pos ha hb, mul_pos ha hc, mul_pos hb hc])
