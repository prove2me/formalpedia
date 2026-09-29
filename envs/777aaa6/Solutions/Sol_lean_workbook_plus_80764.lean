-- Prove2me | solution 1 for lean_workbook_plus_80764
-- status  : ACCEPTED   (prove)
-- author  : @evgeth
-- created : 2026-09-05T04:01:35.233526+00:00
-- url     : https://prove2.me/submissions/bad361e6-876a-40fc-bfae-cff45ac2fcb1

import Mathlib.Analysis.Complex.Basic

set_option autoImplicit false

theorem solution (a b c : ℝ) (ha : 0 < a) (hb : 0 < b) (hc : 0 < c) (hab : 2 * b^2 = a^2 + c^2) : 1 / (a + b) + 1 / (b + c) = 2 / (a + c) := by
  (intros; field_simp; nlinarith [sq_nonneg (a), sq_nonneg (b), sq_nonneg (c), sq_nonneg (a - b), sq_nonneg (a - c), sq_nonneg (b - c), sq_nonneg (a + b), sq_nonneg (a + c), sq_nonneg (b + c), mul_pos ha hb, mul_pos ha hc, mul_pos hb hc])
