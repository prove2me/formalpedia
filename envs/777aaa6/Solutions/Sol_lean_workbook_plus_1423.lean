-- Prove2me | solution 1 for lean_workbook_plus_1423
-- status  : ACCEPTED   (prove)
-- author  : @evgeth
-- created : 2026-09-05T14:24:00.472284+00:00
-- url     : https://prove2.me/submissions/2cd3bb4d-7d3e-41a1-b26f-6bc78239faab

import Mathlib.Analysis.Complex.Basic

set_option autoImplicit false

theorem solution (a b c : ℝ) (ha : 0 < a) (hb : 0 < b) (hc : 0 < c) (ha2 : a^2 + b^2 + c^2 = a^3 + b^3 + c^3) : a + b + c ≤ 3 := by
  (intros; nlinarith [sq_nonneg (a), sq_nonneg (b), sq_nonneg (c), sq_nonneg (a - b), sq_nonneg (a - c), sq_nonneg (b - c), sq_nonneg (a + b), sq_nonneg (a + c), sq_nonneg (b + c), mul_pos ha hb, mul_pos ha hc, mul_pos hb hc])
