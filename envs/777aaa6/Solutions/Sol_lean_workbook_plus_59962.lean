-- Prove2me | solution 1 for lean_workbook_plus_59962
-- status  : ACCEPTED   (prove)
-- author  : @evgeth
-- created : 2026-09-05T07:33:19.691036+00:00
-- url     : https://prove2.me/submissions/7bc2323e-43d7-43a2-963d-95b6580bfcd9

import Mathlib.Analysis.Complex.Basic

set_option autoImplicit false

theorem solution (a b c : ℝ) (ha : 0 < a) (hb : 0 < b) (hc : 0 < c) (habc : a * b * c = 1) (h : a^2 + b^2 + c^2 = 1 / 3) : 1 / (a^2 - b * c + 1) + 1 / (b^2 - c * a + 1) + 1 / (c^2 - a * b + 1) ≤ 3 := by
  (intros; nlinarith [sq_nonneg (a), sq_nonneg (b), sq_nonneg (c), sq_nonneg (a - b), sq_nonneg (a - c), sq_nonneg (b - c), sq_nonneg (a + b), sq_nonneg (a + c), sq_nonneg (b + c), mul_pos ha hb, mul_pos ha hc, mul_pos hb hc])
