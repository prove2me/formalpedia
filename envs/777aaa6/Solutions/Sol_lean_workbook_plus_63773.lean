-- Prove2me | solution 1 for lean_workbook_plus_63773
-- status  : ACCEPTED   (prove)
-- author  : @evgeth
-- created : 2026-09-05T06:49:58.801501+00:00
-- url     : https://prove2.me/submissions/b6482378-5212-46fa-bde6-ae45c359c16d

import Mathlib.Analysis.Complex.Basic

set_option autoImplicit false

theorem solution (a b c : ℝ) (ha : 0 < a) (hb : 0 < b) (hc : 0 < c) : a^2 * (b + c) + b^2 * (a + c) + c^2 * (a + b) ≥ 6 * a * b * c := by
  (intros; nlinarith [sq_nonneg (a), sq_nonneg (b), sq_nonneg (c), sq_nonneg (a - b), sq_nonneg (a - c), sq_nonneg (b - c), sq_nonneg (a + b), sq_nonneg (a + c), sq_nonneg (b + c), mul_pos ha hb, mul_pos ha hc, mul_pos hb hc])
