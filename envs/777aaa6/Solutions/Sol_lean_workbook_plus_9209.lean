-- Prove2me | solution 1 for lean_workbook_plus_9209
-- status  : ACCEPTED   (prove)
-- author  : @evgeth
-- created : 2026-09-05T13:39:04.940107+00:00
-- url     : https://prove2.me/submissions/c08c3d44-1d14-4a5e-aa32-d9e708a69528

import Mathlib.Analysis.Complex.Basic

set_option autoImplicit false

theorem solution (a b c : ℝ) (ha : 0 < a) (hb : 0 < b) (hc : 0 < c) (hab : a + b + c = a * b * c + 2) : (a + b) * (b + c) * (c + a) + 2 ≥ 2 * (a * b + b * c + a * c) + 4 * a * b * c := by
  (intros; nlinarith [sq_nonneg (a), sq_nonneg (b), sq_nonneg (c), sq_nonneg (a - b), sq_nonneg (a - c), sq_nonneg (b - c), sq_nonneg (a + b), sq_nonneg (a + c), sq_nonneg (b + c), mul_pos ha hb, mul_pos ha hc, mul_pos hb hc])
