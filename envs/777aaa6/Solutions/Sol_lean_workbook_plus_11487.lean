-- Prove2me | solution 1 for lean_workbook_plus_11487
-- status  : ACCEPTED   (prove)
-- author  : @evgeth
-- created : 2026-09-05T13:48:22.420898+00:00
-- url     : https://prove2.me/submissions/ae9b3e25-15b6-40e5-bbbd-bc354462a18f

import Mathlib.Analysis.Complex.Basic

set_option autoImplicit false

theorem solution (a b c d : ℝ) (ha : a ≥ 0) (hb : b ≥ 0) (hc : c ≥ 0) (hd : d ≥ 0) : (a + b + c + d) ^ 3 ≥ 16 * (a * b * c + b * c * d + a * c * d + a * b * d) := by
  (intros; nlinarith [sq_nonneg (a), sq_nonneg (b), sq_nonneg (c), sq_nonneg (d), sq_nonneg (a - b), sq_nonneg (a - c), sq_nonneg (a - d), sq_nonneg (b - c), sq_nonneg (b - d), sq_nonneg (c - d), sq_nonneg (a + b), sq_nonneg (a + c), sq_nonneg (a + d), sq_nonneg (b + c), sq_nonneg (b + d), sq_nonneg (c + d)])
