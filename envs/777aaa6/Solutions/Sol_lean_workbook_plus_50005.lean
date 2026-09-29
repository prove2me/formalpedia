-- Prove2me | solution 1 for lean_workbook_plus_50005
-- status  : ACCEPTED   (prove)
-- author  : @evgeth
-- created : 2026-09-05T09:21:16.787742+00:00
-- url     : https://prove2.me/submissions/f464242d-657b-4662-b76e-feb8ce46d159

import Mathlib.Analysis.Complex.Basic

set_option autoImplicit false

theorem solution (a b c d : ℝ) (ha : a ≠ 1) (hb : b ≠ 1) (hc : c ≠ 1) (hd : d ≠ 1) (hab : a ≠ b) (hbc : b ≠ c) (hcd : c ≠ d) (habc : a ≠ c) (habd : a ≠ d) (hbd : b ≠ d) (ha : 0 < a) (hb : 0 < b) (hc : 0 < c) (hd : 0 < d) (hab : a + b + c + d = 1) : (1 - a) * (1 - b) * (1 - c) * (1 - d) ≥ a * b * c * d := by
  (intros; nlinarith [sq_nonneg (a), sq_nonneg (b), sq_nonneg (c), sq_nonneg (d), sq_nonneg (a - b), sq_nonneg (a - c), sq_nonneg (a - d), sq_nonneg (b - c), sq_nonneg (b - d), sq_nonneg (c - d), sq_nonneg (a + b), sq_nonneg (a + c), sq_nonneg (a + d), sq_nonneg (b + c), sq_nonneg (b + d), sq_nonneg (c + d), mul_pos ha hb, mul_pos ha hc, mul_pos hb hc])
