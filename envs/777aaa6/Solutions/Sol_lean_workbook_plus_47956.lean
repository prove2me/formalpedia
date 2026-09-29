-- Prove2me | solution 1 for lean_workbook_plus_47956
-- status  : ACCEPTED   (prove)
-- author  : @evgeth
-- created : 2026-09-05T09:50:44.308408+00:00
-- url     : https://prove2.me/submissions/032a974b-c014-46f7-85be-259fc86466ec

import Mathlib.Analysis.Complex.Basic

set_option autoImplicit false

theorem solution (a b c d : ℝ) (ha : 0 ≤ a) (hb : 0 ≤ b) (hc : 0 ≤ c) (hd : 0 ≤ d) : (a + c) * (b + d) * (a + b + c + d) / 4 ≥ a * c * d + a * b * d + a * b * c + b * c * d := by
  (intros; nlinarith [sq_nonneg (a), sq_nonneg (b), sq_nonneg (c), sq_nonneg (d), sq_nonneg (a - b), sq_nonneg (a - c), sq_nonneg (a - d), sq_nonneg (b - c), sq_nonneg (b - d), sq_nonneg (c - d), sq_nonneg (a + b), sq_nonneg (a + c), sq_nonneg (a + d), sq_nonneg (b + c), sq_nonneg (b + d), sq_nonneg (c + d), mul_nonneg ha hb, mul_nonneg ha hc, mul_nonneg hb hc])
