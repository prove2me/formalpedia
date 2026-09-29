-- Prove2me | solution 1 for lean_workbook_plus_25569
-- status  : ACCEPTED   (prove)
-- author  : @evgeth
-- created : 2026-09-05T12:35:49.610771+00:00
-- url     : https://prove2.me/submissions/867d454a-c0f6-45e3-a75e-bca4a9b084b0

import Mathlib.Analysis.Complex.Basic

set_option autoImplicit false

theorem solution (a b c d : ℝ) (ha : 0 ≤ a) (hb : 0 ≤ b) (hc : 0 ≤ c) (hd : 0 ≤ d) : (a + b + c + d) ^ 3 ≥ 16 * (a * b * c + b * c * d + c * d * a + d * a * b) := by
  (intros; nlinarith [sq_nonneg (a), sq_nonneg (b), sq_nonneg (c), sq_nonneg (d), sq_nonneg (a - b), sq_nonneg (a - c), sq_nonneg (a - d), sq_nonneg (b - c), sq_nonneg (b - d), sq_nonneg (c - d), sq_nonneg (a + b), sq_nonneg (a + c), sq_nonneg (a + d), sq_nonneg (b + c), sq_nonneg (b + d), sq_nonneg (c + d), mul_nonneg ha hb, mul_nonneg ha hc, mul_nonneg hb hc])
