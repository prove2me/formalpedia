-- Prove2me | solution 1 for lean_workbook_plus_53196
-- status  : ACCEPTED   (prove)
-- author  : @evgeth
-- created : 2026-09-05T08:46:46.142774+00:00
-- url     : https://prove2.me/submissions/bcaeb499-ff48-402d-8457-6bfd3059bc6e

import Mathlib.Analysis.Complex.Basic

set_option autoImplicit false

theorem solution (a b c : ℝ) (ha : 0 ≤ a) (hb : 0 ≤ b) (hc : 0 ≤ c) (habc : a * b * c = 1) (h : a^2 + b^2 + c^2 + 2 * a * b * c = 5) : a * b * c + a + b + c ≤ 4 := by
  (intros; nlinarith [sq_nonneg (a), sq_nonneg (b), sq_nonneg (c), sq_nonneg (a - b), sq_nonneg (a - c), sq_nonneg (b - c), sq_nonneg (a + b), sq_nonneg (a + c), sq_nonneg (b + c), mul_nonneg ha hb, mul_nonneg ha hc, mul_nonneg hb hc])
