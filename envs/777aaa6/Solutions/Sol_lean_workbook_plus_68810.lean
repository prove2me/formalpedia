-- Prove2me | solution 1 for lean_workbook_plus_68810
-- status  : ACCEPTED   (prove)
-- author  : @evgeth
-- created : 2026-09-05T06:31:21.688906+00:00
-- url     : https://prove2.me/submissions/be8ee37c-7f64-4e51-a223-8277ec1573c6

import Mathlib.Analysis.Complex.Basic

set_option autoImplicit false

theorem solution (a b c : ℝ) (ha : 0 ≤ a) (hb : 0 ≤ b) (hc : 0 ≤ c) : 3 * (a ^ 3 + b ^ 3 + c ^ 3) ≥ (a + b + c) * (a ^ 2 + b ^ 2 + c ^ 2) := by
  (intros; nlinarith [sq_nonneg (a), sq_nonneg (b), sq_nonneg (c), sq_nonneg (a - b), sq_nonneg (a - c), sq_nonneg (b - c), sq_nonneg (a + b), sq_nonneg (a + c), sq_nonneg (b + c), mul_nonneg ha hb, mul_nonneg ha hc, mul_nonneg hb hc])
