-- Prove2me | solution 1 for lean_workbook_plus_55967
-- status  : ACCEPTED   (prove)
-- author  : @evgeth
-- created : 2026-09-05T08:22:12.946615+00:00
-- url     : https://prove2.me/submissions/1d8ade2f-a9aa-4a95-9921-0bf7dcd14e50

import Mathlib.Analysis.Complex.Basic

set_option autoImplicit false

theorem solution (a b c : ℝ) (ha : 0 ≤ a) (hb : 0 ≤ b) (hc : 0 ≤ c) : (1 / (2 + a) + 1 / (2 + b) + 1 / (2 + c)) ≤ (1 + 1 / (2 + a + b + c)) := by
  (intros; field_simp; nlinarith [sq_nonneg (a), sq_nonneg (b), sq_nonneg (c), sq_nonneg (a - b), sq_nonneg (a - c), sq_nonneg (b - c), sq_nonneg (a + b), sq_nonneg (a + c), sq_nonneg (b + c), mul_nonneg ha hb, mul_nonneg ha hc, mul_nonneg hb hc])
