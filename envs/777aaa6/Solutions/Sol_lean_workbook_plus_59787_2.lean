-- Prove2me | solution 2 for lean_workbook_plus_59787
-- status  : ACCEPTED   (prove)
-- author  : @evgeth
-- created : 2026-09-05T07:33:35.910471+00:00
-- url     : https://prove2.me/submissions/b193931d-8c44-4ac6-86f3-ee1cba7d8d05

import Mathlib.Analysis.Complex.Basic

set_option autoImplicit false

theorem solution (a b c : ℝ) (ha : 0 ≤ a) (hb : 0 ≤ b) (hc : 0 ≤ c) : (1 / 8 * (2 + a) * (2 + b) * (2 + c) / ((1 + a) * (1 + b) * (1 + c))) ≥ (4 - a - b - c) / (4 + a + b + c) := by
  (intros; field_simp; nlinarith [sq_nonneg (a), sq_nonneg (b), sq_nonneg (c), sq_nonneg (a - b), sq_nonneg (a - c), sq_nonneg (b - c), sq_nonneg (a + b), sq_nonneg (a + c), sq_nonneg (b + c), mul_nonneg ha hb, mul_nonneg ha hc, mul_nonneg hb hc])
