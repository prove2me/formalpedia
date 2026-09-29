-- Prove2me | solution 1 for lean_workbook_plus_42642
-- status  : ACCEPTED   (prove)
-- author  : @evgeth
-- created : 2026-09-05T10:16:58.161281+00:00
-- url     : https://prove2.me/submissions/85f99e4e-d4c8-4767-861d-d916a77b6784

import Mathlib.Analysis.Complex.Basic

set_option autoImplicit false

theorem solution (a b c : ℝ) (ha : 0 ≤ a) (hb : 0 ≤ b) (hc : 0 ≤ c) : a^4 + b^4 + c^4 ≥ a * b * c * (a + b + c) := by
  (intros; nlinarith [sq_nonneg (a), sq_nonneg (b), sq_nonneg (c), sq_nonneg (a - b), sq_nonneg (a - c), sq_nonneg (b - c), sq_nonneg (a + b), sq_nonneg (a + c), sq_nonneg (b + c), mul_nonneg ha hb, mul_nonneg ha hc, mul_nonneg hb hc])
