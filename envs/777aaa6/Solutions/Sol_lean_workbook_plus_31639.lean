-- Prove2me | solution 1 for lean_workbook_plus_31639
-- status  : ACCEPTED   (prove)
-- author  : @evgeth
-- created : 2026-09-05T11:44:29.411349+00:00
-- url     : https://prove2.me/submissions/fb053123-64a0-4a6d-8b07-7c4bea8c5ecf

import Mathlib.Analysis.Complex.Basic

set_option autoImplicit false

theorem solution (a b c : ℝ) (ha : 0 ≤ a) (hb : 0 ≤ b) (hc : 0 ≤ c) (habc : a * b * c = 1) (h : a^2 + b^2 + c^2 = 1) : a / (b^2 + 1) + b / (c^2 + 1) + c / (a^2 + 1) ≥ 3 / 4 * (a * Real.sqrt a + b * Real.sqrt b + c * Real.sqrt c) := by
  (intros; nlinarith [sq_nonneg (a), sq_nonneg (b), sq_nonneg (c), sq_nonneg (a - b), sq_nonneg (a - c), sq_nonneg (b - c), sq_nonneg (a + b), sq_nonneg (a + c), sq_nonneg (b + c), mul_nonneg ha hb, mul_nonneg ha hc, mul_nonneg hb hc])
