-- Prove2me | solution 1 for lean_workbook_plus_1295
-- status  : ACCEPTED   (prove)
-- author  : @evgeth
-- created : 2026-09-05T14:17:25.459709+00:00
-- url     : https://prove2.me/submissions/4b0ba0a8-3638-4d5a-8cdb-77d7db17f0ff

import Mathlib.Analysis.Complex.Basic

set_option autoImplicit false

theorem solution (a b c : ℝ) (ha : 0 ≤ a) (hb : 0 ≤ b) (hc : 0 ≤ c) (habc : a * b * c = 1) (h : a^2 + b^2 + c^2 + 2 * a * b * c = 1) :
  (a + 2 * b)^2 + (b + 2 * c)^2 + (c + 2 * a)^2 ≤ 7 ∧ (a + b)^2 + (b + c) * (c + a) ≤ 5 / 2 := by
  (intros; nlinarith [sq_nonneg (a), sq_nonneg (b), sq_nonneg (c), sq_nonneg (a - b), sq_nonneg (a - c), sq_nonneg (b - c), sq_nonneg (a + b), sq_nonneg (a + c), sq_nonneg (b + c), mul_nonneg ha hb, mul_nonneg ha hc, mul_nonneg hb hc])
