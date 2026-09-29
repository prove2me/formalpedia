-- Prove2me | solution 1 for lean_workbook_plus_61078
-- status  : ACCEPTED   (prove)
-- author  : @evgeth
-- created : 2026-09-05T07:32:27.022787+00:00
-- url     : https://prove2.me/submissions/698a5a14-f1d7-46d9-adc4-7fd495068812

import Mathlib.Analysis.Complex.Basic

set_option autoImplicit false

theorem solution (a b : ℝ) (ha : 0 ≤ a) (hb : 0 ≤ b) : (1 / 4) * ((2 + a) * (2 + b) / ((1 + a) * (1 + b))) ≥ (4 - a - b) / (4 + a + b) := by
  (intros; field_simp; nlinarith [sq_nonneg (a), sq_nonneg (b), sq_nonneg (a - b), sq_nonneg (a + b), mul_nonneg ha hb])
