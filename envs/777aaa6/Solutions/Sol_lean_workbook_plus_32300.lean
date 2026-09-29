-- Prove2me | solution 1 for lean_workbook_plus_32300
-- status  : ACCEPTED   (prove)
-- author  : @evgeth
-- created : 2026-09-05T11:43:18.380401+00:00
-- url     : https://prove2.me/submissions/6c60a381-6007-45d9-b45e-474be5404ca1

import Mathlib.Analysis.Complex.Basic

set_option autoImplicit false

theorem solution (a b : ℝ) (ha : 0 ≤ a) (hb : 0 ≤ b) : (1 / 4 * ((2 + a) * (2 + b) / ((1 + a) * (1 + b)))) ≥ (4 - a - b) / (4 + a + b) := by
  (intros; field_simp; nlinarith [sq_nonneg (a), sq_nonneg (b), sq_nonneg (a - b), sq_nonneg (a + b), mul_nonneg ha hb])
