-- Prove2me | solution 1 for lean_workbook_plus_54072
-- status  : ACCEPTED   (prove)
-- author  : @evgeth
-- created : 2026-09-05T08:45:20.809945+00:00
-- url     : https://prove2.me/submissions/a4b09c4d-97fa-4305-89cf-291bd44d3c2f

import Mathlib.Analysis.Complex.Basic

set_option autoImplicit false

theorem solution (a b : ℝ) (ha : 0 ≤ a) (hb : 0 ≤ b) : (a + b + 1) ^ 4 ≥ (a ^ 2 - a + 1) * (b ^ 2 - b + 1) := by
  (intros; nlinarith [sq_nonneg (a), sq_nonneg (b), sq_nonneg (a - b), sq_nonneg (a + b), mul_nonneg ha hb])
