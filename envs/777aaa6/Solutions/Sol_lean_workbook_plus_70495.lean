-- Prove2me | solution 1 for lean_workbook_plus_70495
-- status  : ACCEPTED   (prove)
-- author  : @evgeth
-- created : 2026-09-05T05:51:57.364033+00:00
-- url     : https://prove2.me/submissions/453c4e37-40a9-45df-9af7-3339c867d5f8

import Mathlib.Analysis.Complex.Basic

set_option autoImplicit false

theorem solution (a b : ℝ) (ha : 1 ≥ a ∧ a ≥ b ∧ b ≥ 0) : 2 * a ^ 2 * (1 - b) ≥ (a - b) * (a ^ 2 - b ^ 2 + 2 * b) := by
  (intros; nlinarith [sq_nonneg (a), sq_nonneg (b), sq_nonneg (a - b), sq_nonneg (a + b)])
