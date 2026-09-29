-- Prove2me | solution 1 for lean_workbook_plus_35351
-- status  : ACCEPTED   (prove)
-- author  : @evgeth
-- created : 2026-09-05T11:42:30.165653+00:00
-- url     : https://prove2.me/submissions/f6cf3fa4-d36d-4e61-9569-7707bac4da97

import Mathlib.Analysis.Complex.Basic

set_option autoImplicit false

theorem solution (a b : ℝ) (ha : 0 ≤ a) (hb : 0 ≤ b) : (1 / (1 + a) ^ 2 + 1 / (1 + b) ^ 2) ≥ 2 / (a + b + a * b + 1) := by
  (intros; field_simp; nlinarith [sq_nonneg (a), sq_nonneg (b), sq_nonneg (a - b), sq_nonneg (a + b), mul_nonneg ha hb])
