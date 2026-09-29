-- Prove2me | solution 1 for lean_workbook_plus_17894
-- status  : ACCEPTED   (prove)
-- author  : @evgeth
-- created : 2026-09-05T12:55:53.847274+00:00
-- url     : https://prove2.me/submissions/02c9e7de-1be7-4e40-8f20-5d2c95422761

import Mathlib.Analysis.Complex.Basic

set_option autoImplicit false

theorem solution (a b : ℝ) (ha : 0 ≤ a) (hb : 0 ≤ b) : (a / (1 + a) + b / (1 + b)) ≥ (a + b) / (1 + a + b) := by
  (intros; field_simp; nlinarith [sq_nonneg (a), sq_nonneg (b), sq_nonneg (a - b), sq_nonneg (a + b), mul_nonneg ha hb])
