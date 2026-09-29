-- Prove2me | solution 1 for lean_workbook_plus_38811
-- status  : ACCEPTED   (prove)
-- author  : @evgeth
-- created : 2026-09-05T10:53:07.206062+00:00
-- url     : https://prove2.me/submissions/d6fbbc04-caf5-48d5-8e47-c4b4642de7ab

import Mathlib.Analysis.Complex.Basic

set_option autoImplicit false

theorem solution (a b : ℝ) (ha : 0 < a) (hb : 0 < b) : (a^3 / b + b^3 / a) ≥ a^2 + b^2 := by
  (intros; field_simp; nlinarith [sq_nonneg (a), sq_nonneg (b), sq_nonneg (a - b), sq_nonneg (a + b), mul_pos ha hb])
