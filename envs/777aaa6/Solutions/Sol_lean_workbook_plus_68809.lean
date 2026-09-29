-- Prove2me | solution 1 for lean_workbook_plus_68809
-- status  : ACCEPTED   (prove)
-- author  : @evgeth
-- created : 2026-09-05T06:31:24.621611+00:00
-- url     : https://prove2.me/submissions/f5e497f0-39da-47a5-81be-3f71d322f3bc

import Mathlib.Analysis.Complex.Basic

set_option autoImplicit false

theorem solution (a b c : ℝ) (ha : 0 < a) (hb : 0 < b) (hc : 0 < c) : (a - b) / (b + c) + (b - c) / (c + a) ≥ (a - c) / (a + b) := by
  (intros; field_simp; nlinarith [sq_nonneg (a), sq_nonneg (b), sq_nonneg (c), sq_nonneg (a - b), sq_nonneg (a - c), sq_nonneg (b - c), sq_nonneg (a + b), sq_nonneg (a + c), sq_nonneg (b + c), mul_pos ha hb, mul_pos ha hc, mul_pos hb hc])
