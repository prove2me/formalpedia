-- Prove2me | solution 1 for lean_workbook_plus_3957
-- status  : ACCEPTED   (prove)
-- author  : @evgeth
-- created : 2026-09-05T14:15:35.35508+00:00
-- url     : https://prove2.me/submissions/223abb52-a7f8-42ec-ba57-367df8bf9437

import Mathlib.Analysis.Complex.Basic

set_option autoImplicit false

theorem solution (a b : ℝ) (ha : 0 < a) (hb : 0 < b) : a / b ^ 2 + b / a ^ 2 + 16 / (a + b) ≥ 5 * (1 / a + 1 / b) := by
  (intros; field_simp; nlinarith [sq_nonneg (a), sq_nonneg (b), sq_nonneg (a - b), sq_nonneg (a + b), mul_pos ha hb])
