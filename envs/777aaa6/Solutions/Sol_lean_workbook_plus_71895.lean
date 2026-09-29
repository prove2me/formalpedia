-- Prove2me | solution 1 for lean_workbook_plus_71895
-- status  : ACCEPTED   (prove)
-- author  : @evgeth
-- created : 2026-09-05T05:19:48.747259+00:00
-- url     : https://prove2.me/submissions/0c6aac56-45ee-43fa-af35-34da40d3496c

import Mathlib.Analysis.Complex.Basic

set_option autoImplicit false

theorem solution (a b c : ℝ) (ha : 0 < a) (hb : 0 < b) (hc : 0 < c) : (a + b + c) / (1 + a + b + c) ≥ a / (1 + 3 * a) + b / (1 + 3 * b) + c / (1 + 3 * c) := by
  (intros; field_simp; nlinarith [sq_nonneg (a), sq_nonneg (b), sq_nonneg (c), sq_nonneg (a - b), sq_nonneg (a - c), sq_nonneg (b - c), sq_nonneg (a + b), sq_nonneg (a + c), sq_nonneg (b + c), mul_pos ha hb, mul_pos ha hc, mul_pos hb hc])
