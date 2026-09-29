-- Prove2me | solution 1 for lean_workbook_plus_52702
-- status  : ACCEPTED   (prove)
-- author  : @evgeth
-- created : 2026-09-05T09:04:03.771239+00:00
-- url     : https://prove2.me/submissions/bc896e39-8f9c-43a9-851c-ce741b6b0ddb

import Mathlib.Analysis.Complex.Basic

set_option autoImplicit false

theorem solution (a b c : ℝ) (ha : 0 < a) (hb : 0 < b) (hc : 0 < c) : (a / (a + 5 * b + 3 * c) + b / (b + 5 * c + 3 * a) + c / (c + 5 * a + 3 * b) ≥ 1 / 3) := by
  (intros; field_simp; nlinarith [sq_nonneg (a), sq_nonneg (b), sq_nonneg (c), sq_nonneg (a - b), sq_nonneg (a - c), sq_nonneg (b - c), sq_nonneg (a + b), sq_nonneg (a + c), sq_nonneg (b + c), mul_pos ha hb, mul_pos ha hc, mul_pos hb hc])
