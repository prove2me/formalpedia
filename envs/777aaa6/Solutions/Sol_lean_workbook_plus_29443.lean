-- Prove2me | solution 1 for lean_workbook_plus_29443
-- status  : ACCEPTED   (prove)
-- author  : @evgeth
-- created : 2026-09-05T12:04:42.952482+00:00
-- url     : https://prove2.me/submissions/79c06d1a-d417-4336-a00d-760c322cbe54

import Mathlib.Analysis.Complex.Basic

set_option autoImplicit false

theorem solution (a b : ℝ) (ha : 0 < a) (hb : 0 < b) (hab : a * b = 1) (h : a^9 + b^9 = 2) :
 a^2 / b + b^2 / a ≥ 2 := by
  (intros; field_simp; nlinarith [sq_nonneg (a), sq_nonneg (b), sq_nonneg (a - b), sq_nonneg (a + b), mul_pos ha hb])
