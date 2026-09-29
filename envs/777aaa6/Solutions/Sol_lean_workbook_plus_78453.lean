-- Prove2me | solution 1 for lean_workbook_plus_78453
-- status  : ACCEPTED   (prove)
-- author  : @evgeth
-- created : 2026-09-05T04:25:32.038784+00:00
-- url     : https://prove2.me/submissions/dadd3b9b-4524-484b-ada7-49a1341568e9

import Mathlib.Analysis.Complex.Basic

set_option autoImplicit false

theorem solution (a b : ℝ) (ha : 0 < a) (hb : 0 < b) (hab : a * b = 1) (h : a^4 + b^4 = 2) : 4 * (a + b) + 3 / (a * b) ≥ 11 := by
  (intros; field_simp; nlinarith [sq_nonneg (a), sq_nonneg (b), sq_nonneg (a - b), sq_nonneg (a + b), mul_pos ha hb])
