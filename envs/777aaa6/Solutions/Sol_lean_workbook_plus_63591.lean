-- Prove2me | solution 1 for lean_workbook_plus_63591
-- status  : ACCEPTED   (prove)
-- author  : @evgeth
-- created : 2026-09-05T07:08:05.907298+00:00
-- url     : https://prove2.me/submissions/240edffb-8127-4623-b4d6-271062d58a2f

import Mathlib.Analysis.Complex.Basic

set_option autoImplicit false

theorem solution (a b : ℝ) (ha : 0 < a) (hb : 0 < b) (hab : a + b = 1) : 1 / 2 > a / (b + 2) + b / (a + 2) := by
  (intros; field_simp; nlinarith [sq_nonneg (a), sq_nonneg (b), sq_nonneg (a - b), sq_nonneg (a + b), mul_pos ha hb])
