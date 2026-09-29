-- Prove2me | solution 1 for lean_workbook_plus_11286
-- status  : ACCEPTED   (prove)
-- author  : @evgeth
-- created : 2026-09-05T13:39:17.290837+00:00
-- url     : https://prove2.me/submissions/ee24119b-458a-435a-becb-d71279d2fd07

import Mathlib.Analysis.Complex.Basic

set_option autoImplicit false

theorem solution (x : ℝ) (hx: x ≥ 0) : 2 * (x - 3 / 4) ^ 2 + 1 / (x + 1) ≥ 1 / 8 := by
  (intros; field_simp; nlinarith [sq_nonneg (x)])
