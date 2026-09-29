-- Prove2me | solution 1 for lean_workbook_plus_2544
-- status  : ACCEPTED   (prove)
-- author  : @evgeth
-- created : 2026-09-05T14:26:02.809602+00:00
-- url     : https://prove2.me/submissions/5df68a6f-bf18-4004-bcf4-543759e95d26

import Mathlib.Analysis.Complex.Basic

set_option autoImplicit false

theorem solution (s : ℝ) (h : s ≠ 0) : 6 * s ^ 2 / (2 * s ^ 2 * Real.sqrt 3) = 3 / Real.sqrt 3 := by
  (intros; field_simp; ring)
