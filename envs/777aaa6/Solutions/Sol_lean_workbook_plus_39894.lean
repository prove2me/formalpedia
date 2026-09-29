-- Prove2me | solution 1 for lean_workbook_plus_39894
-- status  : ACCEPTED   (prove)
-- author  : @evgeth
-- created : 2026-09-05T10:41:05.11825+00:00
-- url     : https://prove2.me/submissions/388797d3-f0aa-4de8-b1ce-89c5c12e1898

import Mathlib.Analysis.Complex.Basic

set_option autoImplicit false

theorem solution (x y : ℝ) (h : x = 0) : (x, y) = (0, y) := by
  (intros; simp_all)
