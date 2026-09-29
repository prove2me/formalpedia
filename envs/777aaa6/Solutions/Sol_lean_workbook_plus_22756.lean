-- Prove2me | solution 1 for lean_workbook_plus_22756
-- status  : ACCEPTED   (prove)
-- author  : @evgeth
-- created : 2026-09-05T12:37:20.563928+00:00
-- url     : https://prove2.me/submissions/b8b0ee4c-3288-4ab3-afc7-62af9dfe8c99

import Mathlib.Analysis.Complex.Basic

set_option autoImplicit false

theorem solution (x : ℝ) (hx : 0 < x) : 2 - x < 2 := by
  (intros; simp_all)
