-- Prove2me | solution 1 for lean_workbook_plus_55059
-- status  : ACCEPTED   (prove)
-- author  : @evgeth
-- created : 2026-09-05T08:02:18.656275+00:00
-- url     : https://prove2.me/submissions/91bf42db-2681-425b-a750-150a5dd30615

import Mathlib.Analysis.Complex.Basic

set_option autoImplicit false

theorem solution (b : ℝ) : (49 * b^2 / 36) - (4 * b^2 / 6) = 25 * b^2 / 36 := by
  (intros; linarith)
