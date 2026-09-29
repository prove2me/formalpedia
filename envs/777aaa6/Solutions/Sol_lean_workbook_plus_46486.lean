-- Prove2me | solution 1 for lean_workbook_plus_46486
-- status  : ACCEPTED   (prove)
-- author  : @evgeth
-- created : 2026-09-05T10:15:05.852079+00:00
-- url     : https://prove2.me/submissions/499d8b3d-4142-466f-98e8-a84d3d35c01b

import Mathlib.Analysis.Complex.Basic

set_option autoImplicit false

theorem solution (x : ℝ) : -1 / 2 < x ∧ x < 45 / 8 ↔ -1 / 2 < x ∧ x < 45 / 8 := by
  norm_num
