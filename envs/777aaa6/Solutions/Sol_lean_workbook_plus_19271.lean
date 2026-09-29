-- Prove2me | solution 1 for lean_workbook_plus_19271
-- status  : ACCEPTED   (prove)
-- author  : @evgeth
-- created : 2026-09-05T13:04:07.993983+00:00
-- url     : https://prove2.me/submissions/008b054f-748c-422d-b483-52aed94a2eaa

import Mathlib.Analysis.Complex.Basic

set_option autoImplicit false

theorem solution :
  (3 : ℝ) / 25  = (3 / 36) / (25 / 36) := by
  norm_num
