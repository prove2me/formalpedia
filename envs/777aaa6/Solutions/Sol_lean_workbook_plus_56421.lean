-- Prove2me | solution 1 for lean_workbook_plus_56421
-- status  : ACCEPTED   (prove)
-- author  : @evgeth
-- created : 2026-09-05T08:23:01.868173+00:00
-- url     : https://prove2.me/submissions/808797ed-57e0-4a40-ae75-3bdfd4d05f07

import Mathlib.Analysis.Complex.Basic

set_option autoImplicit false

theorem solution (x : ℝ) : x^3 + (1 - x)^3 + (x - 3)^3 + (2 - x)^3 + 18 = 12 * x := by
  (intros; linarith)
