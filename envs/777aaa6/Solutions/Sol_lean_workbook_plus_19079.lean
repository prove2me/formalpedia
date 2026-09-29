-- Prove2me | solution 1 for lean_workbook_plus_19079
-- status  : ACCEPTED   (prove)
-- author  : @evgeth
-- created : 2026-09-05T13:03:50.440223+00:00
-- url     : https://prove2.me/submissions/fceb4e39-6819-4191-bf81-74e49b37f958

import Mathlib.Analysis.Complex.Basic

set_option autoImplicit false

theorem solution (x : ℝ) :
  x^4 - 2 * x^3 + 2 * x - 1 = (x - 1)^3 * (x + 1) := by
  (intros; linarith)
