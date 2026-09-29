-- Prove2me | solution 1 for lean_workbook_plus_5946
-- status  : ACCEPTED   (prove)
-- author  : @evgeth
-- created : 2026-09-05T14:08:15.518051+00:00
-- url     : https://prove2.me/submissions/f01620cb-b8b5-4b9c-8792-cc342e1839ce

import Mathlib.Analysis.Complex.Basic

set_option autoImplicit false

theorem solution (x : ℝ) : (x^2 - 6*x + 13/2)^2 >= 0 := by
  (intros; positivity)
