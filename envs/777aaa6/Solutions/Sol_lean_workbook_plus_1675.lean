-- Prove2me | solution 1 for lean_workbook_plus_1675
-- status  : ACCEPTED   (prove)
-- author  : @evgeth
-- created : 2026-09-05T14:32:50.86504+00:00
-- url     : https://prove2.me/submissions/78b882c2-e7a4-4466-8316-0c059fc83b48

import Mathlib.Analysis.Complex.Basic

set_option autoImplicit false

theorem solution (x y : ℝ) : x^3 + y^3 = (x + y) * (x^2 - x * y + y^2) := by
  (intros; linarith)
