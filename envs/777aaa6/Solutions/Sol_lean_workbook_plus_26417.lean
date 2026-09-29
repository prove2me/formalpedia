-- Prove2me | solution 1 for lean_workbook_plus_26417
-- status  : ACCEPTED   (prove)
-- author  : @evgeth
-- created : 2026-09-05T12:25:44.968405+00:00
-- url     : https://prove2.me/submissions/25486a73-16e3-436a-b557-ecb6565acf5c

import Mathlib.Analysis.Complex.Basic

set_option autoImplicit false

theorem solution (x y : ℝ) :
  (y - x)^4 + (x - 2)^4 ≥ 0 := by
  (intros; positivity)
