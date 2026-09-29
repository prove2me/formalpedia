-- Prove2me | solution 1 for lean_workbook_plus_9135
-- status  : ACCEPTED   (prove)
-- author  : @evgeth
-- created : 2026-09-05T13:49:10.930616+00:00
-- url     : https://prove2.me/submissions/dfda226a-3301-4dd6-9b44-3ef77f781e85

import Mathlib.Analysis.Complex.Basic

set_option autoImplicit false

theorem solution (f s : ℝ) : (5 * f / 6 = 3 * s / 4) → f = 9 * s / 10 := by
  (intros; linarith)
