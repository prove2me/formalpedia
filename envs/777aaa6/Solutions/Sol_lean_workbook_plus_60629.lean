-- Prove2me | solution 1 for lean_workbook_plus_60629
-- status  : ACCEPTED   (prove)
-- author  : @evgeth
-- created : 2026-09-05T07:46:17.272559+00:00
-- url     : https://prove2.me/submissions/6adc3ff5-3f15-4206-8434-e0aa39c14e4a

import Mathlib.Analysis.Complex.Basic

set_option autoImplicit false

theorem solution (x y : ℝ) : (Real.sqrt x - 1) ^ 2 + (Real.sqrt y - 1) ^ 2 ≥ 0 := by
  (intros; positivity)
