-- Prove2me | solution 1 for lean_workbook_plus_20173
-- status  : ACCEPTED   (prove)
-- author  : @evgeth
-- created : 2026-09-05T13:05:11.892425+00:00
-- url     : https://prove2.me/submissions/79adc2ae-6a15-4e3f-8caa-8ba82695ae11

import Mathlib.Analysis.Complex.Basic

set_option autoImplicit false

theorem solution (a b : ℝ) : (1 / 2 * (a - b) / (a + b) * (Real.sqrt a - Real.sqrt b) / (Real.sqrt a + Real.sqrt b)) = (1 / 2 * (a - b) / (a + b) * (Real.sqrt a - Real.sqrt b) / (Real.sqrt a + Real.sqrt b)) := by
  norm_num
