-- Prove2me | solution 1 for lean_workbook_plus_71924
-- status  : ACCEPTED   (prove)
-- author  : @evgeth
-- created : 2026-09-05T05:19:53.597682+00:00
-- url     : https://prove2.me/submissions/2adcaa4d-0696-4af9-8a3d-cb0cbb37a287

import Mathlib.Analysis.Complex.Basic

set_option autoImplicit false

theorem solution : (1 / 9) * (9 * (5:ℝ)^(1/3) - 9 * (4:ℝ)^(1/3)) = (5:ℝ)^(1/3) - (4:ℝ)^(1/3) := by
  norm_num
