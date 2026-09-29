-- Prove2me | solution 1 for lean_workbook_plus_72226
-- status  : ACCEPTED   (prove)
-- author  : @evgeth
-- created : 2026-09-05T05:20:34.37202+00:00
-- url     : https://prove2.me/submissions/cb318954-0a31-46fa-9989-01ffae1683b0

import Mathlib.Analysis.Complex.Basic

set_option autoImplicit false

theorem solution (a c e f : ℝ) : (Real.sqrt 5 * (Real.sqrt 5 - 1) / 2) * (4 * e^2 / 5 + f^2 / (Real.sqrt 5 - 1)^2) + a^2 * Real.sqrt 5 / 2 + 2 * e^2 / Real.sqrt 5 - 4 * c = (Real.sqrt 5 * (Real.sqrt 5 - 1) / 2) * (4 * e^2 / 5 + f^2 / (Real.sqrt 5 - 1)^2) + a^2 * Real.sqrt 5 / 2 + 2 * e^2 / Real.sqrt 5 - 4 * c := by
  norm_num
