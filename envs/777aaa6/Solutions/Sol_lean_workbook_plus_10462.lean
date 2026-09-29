-- Prove2me | solution 1 for lean_workbook_plus_10462
-- status  : ACCEPTED   (prove)
-- author  : @evgeth
-- created : 2026-09-05T13:40:52.684728+00:00
-- url     : https://prove2.me/submissions/5315fff5-9167-4a2c-b5fc-b20edd5e52dd

import Mathlib.Analysis.Complex.Basic

set_option autoImplicit false

theorem solution (x y : ℝ) : y = x^2 / 4 + 3 * x / 2 ↔ y = x^2 / 4 + 3 * x / 2 := by
  norm_num
