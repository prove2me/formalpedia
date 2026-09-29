-- Prove2me | solution 1 for lean_workbook_plus_63446
-- status  : ACCEPTED   (prove)
-- author  : @evgeth
-- created : 2026-09-05T07:08:18.731367+00:00
-- url     : https://prove2.me/submissions/13b82a58-18b1-45dc-873b-30e82ac77c4f

import Mathlib.Analysis.Complex.Basic

set_option autoImplicit false

theorem solution (a b c : ℝ) : 9*(a - b)^2 * c + 3*(b - c)^2 * (2*c + 2*b - a) = 9*(a - b)^2 * c + 3*(b - c)^2 * (2*c + 2*b - a) := by
  norm_num
