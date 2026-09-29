-- Prove2me | solution 1 for lean_workbook_plus_25596
-- status  : ACCEPTED   (prove)
-- author  : @evgeth
-- created : 2026-09-05T12:35:40.807305+00:00
-- url     : https://prove2.me/submissions/81771979-39b9-4161-8555-9a4a99fd2776

import Mathlib.Analysis.Complex.Basic

set_option autoImplicit false

theorem solution (a b c : ℝ) : a * b * c / 2 * (3 / (a + b + c) - 2 * c / (1 + c ^ 2)) = a * b * c / 2 * (3 / (a + b + c) - 2 * c / (1 + c ^ 2)) := by
  norm_num
