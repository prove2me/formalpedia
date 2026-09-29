-- Prove2me | solution 1 for lean_workbook_plus_13938
-- status  : ACCEPTED   (prove)
-- author  : @evgeth
-- created : 2026-09-05T13:30:05.541679+00:00
-- url     : https://prove2.me/submissions/096c4c8f-95aa-4f13-afed-69bfc813684a

import Mathlib.Analysis.Complex.Basic

set_option autoImplicit false

theorem solution (a b c : ℝ) : (1 / Real.sqrt 97) * (16 * (a / 4 + b / 4 + c / 4) + 65 * (1 / 9 * a + 1 / 9 * b + 1 / 9 * c)) = (1 / Real.sqrt 97) * (16 * (a / 4 + b / 4 + c / 4) + 65 * (1 / 9 * a + 1 / 9 * b + 1 / 9 * c)) := by
  norm_num
