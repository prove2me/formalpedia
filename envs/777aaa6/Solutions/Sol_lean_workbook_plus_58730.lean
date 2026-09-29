-- Prove2me | solution 1 for lean_workbook_plus_58730
-- status  : ACCEPTED   (prove)
-- author  : @evgeth
-- created : 2026-09-05T07:44:37.155279+00:00
-- url     : https://prove2.me/submissions/6258f39a-1829-4883-a33f-7555fa0bcd7a

import Mathlib.Analysis.Complex.Basic

set_option autoImplicit false

theorem solution (r : ℝ) : (∃ a b, 0 < b ∧ r = a / b) ↔ ∃ a b, 0 < b ∧ r = a / b := by
  norm_num
