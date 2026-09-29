-- Prove2me | solution 1 for lean_workbook_plus_56994
-- status  : ACCEPTED   (prove)
-- author  : @evgeth
-- created : 2026-09-05T08:24:05.577971+00:00
-- url     : https://prove2.me/submissions/9a4f989d-7884-4b53-952c-238bc5f23ccb

import Mathlib.Analysis.Complex.Basic

set_option autoImplicit false

theorem solution : ∃ x y z a b c : ℝ, x = y ∧ y = z ∧ z = -1 ∧ a = b ∧ b = c ∧ c = 0 := by
  norm_num
