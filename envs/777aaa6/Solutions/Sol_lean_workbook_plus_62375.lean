-- Prove2me | solution 1 for lean_workbook_plus_62375
-- status  : ACCEPTED   (prove)
-- author  : @evgeth
-- created : 2026-09-05T07:18:40.02126+00:00
-- url     : https://prove2.me/submissions/01826e35-a9e1-4aaf-b01c-8cd8ee75124e

import Mathlib.Analysis.Complex.Basic

set_option autoImplicit false

theorem solution (a b c d : ℝ) : c = a + a^2 / b ∧ d = b + b^2 / a ↔ c = a + a^2 / b ∧ d = b + b^2 / a := by
  norm_num
