-- Prove2me | solution 1 for lean_workbook_plus_62087
-- status  : ACCEPTED   (prove)
-- author  : @evgeth
-- created : 2026-09-05T07:19:20.3255+00:00
-- url     : https://prove2.me/submissions/ca0d19c2-71d8-4e85-b434-1686592a0d80

import Mathlib.Analysis.Complex.Basic

set_option autoImplicit false

theorem solution (a b c : ℝ) : a ≥ b ↔ a + c ≥ b + c := by
  norm_num
