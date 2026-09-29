-- Prove2me | solution 1 for lean_workbook_plus_16254
-- status  : ACCEPTED   (prove)
-- author  : @evgeth
-- created : 2026-09-05T13:12:26.690519+00:00
-- url     : https://prove2.me/submissions/b84e3b47-2855-4cf3-835f-f77c917431d7

import Mathlib.Analysis.Complex.Basic

set_option autoImplicit false

theorem solution (a b : ℝ) : (a + b) ^ 3 = a ^ 3 + 3 * a ^ 2 * b + 3 * a * b ^ 2 + b ^ 3 := by
  (intros; linarith)
