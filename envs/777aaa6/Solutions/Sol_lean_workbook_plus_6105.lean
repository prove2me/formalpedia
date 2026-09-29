-- Prove2me | solution 1 for lean_workbook_plus_6105
-- status  : ACCEPTED   (prove)
-- author  : @evgeth
-- created : 2026-09-05T14:06:47.877615+00:00
-- url     : https://prove2.me/submissions/db77f40c-bb1a-448c-8892-2c5ba8bd197e

import Mathlib.Analysis.Complex.Basic

set_option autoImplicit false

theorem solution (a b : ℝ) : (a + b) ^ 2 = a ^ 2 + 2 * a * b + b ^ 2 := by
  (intros; linarith)
