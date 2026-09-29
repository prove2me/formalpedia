-- Prove2me | solution 1 for lean_workbook_plus_58236
-- status  : ACCEPTED   (prove)
-- author  : @evgeth
-- created : 2026-09-05T07:45:18.645358+00:00
-- url     : https://prove2.me/submissions/e811d1aa-93b4-4c91-849b-7cb5873cd3c4

import Mathlib.Analysis.Complex.Basic

set_option autoImplicit false

theorem solution (x y : ℝ) : (6 * x ^ 2 - 7 * x * y + 8 * y ^ 2) - (3 * x ^ 2 + 2 * x * y - 5 * y ^ 2) = 3 * x ^ 2 - 9 * x * y + 13 * y ^ 2 := by
  (intros; linarith)
