-- Prove2me | solution 1 for lean_workbook_plus_11115
-- status  : ACCEPTED   (prove)
-- author  : @evgeth
-- created : 2026-09-05T02:50:30.195457+00:00
-- url     : https://prove2.me/submissions/8bd7d06e-f810-4de4-b420-550480877930

import Mathlib.Analysis.Complex.Basic

set_option autoImplicit false

theorem solution (x n m : ℤ) (h₁ : (x + n) ^ 3 = x ^ 3 + m) : 3 * n * x ^ 2 + 3 * n ^ 2 * x + n ^ 3 - m = 0 := by
  (intros; linarith)
