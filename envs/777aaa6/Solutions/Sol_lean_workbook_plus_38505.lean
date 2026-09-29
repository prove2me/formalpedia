-- Prove2me | solution 1 for lean_workbook_plus_38505
-- status  : ACCEPTED   (prove)
-- author  : @evgeth
-- created : 2026-09-05T10:51:59.798585+00:00
-- url     : https://prove2.me/submissions/7f94a5d0-3bd7-4929-8d0f-a084922782b4

import Mathlib.Analysis.Complex.Basic

set_option autoImplicit false

theorem solution (x : ℝ) (hx : x > 0) : 9 * x ^ 6 + (x ^ 4 + x ^ 2 + 1) ^ 2 - 18 * x ^ 5 = (x - 1) ^ 2 * (x ^ 6 + 2 * x ^ 5 + 14 * x ^ 4 + 8 * x ^ 3 + 5 * x ^ 2 + 2 * x + 1) := by
  (intros; linarith)
