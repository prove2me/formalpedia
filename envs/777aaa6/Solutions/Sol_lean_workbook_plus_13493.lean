-- Prove2me | solution 1 for lean_workbook_plus_13493
-- status  : ACCEPTED   (prove)
-- author  : @evgeth
-- created : 2026-09-05T02:49:38.387226+00:00
-- url     : https://prove2.me/submissions/cd5b2549-7aec-4591-a871-c18f84370078

import Mathlib.Analysis.Complex.Basic

set_option autoImplicit false

theorem solution (x y : ℤ) : 3 * x ^ 2 + 7 * x * y - 6 * y ^ 2 = (3 * x - 2 * y) * (x + 3 * y) := by
  (intros; linarith)
