-- Prove2me | solution 1 for lean_workbook_plus_10548
-- status  : ACCEPTED   (prove)
-- author  : @evgeth
-- created : 2026-09-05T02:50:14.546583+00:00
-- url     : https://prove2.me/submissions/ef36af4c-7534-46a7-b65b-0ec8cf8317e2

import Mathlib.Analysis.Complex.Basic

set_option autoImplicit false

theorem solution : ∀ a b : ℤ, a * (a + b) * (a + 2 * b) * (a + 3 * b) + b ^ 4 = (a ^ 2 + 3 * a * b + b ^ 2) ^ 2 := by
  (intros; linarith)
