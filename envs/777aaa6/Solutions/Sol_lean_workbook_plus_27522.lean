-- Prove2me | solution 1 for lean_workbook_plus_27522
-- status  : ACCEPTED   (prove)
-- author  : @evgeth
-- created : 2026-09-05T02:41:35.094178+00:00
-- url     : https://prove2.me/submissions/080c3002-c644-4e6d-937d-c41eafef4ec4

import Mathlib.Analysis.Complex.Basic

set_option autoImplicit false

theorem solution : ∀ a b : ℤ, a^3 + b^3 - (a + b)^3 = -3 * a * b * (a + b) := by
  (intros; linarith)
