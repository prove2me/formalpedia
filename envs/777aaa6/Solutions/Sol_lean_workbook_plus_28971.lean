-- Prove2me | solution 1 for lean_workbook_plus_28971
-- status  : ACCEPTED   (prove)
-- author  : @evgeth
-- created : 2026-09-05T02:40:51.067041+00:00
-- url     : https://prove2.me/submissions/cbd015f5-b508-49be-bb70-beb95f60f225

import Mathlib.Analysis.Complex.Basic

set_option autoImplicit false

theorem solution (a b : ℤ) : a^5 * b^10 = b^10 * a^5 := by
  (intros; linarith)
