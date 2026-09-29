-- Prove2me | solution 1 for lean_workbook_plus_33526
-- status  : ACCEPTED   (prove)
-- author  : @evgeth
-- created : 2026-09-05T02:39:05.70795+00:00
-- url     : https://prove2.me/submissions/d75939db-4d80-455a-9258-92a32b7f615e

import Mathlib.Analysis.Complex.Basic

set_option autoImplicit false

theorem solution (x y : ℤ) : x^2 - y^2 = (x + y) * (x - y) := by
  (intros; linarith)
