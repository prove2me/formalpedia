-- Prove2me | solution 1 for lean_workbook_plus_28381
-- status  : ACCEPTED   (prove)
-- author  : @evgeth
-- created : 2026-09-05T02:41:31.703987+00:00
-- url     : https://prove2.me/submissions/de7c5267-307c-4803-a556-925341513a31

import Mathlib.Analysis.Complex.Basic

set_option autoImplicit false

theorem solution (a b : ℤ) : a^2 - b^2 = (a + b) * (a - b) := by
  (intros; linarith)
