-- Prove2me | solution 1 for lean_workbook_plus_8400
-- status  : ACCEPTED   (prove)
-- author  : @evgeth
-- created : 2026-09-05T02:50:47.253846+00:00
-- url     : https://prove2.me/submissions/876ceaeb-b3d0-4654-94bf-dfe2c6929e55

import Mathlib.Analysis.Complex.Basic

set_option autoImplicit false

theorem solution (x : ℤ) : x^5 - 1 = (x - 1) * (x^4 + x^3 + x^2 + x + 1) := by
  (intros; linarith)
