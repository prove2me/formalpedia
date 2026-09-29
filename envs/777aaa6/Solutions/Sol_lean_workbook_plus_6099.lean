-- Prove2me | solution 1 for lean_workbook_plus_6099
-- status  : ACCEPTED   (prove)
-- author  : @evgeth
-- created : 2026-09-05T02:51:09.636444+00:00
-- url     : https://prove2.me/submissions/55d39e18-380a-4e75-a54e-30c543e6f97c

import Mathlib.Analysis.Complex.Basic

set_option autoImplicit false

theorem solution (x : ℤ) :
  (x + 1)^2 - 1 = x^2 + 2 * x := by
  (intros; linarith)
