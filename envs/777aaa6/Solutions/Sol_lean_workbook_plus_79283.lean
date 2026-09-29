-- Prove2me | solution 1 for lean_workbook_plus_79283
-- status  : ACCEPTED   (prove)
-- author  : @evgeth
-- created : 2026-09-05T04:26:17.12893+00:00
-- url     : https://prove2.me/submissions/06a970c8-c2ed-4aa7-8a43-794b98c91519

import Mathlib.Analysis.Complex.Basic

set_option autoImplicit false

theorem solution (x : ℝ) (h : 2014*x + 1337 = 1337*x + 2014) : x = 1 := by
  (intros; linarith)
