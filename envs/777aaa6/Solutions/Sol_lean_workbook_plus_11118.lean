-- Prove2me | solution 1 for lean_workbook_plus_11118
-- status  : ACCEPTED   (prove)
-- author  : @evgeth
-- created : 2026-09-05T13:47:46.037809+00:00
-- url     : https://prove2.me/submissions/bfd24882-a471-4e0d-b320-5a9a798c021a

import Mathlib.Analysis.Complex.Basic

set_option autoImplicit false

theorem solution (x : ℝ) : (x-1)^2 + x^2 + (x+1)^2 = 3*x^2 + 2 := by
  (intros; linarith)
