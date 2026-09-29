-- Prove2me | solution 1 for lean_workbook_plus_33531
-- status  : ACCEPTED   (prove)
-- author  : @evgeth
-- created : 2026-09-05T11:15:02.826638+00:00
-- url     : https://prove2.me/submissions/66db946a-7cb9-4787-b940-25fedb737df6

import Mathlib.Analysis.Complex.Basic

set_option autoImplicit false

theorem solution (x : ℝ) : x^2 - 2*x + 1 = (x-1)^2 := by
  (intros; linarith)
