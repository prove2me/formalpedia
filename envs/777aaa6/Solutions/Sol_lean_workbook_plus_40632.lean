-- Prove2me | solution 1 for lean_workbook_plus_40632
-- status  : ACCEPTED   (prove)
-- author  : @evgeth
-- created : 2026-09-05T10:40:05.155027+00:00
-- url     : https://prove2.me/submissions/6de455c3-e6cd-459e-af07-f8d52cebe035

import Mathlib.Analysis.Complex.Basic

set_option autoImplicit false

theorem solution (x : ℝ) (h : 4*x + 2*(x-2) = 360) : x = 182/3 := by
  (intros; linarith)
