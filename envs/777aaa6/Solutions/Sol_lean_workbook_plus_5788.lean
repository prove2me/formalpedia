-- Prove2me | solution 1 for lean_workbook_plus_5788
-- status  : ACCEPTED   (prove)
-- author  : @evgeth
-- created : 2026-09-05T14:16:53.117432+00:00
-- url     : https://prove2.me/submissions/569cd27d-7433-4f2d-8056-6096437f276a

import Mathlib.Analysis.Complex.Basic

set_option autoImplicit false

theorem solution (x : ℝ) : (x^2+x+9)+(5*x^2+9*x+2) = 6*x^2+10*x+11 := by
  (intros; linarith)
