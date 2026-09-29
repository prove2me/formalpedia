-- Prove2me | solution 1 for lean_workbook_plus_67157
-- status  : ACCEPTED   (prove)
-- author  : @wamlart
-- created : 2026-09-05T17:38:09.395169+00:00
-- url     : https://prove2.me/submissions/f9942ead-ba0f-4ab8-a357-692414f64e08

import Mathlib.Tactic
import Mathlib.Analysis.Complex.Basic

set_option autoImplicit false
set_option maxRecDepth 2048
set_option maxHeartbeats 50000



theorem solution (a b c d : ℝ) :
  (a^2+b^2)*(c^2+d^2) ≥ (a*c+b*d)^2 := by
  intros
  nlinarith [sq_nonneg (a*b - c*d), sq_nonneg (a*c - b*d), sq_nonneg (a*d - b*c)]
