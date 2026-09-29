-- Prove2me | solution 1 for lean_workbook_plus_35251
-- status  : ACCEPTED   (prove)
-- author  : @wamlart
-- created : 2026-09-05T18:00:53.06049+00:00
-- url     : https://prove2.me/submissions/290c9ab2-15d4-4bb1-8764-5f77c873dea6

import Mathlib.Tactic
import Mathlib.Analysis.Complex.Basic

set_option autoImplicit false
set_option maxRecDepth 2048
set_option maxHeartbeats 50000



theorem solution (p q r : ℂ) (h : p + q + r = 0) :
  p*q*r + (p+q)*(q+r)*(r+p) = -(p+q+r)^3 := by
  intros
  grind
