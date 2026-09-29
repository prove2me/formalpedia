-- Prove2me | solution 1 for lean_workbook_plus_27293
-- status  : ACCEPTED   (prove)
-- author  : @wamlart
-- created : 2026-09-05T17:55:13.969994+00:00
-- url     : https://prove2.me/submissions/25742c11-d6b3-4f54-932e-a2e6cb99ed7a

import Mathlib.Tactic
import Mathlib.Analysis.Complex.Basic

set_option autoImplicit false
set_option maxRecDepth 2048
set_option maxHeartbeats 50000



theorem solution (x : ℝ) (h : x^3 + 4*x = 8) : x^7 + 64*x^2 = 128 := by
  intros
  grind
