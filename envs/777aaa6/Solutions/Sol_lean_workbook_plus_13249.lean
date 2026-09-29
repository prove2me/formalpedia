-- Prove2me | solution 1 for lean_workbook_plus_13249
-- status  : ACCEPTED   (prove)
-- author  : @wamlart
-- created : 2026-09-05T18:19:34.231603+00:00
-- url     : https://prove2.me/submissions/e90dac8a-fe3c-4f90-b42b-e9d62080fed4

import Mathlib.Tactic
import Mathlib.Analysis.Complex.Basic

set_option autoImplicit false
set_option maxRecDepth 2048
set_option maxHeartbeats 50000



theorem solution (x : ℝ) (hx : 2*x - 1/(3*x) = 2) : 3*x - 1/(2*x) = 3 := by
  intros
  grind
