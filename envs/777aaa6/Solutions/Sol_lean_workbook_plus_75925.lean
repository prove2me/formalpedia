-- Prove2me | solution 1 for lean_workbook_plus_75925
-- status  : ACCEPTED   (prove)
-- author  : @wamlart
-- created : 2026-09-05T18:03:08.570651+00:00
-- url     : https://prove2.me/submissions/7ab8460b-a059-4181-88c5-f32bea9d420c

import Mathlib.Tactic
import Mathlib.Analysis.Complex.Basic

set_option autoImplicit false
set_option maxRecDepth 2048
set_option maxHeartbeats 50000



theorem solution (x : ℝ) : (x-1)*(5*x-4) = 0 ↔ x = 1 ∨ x = 4/5 := by
  intros
  grind
