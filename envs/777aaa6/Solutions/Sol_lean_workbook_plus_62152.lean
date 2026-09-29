-- Prove2me | solution 1 for lean_workbook_plus_62152
-- status  : ACCEPTED   (prove)
-- author  : @wamlart
-- created : 2026-09-05T17:48:02.60227+00:00
-- url     : https://prove2.me/submissions/8bea8490-5398-4378-a4eb-30e17f46c5aa

import Mathlib.Tactic
import Mathlib.Analysis.Complex.Basic

set_option autoImplicit false
set_option maxRecDepth 2048
set_option maxHeartbeats 50000



theorem solution (x y : ℝ) : |x-y|+|x+y| ≥ |x|+|y| := by
  intros
  grind
