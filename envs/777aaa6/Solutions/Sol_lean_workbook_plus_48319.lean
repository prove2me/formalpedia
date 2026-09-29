-- Prove2me | solution 1 for lean_workbook_plus_48319
-- status  : ACCEPTED   (prove)
-- author  : @wamlart
-- created : 2026-09-05T17:13:08.199762+00:00
-- url     : https://prove2.me/submissions/43f9af07-0ea2-4fd2-a799-55f33bf291a5

import Mathlib.Tactic
import Mathlib.Analysis.Complex.Basic

set_option autoImplicit false
set_option maxRecDepth 2048
set_option maxHeartbeats 50000



theorem solution (x y : ℝ) : 2*x+3*y-10=0 ↔ y = -2/3*x + 10/3 := by
  intros
  grind
