-- Prove2me | solution 1 for lean_workbook_plus_47563
-- status  : ACCEPTED   (prove)
-- author  : @wamlart
-- created : 2026-09-05T17:11:36.578871+00:00
-- url     : https://prove2.me/submissions/8576bd1e-040e-4e66-81a9-d2ef13bffcfc

import Mathlib.Tactic
import Mathlib.Analysis.Complex.Basic

set_option autoImplicit false
set_option maxRecDepth 2048
set_option maxHeartbeats 50000



theorem solution (x : ℝ) (hx : (x-2)*(x-3)*(x+1) = 0) : x = 3 ∨ x = 2 ∨ x = -1 := by
  intros
  grind
