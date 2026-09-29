-- Prove2me | solution 1 for lean_workbook_plus_38005
-- status  : ACCEPTED   (prove)
-- author  : @wamlart
-- created : 2026-09-05T17:47:11.805426+00:00
-- url     : https://prove2.me/submissions/6a808993-6657-4612-a164-4628a4c556af

import Mathlib.Tactic
import Mathlib.Analysis.Complex.Basic

set_option autoImplicit false
set_option maxRecDepth 2048
set_option maxHeartbeats 50000



theorem solution (t : ℝ) : (t^2 = 1/3) ↔ t = 1/Real.sqrt 3 ∨ t = -1/Real.sqrt 3 := by
  intros
  grind
