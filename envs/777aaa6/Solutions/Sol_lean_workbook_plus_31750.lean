-- Prove2me | solution 1 for lean_workbook_plus_31750
-- status  : ACCEPTED   (prove)
-- author  : @wamlart
-- created : 2026-09-05T18:20:19.334571+00:00
-- url     : https://prove2.me/submissions/298e7386-90e1-4d66-887d-04c3a43d623a

import Mathlib.Tactic
import Mathlib.Analysis.Complex.Basic

set_option autoImplicit false
set_option maxRecDepth 2048
set_option maxHeartbeats 50000



theorem solution (a : ℝ) (f : ℝ → ℝ) (hf: (a-1)*f (-1) = 0) : f (-1) = 0 ∨ a = 1 := by
  intros
  grind
