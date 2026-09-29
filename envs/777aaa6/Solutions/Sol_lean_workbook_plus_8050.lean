-- Prove2me | solution 1 for lean_workbook_plus_8050
-- status  : ACCEPTED   (prove)
-- author  : @wamlart
-- created : 2026-09-05T18:16:02.055977+00:00
-- url     : https://prove2.me/submissions/d1dd9bb3-06dd-439f-8044-a17be81dbd98

import Mathlib.Tactic
import Mathlib.Analysis.Complex.Basic

set_option autoImplicit false
set_option maxRecDepth 2048
set_option maxHeartbeats 50000



theorem solution (x : ℝ) : (3^2 + 4^2 - 2*3*4*x = 5^2 + 6^2 - 2*5*6*(-x)) ↔ x = -3/7 := by
  intros
  grind
