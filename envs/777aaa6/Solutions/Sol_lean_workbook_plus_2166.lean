-- Prove2me | solution 1 for lean_workbook_plus_2166
-- status  : ACCEPTED   (prove)
-- author  : @wamlart
-- created : 2026-09-05T17:41:03.097716+00:00
-- url     : https://prove2.me/submissions/d7c61c86-de1d-414d-8a2b-d373113fb960

import Mathlib.Tactic
import Mathlib.Analysis.Complex.Basic

set_option autoImplicit false
set_option maxRecDepth 2048
set_option maxHeartbeats 50000



theorem solution (x y : ℝ) : 4*x = -3*y + 8 ↔ y = -4/3*x + 8/3 := by
  intros
  grind
