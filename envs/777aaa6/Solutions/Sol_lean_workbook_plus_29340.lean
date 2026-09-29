-- Prove2me | solution 1 for lean_workbook_plus_29340
-- status  : ACCEPTED   (prove)
-- author  : @wamlart
-- created : 2026-09-05T18:19:02.526936+00:00
-- url     : https://prove2.me/submissions/f89cc292-6ed9-43de-9dd0-4254868054ee

import Mathlib.Tactic
import Mathlib.Analysis.Complex.Basic

set_option autoImplicit false
set_option maxRecDepth 2048
set_option maxHeartbeats 50000



theorem solution (x : ℝ) : 2*x-166=0 ↔ x=83 := by
  intros
  grind
