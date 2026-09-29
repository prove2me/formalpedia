-- Prove2me | solution 1 for lean_workbook_plus_3918
-- status  : ACCEPTED   (prove)
-- author  : @wamlart
-- created : 2026-09-05T17:11:45.372005+00:00
-- url     : https://prove2.me/submissions/5af69d23-5e68-4a90-a61f-dca93b980bf1

import Mathlib.Tactic
import Mathlib.Analysis.Complex.Basic

set_option autoImplicit false
set_option maxRecDepth 2048
set_option maxHeartbeats 50000



theorem solution : (Real.sqrt 3) * (3 * Real.sqrt 3) = 9 := by
  intros
  grind
