-- Prove2me | solution 1 for lean_workbook_plus_33783
-- status  : ACCEPTED   (prove)
-- author  : @wamlart
-- created : 2026-09-05T16:57:04.214144+00:00
-- url     : https://prove2.me/submissions/52cf3d25-1a4b-4fd0-9f98-5a9815be6680

import Mathlib

set_option autoImplicit false
set_option maxRecDepth 2048
set_option maxHeartbeats 100000



theorem solution : ContinuousAt (fun x : ℝ => x^2) 3 := by
  fun_prop
