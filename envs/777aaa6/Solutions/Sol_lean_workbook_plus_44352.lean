-- Prove2me | solution 1 for lean_workbook_plus_44352
-- status  : ACCEPTED   (prove)
-- author  : @wamlart
-- created : 2026-09-05T17:40:08.67684+00:00
-- url     : https://prove2.me/submissions/99868761-409d-4a75-a7c0-b3120f3bd73c

import Mathlib.Tactic

set_option autoImplicit false
set_option maxRecDepth 2048
set_option maxHeartbeats 50000



theorem solution (x y : ℝ) (h : (x + Real.sqrt (x^2 + 1)) * (y + Real.sqrt (y^2 + 1)) = 0) : x + y = 0 := by
  grind
