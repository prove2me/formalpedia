-- Prove2me | solution 1 for lean_workbook_plus_42310
-- status  : ACCEPTED   (prove)
-- author  : @wamlart
-- created : 2026-09-05T17:45:15.81319+00:00
-- url     : https://prove2.me/submissions/5bada1cb-7747-4dc7-81e8-2ce7e52a4a05

import Mathlib.Tactic
import Mathlib.Analysis.Complex.Basic

set_option autoImplicit false
set_option maxRecDepth 2048
set_option maxHeartbeats 50000



theorem solution (x : ℝ) (hx : x + 2/x = 4) : x^3/2 + 4/x^3 = 20 := by
  intros
  grind
