-- Prove2me | solution 1 for lean_workbook_plus_23336
-- status  : ACCEPTED   (prove)
-- author  : @wamlart
-- created : 2026-09-05T17:42:15.430381+00:00
-- url     : https://prove2.me/submissions/f106e286-0a61-4fc8-b136-2f4304010caf

import Mathlib.Tactic
import Mathlib.Analysis.Complex.Basic

set_option autoImplicit false
set_option maxRecDepth 2048
set_option maxHeartbeats 50000



theorem solution (x y z : ℝ) (h : x + y + z = 0) :
  (x^2 + y^2 + z^2) / 2 * (x^5 + y^5 + z^5) / 5 = (x^7 + y^7 + z^7) / 7 := by
  intros
  grind
