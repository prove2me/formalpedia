-- Prove2me | solution 1 for lean_workbook_plus_46047
-- status  : ACCEPTED   (prove)
-- author  : @wamlart
-- created : 2026-09-05T17:42:39.055781+00:00
-- url     : https://prove2.me/submissions/55cba0c8-2a41-45e0-bbbb-0ebda92c1424

import Mathlib.Tactic
import Mathlib.Analysis.Complex.Basic

set_option autoImplicit false
set_option maxRecDepth 2048
set_option maxHeartbeats 50000



theorem solution (h : ℝ)
  (hh : 0 < h)
  (hh2 : (h / Real.sqrt 3 + 4 + h * Real.sqrt 3) = 16) :
  h = 3 * Real.sqrt 3 := by
  intros
  grind
