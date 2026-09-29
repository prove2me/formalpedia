-- Prove2me | solution 1 for lean_workbook_plus_50451
-- status  : ACCEPTED   (prove)
-- author  : @wamlart
-- created : 2026-09-05T17:55:22.451671+00:00
-- url     : https://prove2.me/submissions/b5057242-4fa7-44a5-a6f3-b23636cea07d

import Mathlib.Tactic
import Mathlib.Analysis.Complex.Basic

set_option autoImplicit false
set_option maxRecDepth 2048
set_option maxHeartbeats 50000



theorem solution (a b c : ℝ) (h : a + b + c = 0) :
  (a^2 + b^2 + c^2)^2 = 2 * (a^4 + b^4 + c^4) := by
  intros
  grind
