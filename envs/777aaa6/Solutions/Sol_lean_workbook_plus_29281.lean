-- Prove2me | solution 1 for lean_workbook_plus_29281
-- status  : ACCEPTED   (prove)
-- author  : @wamlart
-- created : 2026-09-05T17:40:48.29724+00:00
-- url     : https://prove2.me/submissions/31ad3fa7-a3d5-463b-b494-98c68e358f5d

import Mathlib.Tactic
import Mathlib.Analysis.Complex.Basic

set_option autoImplicit false
set_option maxRecDepth 2048
set_option maxHeartbeats 50000



theorem solution (a b c : ℝ) (hab : a + b + c = 0) : (a^2 + b^2 + c^2)^3 - 54 * a^2 * b^2 * c^2 = 2 * (a - b)^2 * (b - c)^2 * (c - a)^2 := by
  intros
  grind
