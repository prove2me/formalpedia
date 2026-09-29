-- Prove2me | solution 1 for lean_workbook_plus_62612
-- status  : ACCEPTED   (prove)
-- author  : @wamlart
-- created : 2026-09-05T17:23:16.923485+00:00
-- url     : https://prove2.me/submissions/2640b241-6d75-4ee8-b4b7-e11782f4366e

import Mathlib.Tactic
import Mathlib.Analysis.Complex.Basic

set_option autoImplicit false
set_option maxRecDepth 2048
set_option maxHeartbeats 50000



theorem solution (x y z : ℝ) (hx : x + y + z = 0) (hy : x ^ 2 + y ^ 2 + z ^ 2 = 6) : x ^ 3 * y + y ^ 3 * z + z ^ 3 * x = -9 := by
  intros
  grind
