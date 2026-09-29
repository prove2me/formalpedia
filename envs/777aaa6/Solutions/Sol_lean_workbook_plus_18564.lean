-- Prove2me | solution 1 for lean_workbook_plus_18564
-- status  : ACCEPTED   (prove)
-- author  : @wamlart
-- created : 2026-09-05T17:28:36.488187+00:00
-- url     : https://prove2.me/submissions/e32b7793-d6f0-4c28-9cdc-e17c5fb185c8

import Mathlib.Tactic
import Mathlib.Analysis.Complex.Basic

set_option autoImplicit false
set_option maxRecDepth 2048
set_option maxHeartbeats 50000



theorem solution (x y z : ℝ) (h : x + y + z = 4) : 1 ≤ |x - 1| + (|y| + |y - 2|) / 2 := by
  intros
  grind
