-- Prove2me | solution 1 for lean_workbook_plus_58385
-- status  : ACCEPTED   (prove)
-- author  : @wamlart
-- created : 2026-09-05T17:48:32.926503+00:00
-- url     : https://prove2.me/submissions/733bc3b2-5795-4bca-811d-4a1ede9f678f

import Mathlib.Tactic
import Mathlib.Analysis.Complex.Basic

set_option autoImplicit false
set_option maxRecDepth 2048
set_option maxHeartbeats 50000



theorem solution (x y z : ℝ) (hx : x > 0) (hy : y > 0) (hz : z > 0) (h : x + y + z = 1) (h' : 1/x + 1/y + 1/z = 1) : x = 1 ∨ y = 1 ∨ z = 1 := by
  intros
  grind
