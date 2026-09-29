-- Prove2me | solution 1 for lean_workbook_plus_46321
-- status  : ACCEPTED   (prove)
-- author  : @wamlart
-- created : 2026-09-05T17:52:55.2659+00:00
-- url     : https://prove2.me/submissions/ec7ef7c1-5c25-4634-a1b4-7d0a3f39a03c

import Mathlib.Tactic
import Mathlib.Analysis.Complex.Basic

set_option autoImplicit false
set_option maxRecDepth 2048
set_option maxHeartbeats 50000



theorem solution (x y : ℝ) : (3*x-10*y=570 ∧ -2*x+13*y=57) ↔ x=420 ∧ y=69 := by
  intros
  grind
