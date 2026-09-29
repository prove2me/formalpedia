-- Prove2me | solution 1 for lean_workbook_plus_942
-- status  : ACCEPTED   (prove)
-- author  : @wamlart
-- created : 2026-09-05T17:27:29.993189+00:00
-- url     : https://prove2.me/submissions/58cd3f2a-0b1e-4ff6-ac32-d6776aa6399e

import Mathlib.Tactic
import Mathlib.Analysis.Complex.Basic

set_option autoImplicit false
set_option maxRecDepth 2048
set_option maxHeartbeats 50000



theorem solution (x y : ℝ) (h : x^2 + y^2 ≤ 2 * x + y) : 2 * x + y ≤ 5 := by
  intros
  nlinarith [sq_nonneg (2*x-y), sq_nonneg (x-2*y), sq_nonneg (x+y)]
