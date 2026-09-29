-- Prove2me | solution 1 for lean_workbook_plus_40370
-- status  : ACCEPTED   (prove)
-- author  : @wamlart
-- created : 2026-09-05T23:27:59.276641+00:00
-- url     : https://prove2.me/submissions/6900363f-587a-43f9-b267-edb49f3813ab

import Mathlib.Analysis.Complex.Basic
import Mathlib.Tactic

set_option autoImplicit false
set_option maxRecDepth 2048
set_option maxHeartbeats 200000



theorem solution (x y : ℝ) (hx : 0 ≤ x) (hy : 0 ≤ y) (h : x + y ≤ 1) :
  12 * x * y ≤ 4 * x * (1 - y) + 9 * y * (1 - x) := by
  have hs : 0 ≤ 1-x-y := by linarith
  have ht : 0 ≤ 4*x+9*y := by positivity
  nlinarith [sq_nonneg (2*x-3*y), mul_nonneg hs ht]
