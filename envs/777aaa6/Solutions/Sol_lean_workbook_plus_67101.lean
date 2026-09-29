-- Prove2me | solution 1 for lean_workbook_plus_67101
-- status  : ACCEPTED   (prove)
-- author  : @wamlart
-- created : 2026-09-05T21:26:45.682805+00:00
-- url     : https://prove2.me/submissions/71bdf396-6ad5-4cca-8bfe-b936fce8e33d

import Mathlib.Tactic
import Mathlib.Analysis.Complex.Basic

set_option autoImplicit false
set_option maxRecDepth 2048
set_option maxHeartbeats 100000



theorem solution (x y z : ℝ) (h : x*y*z = -1) :
  3 * (x^2 - x + 1) * (y^2 - y + 1) * (z^2 - z + 1) ≥ 1 := by
  have hx : 3/4 ≤ x^2-x+1 := by nlinarith [sq_nonneg (x-1/2)]
  have hy : 3/4 ≤ y^2-y+1 := by nlinarith [sq_nonneg (y-1/2)]
  have hz : 3/4 ≤ z^2-z+1 := by nlinarith [sq_nonneg (z-1/2)]
  have hp := mul_nonneg (show 0 ≤ x^2-x+1-3/4 by linarith) (show 0 ≤ y^2-y+1-3/4 by linarith)
  have hxy : 9/16 ≤ (x^2-x+1)*(y^2-y+1) := by nlinarith
  have hq := mul_nonneg (show 0 ≤ (x^2-x+1)*(y^2-y+1)-9/16 by linarith) (show 0 ≤ z^2-z+1-3/4 by linarith)
  nlinarith
