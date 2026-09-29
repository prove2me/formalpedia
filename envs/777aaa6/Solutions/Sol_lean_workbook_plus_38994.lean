-- Prove2me | solution 1 for lean_workbook_plus_38994
-- status  : ACCEPTED   (prove)
-- author  : @wamlart
-- created : 2026-09-05T21:20:23.176532+00:00
-- url     : https://prove2.me/submissions/6bdac765-bdc9-4186-b8ef-482ddd247aea

import Mathlib.Tactic
import Mathlib.Analysis.Complex.Basic

set_option autoImplicit false
set_option maxRecDepth 2048
set_option maxHeartbeats 100000



theorem solution (x y : ℝ) (hx : 0 < x ∧ x < 1) (hy : 0 < y ∧ y < 1) (h : y * (1 - x) > 1 / 4) : y > x := by
  by_contra hn
  have hp := mul_nonneg (show 0 ≤ x-y by linarith) (show 0 ≤ 1-x by linarith [hx.2])
  nlinarith [sq_nonneg (x-1/2)]
