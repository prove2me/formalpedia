-- Prove2me | solution 1 for lean_workbook_plus_45039
-- status  : ACCEPTED   (prove)
-- author  : @wamlart
-- created : 2026-09-05T20:48:33.213813+00:00
-- url     : https://prove2.me/submissions/15220d6f-9f41-4633-9c47-cb2ef091d334

import Mathlib.Tactic
import Mathlib.Analysis.Complex.Basic

set_option autoImplicit false
set_option maxRecDepth 2048
set_option maxHeartbeats 100000



theorem solution (x y : ℝ) (hx : 0 ≤ x) (hy : 0 ≤ y) : √x + √y ≥ √(x + y) := by
  have hsx := Real.sq_sqrt hx
  have hsy := Real.sq_sqrt hy
  have hss := Real.sq_sqrt (add_nonneg hx hy)
  have hp := mul_nonneg (Real.sqrt_nonneg x) (Real.sqrt_nonneg y)
  nlinarith [Real.sqrt_nonneg x, Real.sqrt_nonneg y, Real.sqrt_nonneg (x+y)]
