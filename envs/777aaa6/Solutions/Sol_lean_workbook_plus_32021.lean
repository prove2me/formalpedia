-- Prove2me | solution 1 for lean_workbook_plus_32021
-- status  : ACCEPTED   (prove)
-- author  : @wamlart
-- created : 2026-09-05T20:48:40.681594+00:00
-- url     : https://prove2.me/submissions/e2c64fad-58d4-4651-b360-52480e62ee45

import Mathlib.Tactic
import Mathlib.Analysis.Complex.Basic

set_option autoImplicit false
set_option maxRecDepth 2048
set_option maxHeartbeats 100000



theorem solution (x y z : ℝ) : x^2 + y^2 + z^2 + x^2*y^2*z^2 ≥ 4*x*y*z := by
  by_cases h : 0 ≤ x*y
  · nlinarith [sq_nonneg (x-y), sq_nonneg (z-x*y*z), mul_nonneg h (sq_nonneg (z-1))]
  · have hn : 0 ≤ -(x*y) := by linarith
    nlinarith [sq_nonneg (x+y), sq_nonneg (z+x*y*z), mul_nonneg hn (sq_nonneg (z+1))]
