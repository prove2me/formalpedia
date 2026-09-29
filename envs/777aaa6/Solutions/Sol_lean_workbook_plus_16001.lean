-- Prove2me | solution 1 for lean_workbook_plus_16001
-- status  : ACCEPTED   (prove)
-- author  : @wamlart
-- created : 2026-09-05T23:09:27.876104+00:00
-- url     : https://prove2.me/submissions/7a50b056-3aa7-4159-9223-406e23c5307c

import Mathlib.Analysis.Complex.Basic
import Mathlib.Tactic

set_option autoImplicit false
set_option maxRecDepth 2048
set_option maxHeartbeats 200000



theorem solution (x y : ℝ) (hx : 0 < x) (hy : 0 < y) (h : x^2 + y^3 ≥ x^3 + y^4) : x^3 + y^3 ≤ 2 := by
  nlinarith [mul_nonneg (sq_nonneg (x-1)) (by positivity : 0 ≤ 2*x+1), mul_nonneg (sq_nonneg (y-1)) (by positivity : 0 ≤ 3*y^2+2*y+1)]
