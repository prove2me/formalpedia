-- Prove2me | solution 1 for lean_workbook_plus_36823
-- status  : ACCEPTED   (prove)
-- author  : @wamlart
-- created : 2026-09-05T19:56:04.816726+00:00
-- url     : https://prove2.me/submissions/d45a10fc-d0a8-4ec4-8383-762c9059116c

import Mathlib.Tactic
import Mathlib.Analysis.Complex.Basic

set_option autoImplicit false
set_option maxRecDepth 2048
set_option maxHeartbeats 100000



theorem solution (x y : ℝ) (h : x * y + Real.sqrt ((1 + x ^ 2) * (1 + y ^ 2)) = 1) :
  x * Real.sqrt (1 + y ^ 2) + y * Real.sqrt (1 + x ^ 2) = 0 := by
  have hs := Real.sq_sqrt (by positivity : 0≤(1+x^2)*(1+y^2))
  have he : Real.sqrt ((1+x^2)*(1+y^2))=1-x*y := by linarith
  rw [he] at hs
  have hxy : x+y=0 := by nlinarith only [hs,sq_nonneg (x+y)]
  have hy : y= -x := by linarith
  rw [hy]
  simp [neg_sq]
