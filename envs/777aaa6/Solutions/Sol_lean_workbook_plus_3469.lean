-- Prove2me | solution 1 for lean_workbook_plus_3469
-- status  : ACCEPTED   (prove)
-- author  : @wamlart
-- created : 2026-09-05T23:42:31.912399+00:00
-- url     : https://prove2.me/submissions/7eb98ac7-5275-46e4-b0ed-321fb2165ccb

import Mathlib.Analysis.Complex.Basic
import Mathlib.Tactic

set_option autoImplicit false
set_option maxRecDepth 2048
set_option maxHeartbeats 200000



theorem solution (a b : ℝ) (ha : 0 ≤ a) (hb : 0 ≤ b) : (3 * a + b) * (3 * b + a) ≥ 2 * (a + b) * (Real.sqrt a + Real.sqrt b) ^ 2 := by
  have haux (u v : ℝ) : (3*u^2+v^2)*(3*v^2+u^2) ≥ 2*(u^2+v^2)*(u+v)^2 := by
    nlinarith only [sq_nonneg ((u-v)^2)]
  simpa only [Real.sq_sqrt ha, Real.sq_sqrt hb] using haux (Real.sqrt a) (Real.sqrt b)
