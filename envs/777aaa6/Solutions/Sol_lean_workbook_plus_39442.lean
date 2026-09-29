-- Prove2me | solution 1 for lean_workbook_plus_39442
-- status  : ACCEPTED   (prove)
-- author  : @wamlart
-- created : 2026-09-05T17:12:14.853026+00:00
-- url     : https://prove2.me/submissions/9c9f2d6d-0d14-4f50-9707-556e56f9bb88

import Mathlib.Tactic
import Mathlib.Analysis.Complex.Basic

set_option autoImplicit false
set_option maxRecDepth 2048
set_option maxHeartbeats 50000



theorem solution (x y : ℝ) (h : 2*x + 4*y = 1) : x^2 + y^2 ≥ 1/20 := by
  intros
  nlinarith [sq_nonneg (2*x-y), sq_nonneg (x-2*y), sq_nonneg (x+y)]
