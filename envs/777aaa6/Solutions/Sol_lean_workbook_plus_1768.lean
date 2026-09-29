-- Prove2me | solution 1 for lean_workbook_plus_1768
-- status  : ACCEPTED   (prove)
-- author  : @wamlart
-- created : 2026-09-05T20:51:55.29808+00:00
-- url     : https://prove2.me/submissions/e9832058-c0d4-4be1-9de1-b9e7af777e54

import Mathlib.Tactic
import Mathlib.Analysis.Complex.Basic

set_option autoImplicit false
set_option maxRecDepth 2048
set_option maxHeartbeats 100000



theorem solution (x y z : ℝ) : x^2 ≥ 2*x-1 ∧ y^4 ≥ 4*y-3 ∧ z^8 ≥ 8*z-7 := by
  constructor
  · nlinarith [sq_nonneg (x-1)]
  · constructor
    · nlinarith [sq_nonneg (y-1), sq_nonneg (y^2-1)]
    · nlinarith [sq_nonneg (z-1), sq_nonneg (z^2-1), sq_nonneg (z^4-1)]
