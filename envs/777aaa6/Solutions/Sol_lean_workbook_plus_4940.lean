-- Prove2me | solution 1 for lean_workbook_plus_4940
-- status  : ACCEPTED   (prove)
-- author  : @wamlart
-- created : 2026-09-05T17:50:00.48748+00:00
-- url     : https://prove2.me/submissions/ea59c36b-8bbd-4ba1-88da-9d9ace3c3888

import Mathlib

set_option autoImplicit false
set_option maxRecDepth 2048
set_option maxHeartbeats 30000



theorem solution (x y z : ℝ) (h₁ : x + y + z = 3) (h₂ : x*y + y*z + z*x = 3) : x = 1 ∧ y = 1 ∧ z = 1 := by
  have hx : (x-1)^2 = 0 := by nlinarith [sq_nonneg (x-y),sq_nonneg (y-z),sq_nonneg (z-x),sq_nonneg (y-1),sq_nonneg (z-1)]
  have hy : (y-1)^2 = 0 := by nlinarith [sq_nonneg (x-y),sq_nonneg (y-z),sq_nonneg (z-x),sq_nonneg (x-1),sq_nonneg (z-1)]
  constructor
  · nlinarith [sq_nonneg (x-1)]
  constructor <;> nlinarith [sq_nonneg (y-1)]
