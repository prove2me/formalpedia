-- Prove2me | solution 1 for lean_workbook_plus_59897
-- status  : ACCEPTED   (prove)
-- author  : @wamlart
-- created : 2026-09-05T16:10:21.055498+00:00
-- url     : https://prove2.me/submissions/4dc9ce21-9fef-48d6-8a2e-7216d55e2f72

import Mathlib

set_option autoImplicit false
set_option maxRecDepth 2048
set_option maxHeartbeats 30000


theorem solution (a b : ℝ) (ha : a = 1 / Real.sqrt 2) (hb : b = 1 / Real.sqrt 2) : 1 / a + 1 / b + 1 / (a * b) ^ 2 = 4 + 2 * Real.sqrt 2 := by
  rw [ha, hb]
  have hs : Real.sqrt 2 ^ 2 = 2 := Real.sq_sqrt (by norm_num)
  have hp : Real.sqrt 2 * Real.sqrt 2 = 2 := by nlinarith
  simp only [one_div, inv_inv, ← mul_inv, hp]
  norm_num
  show Real.sqrt 2 + Real.sqrt 2 + 4 = 4 + 2 * Real.sqrt 2
  ring
