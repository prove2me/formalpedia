-- Prove2me | solution 1 for lean_workbook_plus_9560
-- status  : ACCEPTED   (prove)
-- author  : @wamlart
-- created : 2026-09-05T16:29:06.103718+00:00
-- url     : https://prove2.me/submissions/7eb9afae-8d06-4cb8-be65-dd27f5055dbc

import Mathlib

set_option autoImplicit false
set_option maxRecDepth 2048
set_option maxHeartbeats 200000



theorem solution (x y z : ℝ) (h₁ : x + y + z = 6) (h₂ : x * y + y * z + z * x = 9) : 0 ≤ x ∧ x ≤ 4 ∧ 0 ≤ y ∧ y ≤ 4 ∧ 0 ≤ z ∧ z ≤ 4 := by
  have hs : (x+y+z)^2 = 36 := by rw [h₁]; norm_num
  have hxr : x * (x+y+z) = 6*x := by rw [h₁]; ring
  have hyr : y * (x+y+z) = 6*y := by rw [h₁]; ring
  have hzr : z * (x+y+z) = 6*z := by rw [h₁]; ring
  have hx : (x - 2)^2 ≤ 4 := by nlinarith [sq_nonneg (y - z)]
  have hy : (y - 2)^2 ≤ 4 := by nlinarith [sq_nonneg (z - x)]
  have hz : (z - 2)^2 ≤ 4 := by nlinarith [sq_nonneg (x - y)]
  constructor
  · nlinarith
  constructor
  · nlinarith
  constructor
  · nlinarith
  constructor
  · nlinarith
  constructor <;> nlinarith
