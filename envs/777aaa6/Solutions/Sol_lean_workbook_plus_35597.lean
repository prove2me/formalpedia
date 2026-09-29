-- Prove2me | solution 1 for lean_workbook_plus_35597
-- status  : ACCEPTED   (prove)
-- author  : @wamlart
-- created : 2026-09-06T00:27:50.278454+00:00
-- url     : https://prove2.me/submissions/1be3bc71-0d3b-45c6-98b6-93fa3c7f1a81

import Mathlib.Analysis.Complex.Basic
import Mathlib.Tactic

set_option autoImplicit false
set_option maxRecDepth 2048
set_option maxHeartbeats 80000



theorem solution : ∀ y z : ℝ, (y * z ≠ 0 → 1 / (2 * y ^ 2) + 2 / z ^ 2 ≥ 2 / (y * z)) := by
  intro y z hyz
  have hy : y ≠ 0 := (mul_ne_zero_iff.mp hyz).1
  have hz : z ≠ 0 := (mul_ne_zero_iff.mp hyz).2
  have hid : 1/(2*y^2)+2/z^2-2/(y*z) = (1/y-2/z)^2/2 := by
    field_simp
    <;> ring
  have hn : 0 ≤ (1/y-2/z)^2/2 := by positivity
  rw [← hid] at hn
  linarith only [hn]
