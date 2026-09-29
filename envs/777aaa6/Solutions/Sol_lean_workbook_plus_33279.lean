-- Prove2me | solution 1 for lean_workbook_plus_33279
-- status  : ACCEPTED   (prove)
-- author  : @wamlart
-- created : 2026-09-06T00:10:16.45619+00:00
-- url     : https://prove2.me/submissions/3feb44f3-c759-4c5c-aaa2-7f76a93352b8

import Mathlib.Analysis.Complex.Basic
import Mathlib.Analysis.SpecialFunctions.Log.Basic
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Ring

set_option autoImplicit false
set_option maxRecDepth 2048
set_option maxHeartbeats 100000



theorem solution (x y z : ℝ) (hx : 0 < x) (hy : 0 < y) (hz : 0 < z) (hxy : x ≥ y / 2) (hyz : y ≥ z / 2) (hzx : z ≥ x / 2) :  x * y * z ≥ (2 * x - y) * (2 * y - z) * (2 * z - x) := by
  by_cases hA : 2 * x - y = 0
  · rw [hA, zero_mul, zero_mul]; positivity
  by_cases hB : 2 * y - z = 0
  · rw [hB, mul_zero, zero_mul]; positivity
  by_cases hC : 2 * z - x = 0
  · rw [hC, mul_zero]; positivity
  have hAp : 0 < 2 * x - y := lt_of_le_of_ne (by linarith) (Ne.symm hA)
  have hBp : 0 < 2 * y - z := lt_of_le_of_ne (by linarith) (Ne.symm hB)
  have hCp : 0 < 2 * z - x := lt_of_le_of_ne (by linarith) (Ne.symm hC)
  have hl : Real.log (y / x) + Real.log (z / y) + Real.log (x / z) = 0 := by
    rw [Real.log_div (ne_of_gt hy) (ne_of_gt hx),
      Real.log_div (ne_of_gt hz) (ne_of_gt hy),
      Real.log_div (ne_of_gt hx) (ne_of_gt hz)]
    ring
  have hs : 3 ≤ y / x + z / y + x / z := by
    linarith [Real.log_le_sub_one_of_pos (div_pos hy hx),
      Real.log_le_sub_one_of_pos (div_pos hz hy),
      Real.log_le_sub_one_of_pos (div_pos hx hz)]
  have eA : (2 * x - y) / x = 2 - y / x := by field_simp
  have eB : (2 * y - z) / y = 2 - z / y := by field_simp
  have eC : (2 * z - x) / z = 2 - x / z := by field_simp
  have hla := Real.log_le_sub_one_of_pos (div_pos hAp hx)
  have hlb := Real.log_le_sub_one_of_pos (div_pos hBp hy)
  have hlc := Real.log_le_sub_one_of_pos (div_pos hCp hz)
  rw [eA] at hla
  rw [eB] at hlb
  rw [eC] at hlc
  have hlog : Real.log (((2 * x - y) / x) * ((2 * y - z) / y) * ((2 * z - x) / z)) ≤ 0 := by
    rw [Real.log_mul (by positivity) (ne_of_gt (div_pos hCp hz)),
      Real.log_mul (ne_of_gt (div_pos hAp hx)) (ne_of_gt (div_pos hBp hy)), eA, eB, eC]
    linarith
  have hp := (Real.log_nonpos_iff (by positivity : 0 ≤ ((2 * x - y) / x) * ((2 * y - z) / y) * ((2 * z - x) / z))).1 hlog
  have he : ((2 * x - y) / x) * ((2 * y - z) / y) * ((2 * z - x) / z) =
      ((2 * x - y) * (2 * y - z) * (2 * z - x)) / (x * y * z) := by ring
  rw [he] at hp
  simpa only [one_mul] using (div_le_iff₀ (by positivity : 0 < x * y * z)).mp hp
