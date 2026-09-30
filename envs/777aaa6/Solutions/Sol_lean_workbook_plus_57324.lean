-- Prove2me | solution 1 for lean_workbook_plus_57324
-- status  : ACCEPTED   (prove)
-- author  : @ryanshin
-- created : 2026-09-05T06:02:03.675554+00:00
-- url     : https://prove2.me/submissions/50758bed-13e1-4e08-bea0-a7e046b417b1

import Mathlib.Data.Real.Basic
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Ring

theorem fourth_difference_power_nonneg (t : ℝ) : 0 ≤ t ^ 4 := by
  nlinarith only [sq_nonneg (t ^ 2)]

theorem fourth_difference_identity (x y z : ℝ) :
    x ^ 4 * y + x ^ 4 * z + y ^ 4 * x + y ^ 4 * z + z ^ 4 * x + z ^ 4 * y +
      6 * x * y * z * (x * y + x * z + y * z) -
        8 * x * y * z * (x ^ 2 + y ^ 2 + z ^ 2) =
      z * (x - y) ^ 4 + x * (y - z) ^ 4 + y * (z - x) ^ 4 := by
  ring

theorem fourth_difference_equality (x y z : ℝ)
    (hx : 0 < x) (hy : 0 < y) (hz : 0 < z) :
    z * (x - y) ^ 4 + x * (y - z) ^ 4 + y * (z - x) ^ 4 = 0 ↔
      x = y ∧ y = z := by
  constructor
  · intro h
    have h1 := mul_nonneg hz.le (fourth_difference_power_nonneg (x - y))
    have h2 := mul_nonneg hx.le (fourth_difference_power_nonneg (y - z))
    have h3 := mul_nonneg hy.le (fourth_difference_power_nonneg (z - x))
    have hxy : z * (x - y) ^ 4 = 0 := by linarith
    have hyz : x * (y - z) ^ 4 = 0 := by linarith
    have hxy' := eq_zero_of_pow_eq_zero ((mul_eq_zero.mp hxy).resolve_left hz.ne')
    have hyz' := eq_zero_of_pow_eq_zero ((mul_eq_zero.mp hyz).resolve_left hx.ne')
    constructor <;> linarith
  · rintro ⟨rfl, rfl⟩
    ring

theorem solution (x y z : ℝ) (hx : x ≥ 0) (hy : y ≥ 0) (hz : z ≥ 0) :
    x ^ 4 * y + x ^ 4 * z + y ^ 4 * x + y ^ 4 * z + z ^ 4 * x + z ^ 4 * y +
      6 * x * y * z * (x * y + x * z + y * z) ≥
        8 * x * y * z * (x ^ 2 + y ^ 2 + z ^ 2) := by
  have h1 := mul_nonneg hz (fourth_difference_power_nonneg (x - y))
  have h2 := mul_nonneg hx (fourth_difference_power_nonneg (y - z))
  have h3 := mul_nonneg hy (fourth_difference_power_nonneg (z - x))
  linarith [fourth_difference_identity x y z]

#print axioms solution
#print axioms fourth_difference_equality
