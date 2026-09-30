-- Prove2me | solution 1 for lean_workbook_plus_57594
-- status  : ACCEPTED   (prove)
-- author  : @ryanshin
-- created : 2026-09-05T07:27:42.966749+00:00
-- url     : https://prove2.me/submissions/da0df53d-089d-4661-b44f-5314bcd68ae9

import Mathlib.Data.Real.Basic
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Ring
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Positivity

namespace SymmetricReciprocalRefinement

theorem gap (x y z : ℝ) (hx : 0 < x) (hy : 0 < y) (hz : 0 < z) :
    1 / x + 1 / y + 1 / z -
      (4 * (x + y + z) ^ 2 - 3 * (x * y + y * z + z * x)) /
        (x + y + z) / (x * y + y * z + z * x) =
      (x ^ 3 * (y - z) ^ 2 + y ^ 3 * (z - x) ^ 2 + z ^ 3 * (x - y) ^ 2) /
        (x * y * z * (x + y + z) * (x * y + y * z + z * x)) := by
  have hs : x + y + z ≠ 0 := by positivity
  have hq : x * y + y * z + z * x ≠ 0 := by positivity
  field_simp
  ring

theorem bound (x y z : ℝ) (hx : 0 < x) (hy : 0 < y) (hz : 0 < z) :
    (4 * (x + y + z) ^ 2 - 3 * (x * y + y * z + z * x)) /
      (x + y + z) / (x * y + y * z + z * x) ≤ 1 / x + 1 / y + 1 / z := by
  have hp : 0 ≤
      (x ^ 3 * (y - z) ^ 2 + y ^ 3 * (z - x) ^ 2 + z ^ 3 * (x - y) ^ 2) /
        (x * y * z * (x + y + z) * (x * y + y * z + z * x)) := by positivity
  linarith [gap x y z hx hy hz]

theorem equality (x y z : ℝ) (hx : 0 < x) (hy : 0 < y) (hz : 0 < z) :
    1 / x + 1 / y + 1 / z =
      (4 * (x + y + z) ^ 2 - 3 * (x * y + y * z + z * x)) /
        (x + y + z) / (x * y + y * z + z * x) ↔ x = y ∧ y = z := by
  constructor
  · intro he
    have hd : 0 < x * y * z * (x + y + z) * (x * y + y * z + z * x) := by positivity
    have hf :
        (x ^ 3 * (y - z) ^ 2 + y ^ 3 * (z - x) ^ 2 + z ^ 3 * (x - y) ^ 2) /
          (x * y * z * (x + y + z) * (x * y + y * z + z * x)) = 0 := by
      linarith [gap x y z hx hy hz]
    have hm := (div_eq_zero_iff.mp hf).resolve_right (ne_of_gt hd)
    have h₁ : 0 ≤ x ^ 3 * (y - z) ^ 2 := by positivity
    have h₂ : 0 ≤ y ^ 3 * (z - x) ^ 2 := by positivity
    have h₃ : 0 ≤ z ^ 3 * (x - y) ^ 2 := by positivity
    have hzxy : z ^ 3 * (x - y) ^ 2 = 0 := by linarith
    have hxyz : x ^ 3 * (y - z) ^ 2 = 0 := by linarith
    have hxy := (mul_eq_zero.mp hzxy).resolve_left (pow_ne_zero 3 (ne_of_gt hz))
    have hyz := (mul_eq_zero.mp hxyz).resolve_left (pow_ne_zero 3 (ne_of_gt hx))
    exact ⟨eq_of_sub_eq_zero (eq_zero_of_pow_eq_zero hxy),
      eq_of_sub_eq_zero (eq_zero_of_pow_eq_zero hyz)⟩
  · rintro ⟨rfl, rfl⟩
    field_simp
    ring

end SymmetricReciprocalRefinement

theorem solution (x y z : ℝ) (hx : 0 < x) (hy : 0 < y) (hz : 0 < z) :
    1 / x + 1 / y + 1 / z ≥
      (4 * (x + y + z) ^ 2 - 3 * (x * y + y * z + z * x)) /
        (x + y + z) / (x * y + y * z + z * x) :=
  SymmetricReciprocalRefinement.bound x y z hx hy hz
