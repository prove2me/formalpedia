-- Prove2me | solution 1 for lean_workbook_plus_57100
-- status  : ACCEPTED   (prove)
-- author  : @ryanshin
-- created : 2026-09-05T09:12:14.566291+00:00
-- url     : https://prove2.me/submissions/83190c89-954a-4e3b-b9d0-4e87e31d5aaa

import Mathlib.Data.Real.Basic
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.NormNum

namespace CyclicSquareSystem

theorem equal_coordinates (x y z : ℝ)
    (hx : x = y ^ 2 + z ^ 2) (hy : y = z ^ 2 + x ^ 2)
    (hz : z = x ^ 2 + y ^ 2) : x = y ∧ y = z := by
  have hx0 : 0 ≤ x := by nlinarith [sq_nonneg y, sq_nonneg z]
  have hy0 : 0 ≤ y := by nlinarith [sq_nonneg z, sq_nonneg x]
  have hz0 : 0 ≤ z := by nlinarith [sq_nonneg x, sq_nonneg y]
  have hxy : (x - y) * (1 + x + y) = 0 := by nlinarith [hx, hy]
  have hyz : (y - z) * (1 + y + z) = 0 := by nlinarith [hy, hz]
  have hxy' : x - y = 0 := (mul_eq_zero.mp hxy).resolve_right (by linarith)
  have hyz' : y - z = 0 := (mul_eq_zero.mp hyz).resolve_right (by linarith)
  exact ⟨sub_eq_zero.mp hxy', sub_eq_zero.mp hyz'⟩

theorem full_source_classification (x y z : ℝ) :
    (x = y ^ 2 + z ^ 2 ∧ y = z ^ 2 + x ^ 2 ∧ z = x ^ 2 + y ^ 2) ↔
      (x = 0 ∧ y = 0 ∧ z = 0) ∨ (x = 1 / 2 ∧ y = 1 / 2 ∧ z = 1 / 2) := by
  constructor
  · rintro ⟨hx, hy, hz⟩
    obtain ⟨hxy, hyz⟩ := equal_coordinates x y z hx hy hz
    have hroot : x * (2 * x - 1) = 0 := by nlinarith [hx, hxy, hyz]
    rcases mul_eq_zero.mp hroot with h | h
    · left
      exact ⟨h, hxy.symm.trans h, hyz.symm.trans (hxy.symm.trans h)⟩
    · right
      exact ⟨by linarith, by linarith, by linarith⟩
  · rintro (⟨rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl⟩) <;> norm_num

end CyclicSquareSystem

theorem solution (x y z : ℝ)
    (hx : x = y ^ 2 + z ^ 2) (hy : y = z ^ 2 + x ^ 2)
    (hz : z = x ^ 2 + y ^ 2) : x = y ∧ y = z ∧ z = x := by
  obtain ⟨hxy, hyz⟩ := CyclicSquareSystem.equal_coordinates x y z hx hy hz
  exact ⟨hxy, hyz, (hxy.trans hyz).symm⟩
