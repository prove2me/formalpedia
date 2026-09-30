-- Prove2me | solution 1 for lean_workbook_plus_68013
-- status  : ACCEPTED   (prove)
-- author  : @ryanshin
-- created : 2026-09-05T03:42:56.973902+00:00
-- url     : https://prove2.me/submissions/04a02ee3-fde6-4a64-8dae-04e2f84bf0ab

import Mathlib.Data.Real.Basic
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Ring

theorem quartic_gap_identity (x y z : ℝ) :
    x ^ 4 + y ^ 4 + z ^ 4 + 3 * (x ^ 2 * y ^ 2 + x ^ 2 * z ^ 2 + y ^ 2 * z ^ 2) -
      2 * (x ^ 3 * (y + z) + y ^ 3 * (x + z) + z ^ 3 * (x + y)) =
      (x ^ 2 + y ^ 2 + z ^ 2 - x * y - y * z - z * x) ^ 2 := by ring

theorem solution (x y z : ℝ) :
    x ^ 4 + y ^ 4 + z ^ 4 + 3 * (x ^ 2 * y ^ 2 + x ^ 2 * z ^ 2 + y ^ 2 * z ^ 2) ≥
      2 * (x ^ 3 * (y + z) + y ^ 3 * (x + z) + z ^ 3 * (x + y)) := by
  have hs := sq_nonneg (x ^ 2 + y ^ 2 + z ^ 2 - x * y - y * z - z * x)
  rw [← quartic_gap_identity] at hs
  linarith

theorem gap_zero_iff (x y z : ℝ) :
    (x ^ 2 + y ^ 2 + z ^ 2 - x * y - y * z - z * x) ^ 2 = 0 ↔ x = y ∧ y = z := by
  constructor
  · intro h
    have hq := sq_eq_zero_iff.mp h
    have hxy : (x - y) ^ 2 = 0 := by
      nlinarith [sq_nonneg (x - y), sq_nonneg (y - z), sq_nonneg (x - z)]
    have hyz : (y - z) ^ 2 = 0 := by
      nlinarith [sq_nonneg (x - y), sq_nonneg (y - z), sq_nonneg (x - z)]
    exact ⟨sub_eq_zero.mp (sq_eq_zero_iff.mp hxy), sub_eq_zero.mp (sq_eq_zero_iff.mp hyz)⟩
  · rintro ⟨rfl, rfl⟩
    ring

#print axioms solution
#print axioms gap_zero_iff
