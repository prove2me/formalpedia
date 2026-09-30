-- Prove2me | solution 1 for lean_workbook_plus_56363
-- status  : ACCEPTED   (prove)
-- author  : @ryanshin
-- created : 2026-09-05T07:43:44.57059+00:00
-- url     : https://prove2.me/submissions/4207bfcb-3fc4-469d-bffb-c7edde35486d

import Mathlib.Data.Real.Basic
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.Ring

theorem quartic_identity {R : Type*} [CommRing R] (x y z : R) :
    (x ^ 2 + 2 * y ^ 2 - x * y) * z ^ 2 +
      (x ^ 3 - x * y ^ 2 - 4 * x ^ 2 * y) * z + y * x ^ 3 + y ^ 2 * x ^ 2 =
      y * (x + y) * (x - z) ^ 2 + z * (x + z) * (x - y) ^ 2 := by ring

theorem nonnegative_quartic (x y z : ℝ) (hx : 0 ≤ x) (hy : 0 ≤ y) (hz : 0 ≤ z) :
    0 ≤ (x ^ 2 + 2 * y ^ 2 - x * y) * z ^ 2 +
      (x ^ 3 - x * y ^ 2 - 4 * x ^ 2 * y) * z + y * x ^ 3 + y ^ 2 * x ^ 2 := by
  rw [quartic_identity]
  positivity

theorem positive_equality (x y z : ℝ) (hx : 0 < x) (hy : 0 < y) (hz : 0 < z) :
    (x ^ 2 + 2 * y ^ 2 - x * y) * z ^ 2 +
      (x ^ 3 - x * y ^ 2 - 4 * x ^ 2 * y) * z + y * x ^ 3 + y ^ 2 * x ^ 2 = 0 ↔
      x = y ∧ y = z := by
  rw [quartic_identity]
  constructor
  · intro he
    have hn1 : 0 ≤ y * (x + y) * (x - z) ^ 2 := by positivity
    have hn2 : 0 ≤ z * (x + z) * (x - y) ^ 2 := by positivity
    have he1 : y * (x + y) * (x - z) ^ 2 = 0 := by linarith
    have he2 : z * (x + z) * (x - y) ^ 2 = 0 := by linarith
    have h1 := sq_eq_zero_iff.mp ((mul_eq_zero.mp he1).resolve_left
      (ne_of_gt (mul_pos hy (add_pos hx hy))))
    have h2 := sq_eq_zero_iff.mp ((mul_eq_zero.mp he2).resolve_left
      (ne_of_gt (mul_pos hz (add_pos hx hz))))
    constructor <;> linarith
  · rintro ⟨rfl, rfl⟩
    ring

theorem solution (x y z : ℝ) (hx : 0 < x) (hy : 0 < y) (hz : 0 < z) :
    (x ^ 2 + 2 * y ^ 2 - x * y) * z ^ 2 +
      (x ^ 3 - x * y ^ 2 - 4 * x ^ 2 * y) * z + y * x ^ 3 + y ^ 2 * x ^ 2 ≥ 0 :=
  nonnegative_quartic x y z (le_of_lt hx) (le_of_lt hy) (le_of_lt hz)
