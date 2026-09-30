-- Prove2me | solution 1 for lean_workbook_plus_58978
-- status  : ACCEPTED   (prove)
-- author  : @ryanshin
-- created : 2026-09-05T07:32:07.023199+00:00
-- url     : https://prove2.me/submissions/1823b968-fcb3-49d2-82bc-a9b8614349cb

import Mathlib.Data.Real.Basic
import Mathlib.Tactic.Ring
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.NormNum

namespace SharpWeightedCubicMinimum

theorem certificate (x y : ℝ) :
    4 * (x + 3 * y) ^ 3 - 25 * (x * y * (x + 8 * y)) =
      (x - 2 * y) ^ 2 * (4 * x + 27 * y) := by ring

theorem homogeneous_bound (x y : ℝ) (hx : 0 ≤ x) (hy : 0 ≤ y) :
    25 * (x * y * (x + 8 * y)) ≤ 4 * (x + 3 * y) ^ 3 := by
  have hp : 0 ≤ (x - 2 * y) ^ 2 * (4 * x + 27 * y) := by positivity
  linarith [certificate x y]

theorem bound (x y : ℝ) (hx : 0 < x) (hy : 0 < y)
    (h : x * y * (x + 8 * y) = 20) : 5 ≤ x + 3 * y := by
  have hc := homogeneous_bound x y hx.le hy.le
  have hp : (5 : ℝ) ^ 3 ≤ (x + 3 * y) ^ 3 := by nlinarith
  exact (show Odd (3 : ℕ) by decide).pow_le_pow.mp hp

theorem equality (x y : ℝ) (hx : 0 < x) (hy : 0 < y)
    (h : x * y * (x + 8 * y) = 20) : x + 3 * y = 5 ↔ x = 2 ∧ y = 1 := by
  constructor
  · intro hs
    have hc := certificate x y
    rw [hs, h] at hc
    have hz : (x - 2 * y) ^ 2 * (4 * x + 27 * y) = 0 := by nlinarith
    have hp : 0 < 4 * x + 27 * y := by positivity
    have hd := (mul_eq_zero.mp hz).resolve_right (ne_of_gt hp)
    have hxy : x - 2 * y = 0 := eq_zero_of_pow_eq_zero hd
    exact ⟨by linarith, by linarith⟩
  · rintro ⟨rfl, rfl⟩
    norm_num

theorem attainment : (2 : ℝ) * 1 * (2 + 8 * 1) = 20 ∧ (2 : ℝ) + 3 * 1 = 5 := by
  norm_num

end SharpWeightedCubicMinimum

theorem solution (x y : ℝ) (hx : 0 < x) (hy : 0 < y)
    (h : x * y * (x + 8 * y) = 20) :
    x + 3 * y ≥ 5 ∧ (x = 2 ∧ y = 1 → x + 3 * y = 5) :=
  ⟨SharpWeightedCubicMinimum.bound x y hx hy h,
    (SharpWeightedCubicMinimum.equality x y hx hy h).mpr⟩
