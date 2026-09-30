-- Prove2me | solution 1 for lean_workbook_plus_75839
-- status  : ACCEPTED   (prove)
-- author  : @ryanshin
-- created : 2026-09-05T09:13:33.969749+00:00
-- url     : https://prove2.me/submissions/03f98499-ed52-4e8b-89f0-18c6f30b5463

import Mathlib.Data.Real.Basic
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Ring

namespace QuarticCompositionComparison

theorem quartic_gap (t : ℝ) :
    t ^ 4 - t ^ 3 + 1 - t = (t - 1) ^ 2 * (t ^ 2 + t + 1) := by ring

theorem quartic_dominates (t : ℝ) : t ≤ t ^ 4 - t ^ 3 + 1 := by
  have hq : 0 ≤ t ^ 2 + t + 1 := by nlinarith [sq_nonneg (2 * t + 1)]
  have := mul_nonneg (sq_nonneg (t - 1)) hq
  nlinarith [quartic_gap t]

theorem quartic_fixed_point (t : ℝ) : t ^ 4 - t ^ 3 + 1 = t ↔ t = 1 := by
  constructor
  · intro h
    have hq : 0 < t ^ 2 + t + 1 := by nlinarith [sq_nonneg (2 * t + 1)]
    have hp : (t - 1) ^ 2 * (t ^ 2 + t + 1) = 0 := by
      linarith [quartic_gap t]
    have hs := (mul_eq_zero.mp hp).resolve_right (ne_of_gt hq)
    nlinarith [sq_nonneg (t - 1)]
  · rintro rfl
    ring

theorem all_real_source (x y : ℝ) (h : x + y ^ 3 = y ^ 4 + 1) :
    y + x ^ 3 ≤ x ^ 4 + 1 := by
  have hx := quartic_dominates x
  have hy := quartic_dominates y
  linarith

theorem equality_classification (x y : ℝ) (h : x + y ^ 3 = y ^ 4 + 1) :
    y + x ^ 3 = x ^ 4 + 1 ↔ x = 1 ∧ y = 1 := by
  constructor
  · intro he
    have hx := quartic_dominates x
    have hy := quartic_dominates y
    have hxy : x = y := by linarith
    have hy1 : y = 1 := (quartic_fixed_point y).mp (by linarith)
    exact ⟨hxy.trans hy1, hy1⟩
  · rintro ⟨rfl, rfl⟩
    ring

theorem exact_gap (x y : ℝ) (h : x + y ^ 3 = y ^ 4 + 1) :
    x ^ 4 + 1 - (y + x ^ 3) =
      (x - 1) ^ 2 * (x ^ 2 + x + 1) + (y - 1) ^ 2 * (y ^ 2 + y + 1) := by
  nlinarith [quartic_gap x, quartic_gap y]

end QuarticCompositionComparison

theorem solution (x y : ℝ) (_hx : 0 ≤ x) (_hy : 0 ≤ y)
    (h : x + y ^ 3 = y ^ 4 + 1) : y + x ^ 3 ≤ x ^ 4 + 1 :=
  QuarticCompositionComparison.all_real_source x y h
